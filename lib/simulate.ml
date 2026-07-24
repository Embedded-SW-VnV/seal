(* Trajectory simulation for Dynsys.poly_t, used to empirically sanity-check
   invariants returned by Analysis (round/shape/affine/prop_driven_sos_lyap/
   liouville_method/piecewise_lin): forward-simulate the actual dynamics from
   the init region and see whether the claimed invariant ever gets violated.

   Points are represented as plain [float array] of length [df] (state only);
   inputs, when present, as [float array] of length [di]. Polynomials are
   evaluated by concatenating state then input floats, matching the
   convention used everywhere in this codebase that input variables are
   x_df .. x_(df+di-1) (see e.g. Liouville.compute's [xi (dynsys.df + idx)]). *)

module Make (Dynsys : Dynsys.S) = struct
  module Poly = Dynsys.Poly
  module Coeff = Dynsys.Coeff

  let eval (p : Poly.t) (state : float array) (input : float array) : float =
    let vars = Array.to_list state @ Array.to_list input in
    Coeff.to_float (Poly.eval p (List.map Coeff.of_float vars))

  (* Standard normal via Box-Muller, off a caller-supplied RNG state so
     simulations stay reproducible from a single seed. *)
  let gaussian rng =
    let u1 = max epsilon_float (Random.State.float rng 1.) in
    let u2 = Random.State.float rng 1. in
    sqrt (-2. *. log u1) *. cos (2. *. Float.pi *. u2)

  (* A basic_semialgebraic_t is a conjunction of [p_i(x) >= 0] (the
     convention used for init/input/guards throughout this codebase, unlike
     the [p_i(x) <= 0] convention used for analysis *results*; see
     Polynomial_examples.ml's header comment and MatrixPolynomialCast's
     [ball_to_semialg]). *)
  let satisfies ?(eps = 0.) (bsa : Dynsys.basic_semialgebraic_t) state input =
    List.for_all (fun p -> eval p state input >= -.eps) bsa

  (* Try to recognize [bsa] as exactly a ball [radius^2 - sum_i (x_i -
     c_i)^2 >= 0] over the [dim] variables starting at [start_idx] (the
     shape produced by [MatrixPolynomialCast.ball_to_semialg], used by every
     example in this repo for init/input regions). Returns (center, radius)
     on success, so trajectories can be seeded/sampled exactly rather than
     by rejection sampling (critical when the region is tiny, e.g. ex1's
     init ball has radius 1e-4). *)
  let detect_ball (bsa : Dynsys.basic_semialgebraic_t) ~start_idx ~dim :
      (float array * float) option =
    match bsa with
    | [ p ] -> (
        let const = ref 0. in
        let linear = Array.make dim 0. in
        let quad = Array.make dim 0. in
        let seen_quad = Array.make dim false in
        let ok = ref true in
        List.iter
          (fun (m, coeff) ->
            if !ok then begin
              let degs = Array.of_list (Osdp.Monomial.to_list m) in
              let c = Coeff.to_float coeff in
              let nz =
                List.filter (fun i -> Array.get degs i <> 0)
                  (List.init (Array.length degs) (fun i -> i))
              in
              match nz with
              | [] -> const := !const +. c
              | [ i ] when i >= start_idx && i < start_idx + dim ->
                let j = i - start_idx in
                (match Array.get degs i with
                 | 1 -> linear.(j) <- linear.(j) +. c
                 | 2 ->
                   quad.(j) <- quad.(j) +. c;
                   seen_quad.(j) <- true
                 | _ -> ok := false)
              | _ -> ok := false
            end)
          (Poly.to_list p);
        if not !ok || not (Array.for_all (fun b -> b) seen_quad) then None
        else if not (Array.for_all (fun q -> abs_float (q +. 1.) < 1e-9) quad)
        then None (* not a sphere: quadratic coeff must be exactly -1 *)
        else
          let center = Array.map (fun l -> l /. 2.) linear in
          let radius_sq =
            !const
            +. Array.fold_left (fun acc ci -> acc +. (ci *. ci)) 0. center
          in
          if radius_sq < 0. then None
          else Some (center, sqrt radius_sq))
    | _ -> None

  (* Uniform point in the ball of given center/radius, by normalizing a
     Gaussian vector and rescaling its norm by u^(1/dim) (standard technique
     for uniform sampling in an n-ball). *)
  let sample_in_ball rng (center : float array) (radius : float) : float array =
    let dim = Array.length center in
    if radius <= 0. then Array.copy center
    else
      let g = Array.init dim (fun _ -> gaussian rng) in
      let norm = sqrt (Array.fold_left (fun a x -> a +. (x *. x)) 0. g) in
      let norm = if norm = 0. then 1. else norm in
      let u = Random.State.float rng 1. in
      let scale = radius *. (u ** (1. /. float_of_int dim)) /. norm in
      Array.mapi (fun i ci -> ci +. (g.(i) *. scale)) center

  (* Rejection sampling fallback for regions that aren't a plain ball:
     sample uniformly in the box [center_i - half_width, center_i +
     half_width] and reject until all conjuncts hold. [half_width] should be
     generous enough that the region is actually contained in the box, or
     this will spin/fail. *)
  let sample_by_rejection rng (bsa : Dynsys.basic_semialgebraic_t) ~start_idx
      ~dim ~half_width ~max_tries =
    let rec go n =
      if n <= 0 then None
      else
        let cand = Array.init dim (fun _ -> (Random.State.float rng 2. -. 1.) *. half_width) in
        let padded = Array.append (Array.make start_idx 0.) cand in
        if satisfies bsa padded [||] then Some cand else go (n - 1)
    in
    go max_tries

  let sample_region rng (bsa : Dynsys.basic_semialgebraic_t) ~start_idx ~dim
      ~fallback_half_width : float array =
    match detect_ball bsa ~start_idx ~dim with
    | Some (center, radius) -> sample_in_ball rng center radius
    | None -> (
        match
          sample_by_rejection rng bsa ~start_idx ~dim ~half_width:fallback_half_width
            ~max_tries:100_000
        with
        | Some s -> s
        | None ->
          failwith
            "Simulate.sample_region: rejection sampling failed to find a \
             point in the region (region not recognized as a ball and too \
             small/oddly-shaped relative to fallback_half_width)")

  type input_mode =
    | Zero
    | Uniform
    | Adversarial of (float array -> float)
      (* scores a *candidate next state*; the input maximizing the score is
         picked at each step (a cheap worst-case-seeking heuristic, not an
         exact adversary) *)

  (* Candidate inputs tried by [Adversarial]: the ball's center-relative
     cardinal extremes plus a handful of random boundary directions, so it
     at least explores the corners/boundary of the input region rather than
     its interior. *)
  let adversarial_candidates rng (center : float array) (radius : float) ~n_random :
      float array list =
    let dim = Array.length center in
    let cardinals =
      List.concat
        (List.init dim (fun i ->
             [ Array.mapi (fun j c -> if i = j then c +. radius else c) center;
               Array.mapi (fun j c -> if i = j then c -. radius else c) center ]))
    in
    let randoms =
      List.init n_random (fun _ ->
          let g = Array.init dim (fun _ -> gaussian rng) in
          let norm = sqrt (Array.fold_left (fun a x -> a +. (x *. x)) 0. g) in
          let norm = if norm = 0. then 1. else norm in
          Array.mapi (fun i ci -> ci +. (g.(i) *. radius /. norm)) center)
    in
    cardinals @ randoms

  let pick_mode (sys : Dynsys.poly_t) (state : float array) (input : float array) =
    match List.find_opt (fun (g, _) -> satisfies g state input) sys.Dynsys.map with
    | Some m -> m
    | None -> (
        match sys.Dynsys.map with
        | [ m ] -> m
        | _ ->
          failwith
            "Simulate.pick_mode: no guard matched the current state (and the \
             system isn't single-mode) -- sampled point likely escaped the \
             region the piecewise guards were meant to partition")

  let step rng (sys : Dynsys.poly_t) ~input_mode ~input_fallback_half_width
      (state : float array) : float array * float array =
    let input =
      if sys.Dynsys.di = 0 then [||]
      else
        match sys.Dynsys.input with
        | None -> Array.make sys.Dynsys.di 0.
        | Some bsa -> (
            match input_mode with
            | Zero -> Array.make sys.Dynsys.di 0.
            | Uniform ->
              sample_region rng bsa ~start_idx:sys.Dynsys.df ~dim:sys.Dynsys.di
                ~fallback_half_width:input_fallback_half_width
            | Adversarial score -> (
                match detect_ball bsa ~start_idx:sys.Dynsys.df ~dim:sys.Dynsys.di with
                | None ->
                  sample_region rng bsa ~start_idx:sys.Dynsys.df ~dim:sys.Dynsys.di
                    ~fallback_half_width:input_fallback_half_width
                | Some (center, radius) ->
                  let candidates = adversarial_candidates rng center radius ~n_random:8 in
                  let _, update = pick_mode sys state (Array.make sys.Dynsys.di 0.) in
                  let best =
                    List.fold_left
                      (fun best cand ->
                        let next = Array.map (fun p -> eval p state cand) update in
                        let s = score next in
                        match best with
                        | Some (_, best_s) when best_s >= s -> best
                        | _ -> Some (cand, s))
                      None candidates
                  in
                  (match best with Some (cand, _) -> cand | None -> center)))
    in
    let _, update = pick_mode sys state input in
    (Array.map (fun p -> eval p state input) update, input)

  let sample_init rng (sys : Dynsys.poly_t) ~init_fallback_half_width : float array =
    sample_region rng sys.Dynsys.init ~start_idx:0 ~dim:sys.Dynsys.df
      ~fallback_half_width:init_fallback_half_width

  (* Forward-simulate [ntraj] trajectories of [nsteps] steps each, starting
     from fresh samples of [sys.init] every time, and return every visited
     state point (including the initial ones) across all trajectories. *)
  let run ?(seed = 0) ?(input_mode = Uniform) ?(init_fallback_half_width = 10.)
      ?(input_fallback_half_width = 10.) (sys : Dynsys.poly_t) ~ntraj ~nsteps :
      float array list =
    let rng = Random.State.make [| seed |] in
    let points = ref [] in
    for _ = 1 to ntraj do
      let state = ref (sample_init rng sys ~init_fallback_half_width) in
      points := !state :: !points;
      for _ = 1 to nsteps do
        let next, _ = step rng sys ~input_mode ~input_fallback_half_width !state in
        state := next;
        points := !state :: !points
      done
    done;
    !points

  (* Per-variable (min, max) over a set of visited points; a cheap way to
     report the empirical reachable box, comparable directly against a
     prop_driven_sos_lyap per-axis bound. *)
  let bounding_box (points : float array list) ~df : (float * float) array =
    let mins = Array.make df infinity and maxs = Array.make df neg_infinity in
    List.iter
      (fun p ->
        Array.iteri
          (fun i x ->
            if x < mins.(i) then mins.(i) <- x;
            if x > maxs.(i) then maxs.(i) <- x)
          p)
      points;
    Array.init df (fun i -> (mins.(i), maxs.(i)))
end
