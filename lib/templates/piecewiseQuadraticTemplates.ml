(* k-inductive piecewise-quadratic invariant search for piecewise-*linear*
   systems (Dynsys.lin_t), guards restricted to affine half-spaces.

   Ported from the PiecewiseLyapunov Matlab toolbox at
   /Users/ploc/Repositories/svn/numericaltools/PiecewiseLyapunov/code/matlab/PiecewisePolicy/PiecewiseLyapunov-version-journal/
   (analyzer/@PWA/invariant.m, compute_paths.m; system/Laws.m, Guard.m,
   MotzkinTest.m; analyzer/@PWA/isinit.m) -- the same toolbox
   piecewise_linear_examples.ml's MignoneInvariance1/Example1Pierre were
   ported from.

   The algorithm: find quadratic certificates M_path(x) = 2.q_path^T.x +
   x^T.P_path.x, one per path of up to k cell indices (not one per cell --
   the certificate can depend on the last k modes visited, a sliding
   window), such that:
   - boundedness (per path, on the path's last cell's guard): M_path(x) +
     b - ||x||^2 >= a, via an S-procedure multiplier against the cell's
     quadratized guard;
   - init (only for length-1 paths whose cell intersects the init region):
     M_path(x) <= a there;
   - transition (per path i ending in cell plast, per cell j reachable
     from plast): M_path(x) >= M_next(F(x)), where next is path extended
     by j (sliding the window if already at length k) -- the actual
     k-induction step;
   - minimizing a + b.

   Two deliberate deviations from the literal Matlab source (both agreed
   with the user before porting):
   - invariant.m's transition constraint computes idnext (the slid-window
     path) but then uses M{j} (the plain per-cell certificate) instead of
     M{idnext} in the actual LMI -- idnext is dead code. Comparing against
     invariant_bkp.m (the pre-k-induction version, where M{j} is correct
     because paths *are* cells there) makes this look like an incomplete
     refactor: porting it literally would make k functionally pointless.
     This port uses M_next (the idnext-indexed certificate), the
     mathematically-intended k-inductive version.
   - The guard-quadratization multipliers (U/W/X in invariant.m) are
     general matrices with every entry constrained >=0 (full cross-terms
     between guard rows), not diagonal-only S-procedure multipliers like
     elsewhere in this codebase -- Matlab's plain (non-'symmetric')
     sdpvar(n,n) is not itself symmetric. Ported via [nonneg_matrix]
     below as a grid of individually-declared 1x1 Osdp.Lmi scalar
     variables assembled with Lmi.block, but forced *symmetric* (the same
     variable reused at (i,j) and (j,i)): Osdp.Lmi.solve requires every
     constraint to evaluate to a symmetric matrix (confirmed empirically:
     an asymmetric W raises Not_symmetric), and this turns out to be
     mathematically necessary regardless of that restriction -- see the
     comment on [nonneg_matrix] itself. Still fully expressive (genuine
     cross-terms between different guard rows), just symmetric ones.

   Scope: di = 0 only -- the source has no input/disturbance concept at
   all (Contrainte/Law model pure x' = Ax+b, with bounded-input systems
   like the paper's "running example" instead folding the input into an
   extra frozen state coordinate, see piecewise_linear_examples.ml).

   TODO (known gap, deliberately deferred): the "frozen state" reading
   models the input as an unknown-but-time-invariant *parameter*, not a
   genuinely time-varying, per-step-resampled disturbance -- a strictly
   weaker (easier to satisfy) model than what Dynsys.di/input represent
   everywhere else in this codebase (see the note on Example1Pierre in
   piecewise_linear_examples.ml, which deliberately does NOT use the
   frozen encoding for that reason). Supporting real di > 0 here would
   mean universally quantifying over the input at every transition (an
   extra S-procedure multiplier against the input's guard, the same
   pattern Liouville.compute/PropSOSTemplates.template already use) --
   not done yet; matching the paper's own running-example result requires
   the frozen reading regardless, since that's what its own algorithm
   computes under.

   [Dynsys.lin_update_t] itself has no way to represent a nonzero offset
   b (it's a plain df x df linear map), so [invariant]'s [?offsets]
   parameter carries it separately, one length-d vector per cell,
   defaulting to all-zero. *)

module Make (Dynsys : Dynsys.S) = struct
  module Mat = Dynsys.Mat
  module Coeff = Mat.Coeff
  module Lmi = Osdp.Lmi.Make (Mat)

  (* ---- Guard rows ---------------------------------------------------- *)

  (* Recovers [c; -a_1; ...; -a_d] (a row of Guard.homogeneize's [c -T]
     form, i.e. "c - a.x >= 0") from a (1,x)^T Q (1,x) affine-guard
     embedding: Q_00 = c, Q_(0,k) = Q_(k,0) = -a_(k-1)/2 for k=1..d (see
     affine_guard in piecewise_linear_examples.ml, whose construction this
     undoes). Every guard used by this algorithm is affine (matching the
     Matlab source's Contrainte-only model), so this is exact, not an
     approximation. *)
  let affine_row (q : Mat.t) : Coeff.t array =
    let qq = Mat.to_array_array q in
    let two = Coeff.of_int 2 in
    Array.mapi (fun k c -> if k = 0 then c else Coeff.mult two c) qq.(0)

  let guard_rows (g : Dynsys.quad_guard_t) : Coeff.t array list = List.map (fun (m, _) -> affine_row m) g

  (* Split by strictness, for the Motzkin feasibility test (is_feasible
     below) -- the S-procedure/quadratization construction later in this
     file always uses the combined [guard_rows] instead, since strictness
     doesn't matter there. *)
  let strict_rows (g : Dynsys.quad_guard_t) : Coeff.t array list =
    List.filter_map (function m, Dynsys.Strict -> Some (affine_row m) | _, Dynsys.Weak -> None) g

  let weak_rows (g : Dynsys.quad_guard_t) : Coeff.t array list =
    List.filter_map (function m, Dynsys.Weak -> Some (affine_row m) | _, Dynsys.Strict -> None) g

  (* the (d+1)x(d+1) homogenized update matrix F_i = [1 0; b A_i] (see
     Law.homogeneize: M=[1,zeros(1,d);vector matrix]). [b] defaults to the
     zero vector, matching Dynsys.lin_update_t's own inability to
     represent a nonzero offset (see the scope note above) -- callers that
     need a genuinely affine update (like the running example, whose modes
     each have a translation offset) pass it in separately via
     [invariant]'s [?offsets]. *)
  let homogenize_update (d : int) (b : Coeff.t array) (a : Mat.t) : Mat.t =
    let aa = Mat.to_array_array a in
    Mat.of_array_array
      (Array.init (d + 1) (fun r ->
           Array.init (d + 1) (fun c ->
               if r = 0 && c = 0 then Coeff.one
               else if r = 0 then Coeff.zero
               else if c = 0 then b.(r - 1)
               else aa.(r - 1).(c - 1))))

  (* row . F, i.e. the guard row expressed in terms of the pre-image under
     the homogenized update F (used to pull a successor cell's guard back
     through a transition) *)
  let row_through (f : Mat.t) (row : Coeff.t array) : Coeff.t array =
    let fa = Mat.to_array_array f in
    let d1 = Array.length row in
    Array.init d1 (fun c ->
        let s = ref Coeff.zero in
        Array.iteri (fun r rc -> s := Coeff.add !s (Coeff.mult rc fa.(r).(c))) row;
        !s)

  (* ---- Feasibility test (Guard.TestFeasible / MotzkinTest) ----------- *)

  (* "exists x: strict_rows.(1,x) > 0 elementwise AND weak_rows.(1,x) >=
     0 elementwise" (rows include the homogeneous "z=1" positivity row,
     see [with_positivity]/[positivity_row] below, but that's now just a
     harmless always-true constant row from LpFeasible's point of view,
     not load-bearing the way it was for the previous Motzkin-based
     encoding -- see LpFeasible's own comment for why this checks the
     primal system directly instead). *)
  let is_feasible (strict : Coeff.t array list) (weak : Coeff.t array list) (d : int) : bool =
    let to_q = List.map (Array.map Coeff.to_q) in
    LpFeasible.is_feasible (to_q strict) (to_q weak) d

  (* the guard's own homogeneous "z=1" row, prefixed onto quadratization
     row-sets (harmless/sound to include as an extra S-procedure term
     there, unlike in the Motzkin feasibility test above where it must be
     handled as the strict row specifically -- see is_feasible) *)
  let positivity_row d = Array.init (d + 1) (fun k -> if k = 0 then Coeff.one else Coeff.zero)
  let with_positivity d rows = positivity_row d :: rows

  (* ---- The init region: a ball, not a polytope -----------------------

     Unlike Matlab's PWA.init (a general polytope, same representation as
     every other guard), Dynsys.lin_t's init is a ball_t (center, radius):
     Cast.ball_to_semialg's convention, "r^2 - ||x-c||^2 >= 0". This is a
     genuine quadratic constraint, not decomposable into the affine-row
     form the rest of this module works with, so it's handled on its own:
     - the exact (d+1)x(d+1) quadratic form is used directly in the LMI
       (a single scalar S-procedure multiplier, rather than a matrix of
       per-row multipliers -- there's only one constraint, not a list of
       affine ones);
     - for the cheap "does this cell's guard even intersect init" gate
       (isinit.m's I(i)), an axis-aligned bounding box of the ball is used
       as an affine approximation, so the existing Motzkin feasibility
       test can be reused. This can only be a false positive (flagging an
       intersection that doesn't quite exist for the true ball), never a
       false negative, so it never drops a genuinely-needed init
       constraint -- at worst it adds one extra, still-sound constraint
       for a cell that turns out not to matter. *)
  let ball_quadratic_form ((center, radius) : Dynsys.ball_t) : Mat.t =
    let d = Array.length center in
    let q = Array.make_matrix (d + 1) (d + 1) Coeff.zero in
    let sum_c2 = Array.fold_left (fun acc c -> Coeff.add acc (Coeff.mult c c)) Coeff.zero center in
    q.(0).(0) <- Coeff.sub (Coeff.mult radius radius) sum_c2;
    Array.iteri
      (fun k c ->
        q.(0).(k + 1) <- c;
        q.(k + 1).(0) <- c)
      center;
    for k = 1 to d do
      q.(k).(k) <- Coeff.of_int (-1)
    done;
    Mat.of_array_array q

  let ball_bounding_box_rows ((center, radius) : Dynsys.ball_t) : Coeff.t array list =
    let d = Array.length center in
    List.concat
      (List.init d (fun k ->
           let upper = Array.make (d + 1) Coeff.zero in
           (* c_k + r - x_k >= 0 *)
           upper.(0) <- Coeff.add center.(k) radius;
           upper.(k + 1) <- Coeff.of_int (-1);
           let lower = Array.make (d + 1) Coeff.zero in
           (* x_k - (c_k - r) >= 0 *)
           lower.(0) <- Coeff.sub center.(k) radius;
           lower.(0) <- Coeff.mult (Coeff.of_int (-1)) lower.(0);
           lower.(k + 1) <- Coeff.one;
           [ upper; lower ]))

  (* ---- Path enumeration (compute_paths.m) ---------------------------- *)

  type path = int array (* cell indices, most-recent last, length <= k *)

  let compute_paths (adjacent : int -> int -> bool) (nb_cells : int) (k : int) : path list =
    let rec grow n =
      if n <= 1 then List.init nb_cells (fun i -> [| i |])
      else
        let shorter = grow (n - 1) in
        let extended =
          List.concat_map
            (fun p ->
              let last = p.(Array.length p - 1) in
              List.filter_map
                (fun j -> if adjacent last j then Some (Array.append p [| j |]) else None)
                (List.init nb_cells (fun j -> j)))
            shorter
        in
        shorter @ extended
    in
    grow (max k 1)

  let path_index (paths : path array) (p : path) : int =
    let n = Array.length paths in
    let rec find i = if i >= n then assert false else if paths.(i) = p then i else find (i + 1) in
    find 0

  (* the path obtained by appending cell j to path p, sliding the window
     (dropping the oldest cell) if already at length k *)
  let extend_path (p : path) (j : int) (k : int) : path =
    let p = if Array.length p >= k then Array.sub p 1 (Array.length p - 1) else p in
    Array.append p [| j |]

  (* ---- Main algorithm -------------------------------------------------- *)

  type result = {
    paths : path array;
    certificates : Mat.t array; (* M_path, size (d+1)x(d+1), per path *)
    a : Coeff.t;
    b : Coeff.t;
  }

  (* Bisection-based search for a good (alpha,beta), replacing a single
     direct [Minimize (a+b)] solve (see the note on [search_alpha_beta]'s
     caller for why). [feasible_at a b] must be monotonic in each argument
     separately (increasing either only relaxes the problem: alpha only
     ever appears subtracted in the init/boundedness constraints, beta only
     ever appears added in the boundedness constraint), which holds here
     but isn't checked -- passing a non-monotonic [feasible_at] will just
     make the search's result meaningless, not raise.

     Both alpha and beta are treated as non-negative reals here (beta
     genuinely must be, since it bounds a squared norm; alpha could in
     principle be negative for some systems, a case this search doesn't
     handle -- a known, narrow limitation). *)
  let bracket_steps = 12
  let bisect_steps = 15

  (* Minimal v >= 0 with [feasible v], via galloping out to a feasible
     upper bound then bisecting down -- same shape as
     PropSOSTemplates.search_alpha's bracket/bisect, specialized to a
     single non-negative parameter. [None] if not even a generously grown
     seed is feasible. *)
  let bisect_min (feasible : Coeff.t -> bool) (seed : Coeff.t) : Coeff.t option =
    let two = Coeff.of_int 2 in
    let seed = if Coeff.compare seed Coeff.zero <= 0 then Coeff.one else seed in
    let rec grow v n = if feasible v then Some v else if n <= 0 then None else grow (Coeff.mult v two) (n - 1) in
    match grow seed bracket_steps with
    | None -> None
    | Some hi0 ->
      let rec gallop_down delta lo hi n =
        if n <= 0 then (lo, hi)
        else
          let cand = Coeff.sub hi delta in
          if Coeff.compare cand Coeff.zero > 0 && feasible cand then gallop_down (Coeff.mult delta two) lo cand (n - 1)
          else (cand, hi)
      in
      let lo, hi = gallop_down Coeff.one hi0 hi0 bracket_steps in
      let rec bisect lo hi n =
        if n <= 0 then hi
        else
          let mid = Coeff.div (Coeff.add lo hi) two in
          if feasible mid then bisect lo mid (n - 1) else bisect mid hi (n - 1)
      in
      Some (bisect lo hi bisect_steps)

  (* alpha and beta interact (both appear in the boundedness constraint,
     whose relevant corner term is exactly beta-alpha), so this isn't a
     single monotonic parameter to bisect; instead, alternate bisecting
     each one holding the other fixed (coordinate descent) for a handful
     of rounds, after first finding ANY jointly-feasible seed point to
     bisect from.

     The seed search tries (alpha,beta) pairs, NOT alpha=beta=v for
     growing v: that direction can never work here, since beta-alpha is
     then identically 0 regardless of v's size (confirmed: this was the
     search's very first, broken version). Instead grow alpha outward,
     and for each candidate alpha do a full inner doubling search over
     beta, so any needed ratio between them is eventually covered
     regardless of the system's actual scale. *)
  let search_rounds = 8

  let search_alpha_beta (feasible_at : Coeff.t -> Coeff.t -> bool) : (Coeff.t * Coeff.t) option =
    let two = Coeff.of_int 2 in
    (* [seed_for outer inner] grows [outer]'s parameter, and for each
       candidate value does a full inner doubling search over [inner]'s
       parameter; [outer]/[inner] pick out which of alpha/beta plays which
       role, so calling this both ways gives two seeds biased toward
       opposite ends of the (alpha,beta) ratio spectrum -- important since
       alternating descent below converges to whichever *local*
       coordinatewise-minimal point is nearest its starting seed, not
       necessarily the point minimizing alpha+beta overall (confirmed:
       from a single seed it plateaus after ~3 rounds at a point looser
       than the true optimum). *)
    let seed_for feasible_at =
      let rec try_inner outer inner ni =
        if feasible_at outer inner then Some (outer, inner)
        else if ni <= 0 then None
        else try_inner outer (Coeff.mult inner two) (ni - 1)
      in
      let rec try_outer outer no =
        match try_inner outer Coeff.one bracket_steps with
        | Some oi -> Some oi
        | None -> if no <= 0 then None else try_outer (Coeff.mult outer two) (no - 1)
      in
      try_outer Coeff.one bracket_steps
    in
    let alternate feasible_at a b n =
      let rec go a b n =
        if n <= 0 then (a, b)
        else
          let a' = match bisect_min (fun x -> feasible_at x b) a with Some x -> x | None -> a in
          let b' = match bisect_min (fun x -> feasible_at a' x) b with Some x -> x | None -> b in
          go a' b' (n - 1)
      in
      go a b n
    in
    let seed1 = seed_for feasible_at in
    let seed2 = seed_for (fun b a -> feasible_at a b) in
    (* seed2 grew what it thinks of as "alpha" first, but that's really
       beta in [feasible_at]'s own argument order -- swap back. *)
    let seed2 = match seed2 with Some (b, a) -> Some (a, b) | None -> None in
    let candidates =
      List.filter_map
        (fun seed ->
          match seed with
          | None -> None
          | Some (a, b) -> Some (alternate feasible_at a b search_rounds))
        [ seed1; seed2 ]
    in
    match candidates with
    | [] -> None
    | best :: rest ->
      Some
        (List.fold_left
           (fun (a, b) (a', b') -> if Coeff.gt (Coeff.add a b) (Coeff.add a' b') then (a', b') else (a, b))
           best rest)

  (* Cheap, solver-free count of how many paths of length <= k [invariant]
     would need a certificate for -- just the switch-graph adjacency
     (Motzkin/LP feasibility checks, not full SDP solves) plus path
     enumeration. Useful to gauge problem size before committing to a
     (possibly very expensive, since it's one certificate matrix, and
     several nonneg-multiplier matrices, per path) full [invariant] solve:
     path counts grow fast with k (e.g. 4, 17, 73, 314 for k=1..4 on the
     paper's own running_example), and so does the resulting SDP. *)
  let count_paths ?offsets (k : int) (sys : Dynsys.lin_t) : int =
    let d = sys.Dynsys.df in
    let cells = Array.of_list sys.Dynsys.map in
    let nb_cells = Array.length cells in
    let offsets =
      match offsets with Some o -> o | None -> Array.make nb_cells (Array.make d Coeff.zero)
    in
    let cell_f i = homogenize_update d offsets.(i) (snd cells.(i)) in
    let adjacent i j =
      let fi = cell_f i in
      let strict =
        positivity_row d
        :: (strict_rows (fst cells.(i)) @ List.map (row_through fi) (strict_rows (fst cells.(j))))
      in
      let weak = weak_rows (fst cells.(i)) @ List.map (row_through fi) (weak_rows (fst cells.(j))) in
      is_feasible strict weak d
    in
    List.length (compute_paths adjacent nb_cells k)

  (* [?fixed_a]/[?fixed_b] pin alpha/beta to concrete values (as two-sided
     PSD equality constraints, same trick as [is_feasible]'s [eqs]) instead
     of leaving them free under the [Minimize (a+b)] objective. A pure
     feasibility check at a fixed target is far more numerically robust
     than a joint minimization for diagnosing whether a given (alpha,beta)
     is actually achievable, without waiting on a full interior-point
     convergence that may hit solver capacity limits before reaching the
     optimum (see propSOSTemplates.ml's search_alpha for the same
     motivation elsewhere in this codebase). *)
  let invariant ?(nonhom = true) ?offsets ?options ?solver ?fixed_a ?fixed_b (k : int)
      (sys : Dynsys.lin_t) : Osdp.SdpRet.t * result option =
    if sys.Dynsys.di > 0 then
      invalid_arg
        "PiecewiseQuadraticTemplates.invariant: di > 0 is not supported (the source has no \
         input concept)";
    let d = sys.Dynsys.df in
    let cells = Array.of_list sys.Dynsys.map in
    let nb_cells = Array.length cells in
    let offsets =
      match offsets with
      | Some o -> o
      | None -> Array.make nb_cells (Array.make d Coeff.zero)
    in
    let cell_raw_rows i = guard_rows (fst cells.(i)) in
    let cell_guard_rows = Array.init nb_cells (fun i -> with_positivity d (cell_raw_rows i)) in
    let cell_f i = homogenize_update d offsets.(i) (snd cells.(i)) in

    (* Laws.switches: over-approximated feasible transitions i -> j, and
       the combined (guard_i /\ pre-image of guard_j under update_i) rows
       used to quadratize that transition's guard (combined: strictness
       doesn't matter for that quadratization, only for the feasibility
       test below -- see the note on [guard_rows]/[strict_rows]). Strict
       rows pulled back through the update stay strict (pre-imaging a
       strict half-space under an affine map is still a strict
       half-space). *)
    let switch_rows : Coeff.t array list option array array = Array.make_matrix nb_cells nb_cells None in
    for i = 0 to nb_cells - 1 do
      let fi = cell_f i in
      for j = 0 to nb_cells - 1 do
        let combined = cell_raw_rows i @ List.map (row_through fi) (cell_raw_rows j) in
        let strict =
          positivity_row d
          :: (strict_rows (fst cells.(i)) @ List.map (row_through fi) (strict_rows (fst cells.(j))))
        in
        let weak = weak_rows (fst cells.(i)) @ List.map (row_through fi) (weak_rows (fst cells.(j))) in
        if is_feasible strict weak d then switch_rows.(i).(j) <- Some (with_positivity d combined)
      done
    done;
    let adjacent i j = match switch_rows.(i).(j) with Some _ -> true | None -> false in

    (* isinit.m: which cells intersect the init region (via the bounding-box
       gate, see the note above ball_quadratic_form/ball_bounding_box_rows;
       the bounding box itself is always weak, being an axis-aligned
       over-approximation of a closed ball). *)
    let init_ball_q = ball_quadratic_form sys.Dynsys.init in
    let cell_meets_init =
      Array.init nb_cells (fun i ->
          let strict = positivity_row d :: strict_rows (fst cells.(i)) in
          let weak = weak_rows (fst cells.(i)) @ ball_bounding_box_rows sys.Dynsys.init in
          is_feasible strict weak d)
    in

    let paths = Array.of_list (compute_paths adjacent nb_cells k) in
    let nb_paths = Array.length paths in
    let path_last p = p.(Array.length p - 1) in

    (* M_path = [0 q^T; q P], the (d+1)x(d+1) certificate for each path *)
    let unknown_p = Array.init nb_paths (fun i -> snd (Lmi.var_var (Printf.sprintf "P%d" i) d)) in
    let unknown_q =
      Array.init nb_paths (fun i ->
          if nonhom then Array.init d (fun c -> snd (Lmi.var_var (Printf.sprintf "q%d_%d" i c) 1))
          else Array.make d (Lmi.zeros 1 1))
    in
    let m_path i =
      let qcol = Lmi.block (Array.map (fun c -> [| c |]) unknown_q.(i)) in
      Lmi.block [| [| Lmi.zeros 1 1; Lmi.transpose qcol |]; [| qcol; unknown_p.(i) |] |]
    in

    let _a_var, a_expr = Lmi.var_var "a" 1 in
    let _b_var, b_expr = Lmi.var_var "b" 1 in
    let bound_mat =
      (* [b 0; 0 -eye_d] *)
      Lmi.block [| [| b_expr; Lmi.zeros 1 d |]; [| Lmi.zeros d 1; Lmi.(Coeff.of_int (-1) *. eye d) |] |]
    in
    let r_mat =
      (* [a 0; 0 0] *)
      Lmi.block [| [| a_expr; Lmi.zeros 1 d |]; [| Lmi.zeros d 1; Lmi.zeros d d |] |]
    in

    (* A grid of individually-declared nonneg 1x1 Lmi scalars, assembled
       into a nonneg n x n matrix -- see the "faithful multiplier
       matrices" note at the top of this file. Forced *symmetric* here
       (same Lmi var reused at (i,j) and (j,i)), unlike Matlab's plain
       sdpvar(n,n): Osdp.Lmi.solve requires every constraint to evaluate
       to a symmetric matrix (raises Not_symmetric otherwise, confirmed
       empirically), and this turns out to be mathematically necessary
       here regardless, not just an osdp restriction -- El^T.W.El
       inherits W's antisymmetric part as its own antisymmetric part
       (transpose flips the sign), and since it appears inside an
       otherwise-symmetric equation (M_path +/- El^T.W.El +/- ... ), that
       antisymmetric part would have nothing to cancel against unless it's
       zero, i.e. unless W is symmetric. Still fully expressive (genuine
       cross-terms between different guard rows), just symmetric ones. *)
    let nonneg_matrix name n =
      let g = Array.make_matrix n n (Lmi.zeros 1 1) in
      let vars = ref [] in
      for i = 0 to n - 1 do
        for j = i to n - 1 do
          let v = snd (Lmi.var_var (Printf.sprintf "%s_%d_%d" name i j) 1) in
          vars := v :: !vars;
          g.(i).(j) <- v;
          g.(j).(i) <- v
        done
      done;
      Lmi.block g, !vars
    in
    let quad_form (rows : Coeff.t array list) (mult_expr : Lmi.matrix_expr) : Lmi.matrix_expr =
      (* rows^T . mult_expr . rows, where rows is a concrete (m x (d+1))
         matrix and mult_expr an m x m Lmi expression *)
      let el = Lmi.const (Mat.of_list_list (List.map Array.to_list rows)) in
      Lmi.(transpose el * mult_expr * el)
    in

    let lmis = ref [ b_expr ] in
    let add lmi = lmis := lmi :: !lmis in

    (* boundedness: M_path - Q_plast^T.W.Q_plast + Bound - R >= 0 *)
    Array.iteri
      (fun i path ->
        let plast = path_last path in
        let rows = cell_guard_rows.(plast) in
        let w, w_vars = nonneg_matrix (Printf.sprintf "W%d" i) (List.length rows) in
        List.iter add w_vars;
        add Lmi.(m_path i - quad_form rows w + bound_mat - r_mat))
      paths;

    (* init: only for length-1 paths whose (single) cell intersects Init.
       A single scalar S-procedure multiplier against the exact ball
       quadratic form (see the note above ball_quadratic_form): there's
       one quadratic constraint here, not a list of affine ones, so
       nonneg_matrix's per-row-pair machinery doesn't apply. *)
    Array.iteri
      (fun i path ->
        if Array.length path = 1 && cell_meets_init.(path.(0)) then begin
          let x_expr = snd (Lmi.var_var (Printf.sprintf "X%d" i) 1) in
          add x_expr;
          add Lmi.(r_mat - m_path i - (x_expr * const init_ball_q))
        end)
      paths;

    (* transition: for every path i and cell j reachable from plast,
       M_path(i) - F_plast^T.M_next.F_plast - El^T.U.El >= 0, where next is
       path(i) extended by j (sliding the window at length k) *)
    for i = 0 to nb_paths - 1 do
      let plast = path_last paths.(i) in
      for j = 0 to nb_cells - 1 do
        match switch_rows.(plast).(j) with
        | None -> ()
        | Some rows ->
          let next = extend_path paths.(i) j k in
          let idnext = path_index paths next in
          let fi = Lmi.const (cell_f plast) in
          let u, u_vars = nonneg_matrix (Printf.sprintf "U%d_%d" i j) (List.length rows) in
          List.iter add u_vars;
          add Lmi.(m_path i - transpose fi * m_path idnext * fi - quad_form rows u)
      done
    done;

    let base_lmis = !lmis in
    let pin expr v acc =
      let diff = Lmi.(expr - const (Mat.of_list_list [ [ v ] ])) in
      diff :: Lmi.Minus diff :: acc
    in
    let lmis_at fixed_a fixed_b =
      let acc = match fixed_a with None -> base_lmis | Some v -> pin a_expr v base_lmis in
      match fixed_b with None -> acc | Some v -> pin b_expr v acc
    in
    let solve_at fixed_a fixed_b = Lmi.solve ?options ?solver (Lmi.Minimize Lmi.(a_expr + b_expr)) (lmis_at fixed_a fixed_b) in
    let feasible_at a b = Osdp.SdpRet.is_success (let ret, _, _ = solve_at (Some a) (Some b) in ret) in

    (* When the caller pins alpha and/or beta explicitly, solve once at
       those values (the diagnostic/probing use case). Otherwise auto-search
       for a good (alpha,beta) via alternating bisection (see
       search_alpha_beta above the [nonneg_matrix] note -- actually defined
       just below) before the final solve that extracts certificates: a
       direct [Minimize (a+b)] can fail to converge well before reaching
       the true optimum on larger examples (confirmed on the paper's own
       running_example: CSDP's primal/dual objectives stalled around
       ~3030-3060 and then failed outright, while pure feasibility checks
       at fixed (alpha,beta) close to the paper's own reported optimum --
       242.0155/2173.8501 -- succeed cleanly, meaning the true optimum was
       being approached but never reached), the same class of numerical
       fragility PropSOSTemplates.search_alpha works around elsewhere in
       this codebase. *)
    let final_a, final_b =
      match fixed_a, fixed_b with
      | Some a, Some b -> (Some a, Some b)
      | _ -> (
        match search_alpha_beta feasible_at with
        | None -> (fixed_a, fixed_b)
        | Some (a, b) ->
          (* [a, b] sit right at the numerical feasibility boundary
             bisection converged to, where CSDP's verdict isn't perfectly
             reproducible (confirmed empirically: the exact same (a,b) pin
             came back PartialSuccess in one process run and DualInfeasible
             in another) -- re-solving exactly there for the final
             certificate is unreliable, so back off with a small,
             growing safety margin (still sound: larger alpha/beta only
             relaxes the constraints) until a solve actually succeeds. *)
          let rec with_margin pct =
            if pct > 10 then (Some a, Some b) (* exact values, as a last resort *)
            else
              let factor = Coeff.of_float (1. +. (0.01 *. float_of_int pct)) in
              let a' = Coeff.mult a factor and b' = Coeff.mult b factor in
              if feasible_at a' b' then (Some a', Some b') else with_margin (pct + 1)
          in
          with_margin 1)
    in
    let ret, _, values = solve_at final_a final_b in
    if Osdp.SdpRet.is_success ret then
      try
        let certificates = Array.init nb_paths (fun i -> Lmi.value_mat (m_path i) values) in
        let a = Lmi.value a_expr values in
        let b = Lmi.value b_expr values in
        ret, Some { paths; certificates; a; b }
      with Not_found -> ret, None
    else ret, None
end
