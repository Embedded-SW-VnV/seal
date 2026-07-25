(* Empirical soundness sweep: forward-simulate real trajectories of a system
   and check every Analysis method's claimed invariant against them, per the
   investigation brief in the lustrec-side scratchpad (apparent unsoundness
   found in prop_driven_sos_lyap/liouville_method on Polynomial_examples.ex1
   "Pierre1"). Separate executable from run_examples.ml's smoke test since
   this one is deliberately slow (many SDP solves across degrees). *)

module Sys = Seal.Dynsys.Float
module Ana = Seal.Analysis.Make (Sys)
module Sim = Seal.Simulate.Make (Sys)
module Check = Seal.Soundness_check.Make (Sys)
module PQuad = Seal.PiecewiseQuadraticTemplates.Make (Sys)

let pf = Format.printf

let ex1 = Polynomial_examples.ex1

let norm2 (state : float array) = Array.fold_left (fun a x -> a +. (x *. x)) 0. state

(* Synthetic switched + input system, built to have a *known* common
   Lyapunov function (P=I), unlike MignoneInvariance1: A0/A1 are both a
   0.5-scaled 90-degree rotation (one +90, one -90), so A_i'*I*A_i = 0.25*I
   for both modes regardless of which is active -- P=I trivially works.
   Same B (gain 1) and input bound in both modes; switches on sign(x0), a
   real (if simplistic) state-dependent partition, to exercise actual
   guard-driven switching under simulation, not just a direct matrix check. *)
let switched_input_example : Sys.lin_t =
  let c = Sys.Coeff.of_float in
  let carr = Array.map c in
  let crows = List.map (List.map c) in
  let g a b = Piecewise_linear_examples.affine_guard (carr a) (c b) in
  let a0 = Sys.Mat.of_list_list (crows [ [ 0.; -0.5; 1. ]; [ 0.5; 0.; 0. ] ]) in
  let a1 = Sys.Mat.of_list_list (crows [ [ 0.; 0.5; 1. ]; [ -0.5; 0.; 0. ] ]) in
  {
    Sys.df = 2;
    di = 1;
    map = [ ([ g [| -1.; 0. |] 0. ], a0); ([ g [| 1.; 0. |] 0. ], a1) ];
    init = (carr [| 0.; 0. |], c 1e-4);
    input = Some (carr [| 0. |], c 1.);
    r_g = Some (c 10.);
  }

(* Small 2x2-matrix helpers, reused by every direct (non-simulation) check
   of a Lyapunov/invariance LMI against the actual returned P/A matrices. *)
let to_2x2 m =
  match List.map (List.map Sys.Coeff.to_float) (Sys.Mat.to_list_list m) with
  | [ [ a00; a01 ]; [ a10; a11 ] ] -> (a00, a01, a10, a11)
  | _ -> assert false

let atpa (a00, a01, a10, a11) (p00, p01, p10, p11) =
  (* A'PA where A' rows/cols swapped: (A'PA)_ij = sum_kl A_ki P_kl A_lj *)
  let a = [| [| a00; a01 |]; [| a10; a11 |] |] in
  let p = [| [| p00; p01 |]; [| p10; p11 |] |] in
  let get i j =
    let s = ref 0. in
    for k = 0 to 1 do
      for l = 0 to 1 do
        s := !s +. (a.(k).(i) *. p.(k).(l) *. a.(l).(j))
      done
    done;
    !s
  in
  (get 0 0, get 0 1, get 1 0, get 1 1)

(* Sylvester's criterion for a symmetric 2x2 [[a,b];[b,d]] being PSD:
   a>=0, d>=0, a*d-b*b>=0 (using a small negative tolerance for float noise) *)
let is_psd ?(tol = 1e-9) (a, b, _b', d) =
  a >= -.tol && d >= -.tol && (a *. d) -. (b *. b) >= -.tol

let pp_2x2 (a, b, c, d) = Printf.sprintf "[[%.6g;%.6g];[%.6g;%.6g]]" a b c d
let sub_2x2 (a, b, c, d) (a', b', c', d') = (a -. a', b -. b', c -. c', d -. d')
let scale_2x2 k (a, b, c, d) = (k *. a, k *. b, k *. c, k *. d)

(* Ground truth: a large batch of random trajectories, plus per-target
   adversarial (bang-bang-seeking) batches, since random sampling alone
   under-explores the extremes of a bounded-input system. *)
let ntraj_random = 2000
let ntraj_adversarial = 300
let nsteps = 2000

let simulate ~seed ~input_mode = Sim.run ~seed ~input_mode ex1 ~ntraj:ntraj_random ~nsteps

let simulate_adv ~seed monitor =
  Sim.run ~seed ~input_mode:(Sim.Adversarial monitor) ex1 ~ntraj:ntraj_adversarial ~nsteps

let random_points = lazy (simulate ~seed:1 ~input_mode:Sim.Uniform)
let norm2_adv_points = lazy (simulate_adv ~seed:2 norm2)
let axis_adv_points =
  lazy (List.init ex1.df (fun i -> (simulate_adv ~seed:(10 + (2 * i)) (fun s -> s.(i)),
                                     simulate_adv ~seed:(11 + (2 * i)) (fun s -> -.s.(i)))))

let all_points_for_norm () = Lazy.force random_points @ Lazy.force norm2_adv_points

let all_points_for_axis i =
  let plus, minus = List.nth (Lazy.force axis_adv_points) i in
  Lazy.force random_points @ plus @ minus

let print_empirical_box () =
  let bb = Sim.bounding_box (Lazy.force random_points) ~df:ex1.df in
  pf "@[<v>== Empirical bounding box for ex1, %d random traj x %d steps ==@ " ntraj_random nsteps;
  Array.iteri (fun i (lo, hi) -> pf "x%d in [%.6g, %.6g]@ " i lo hi) bb;
  let bb_adv = Sim.bounding_box (all_points_for_norm ()) ~df:ex1.df in
  pf "(with ||x||^2-adversarial batch added:)@ ";
  Array.iteri (fun i (lo, hi) -> pf "x%d in [%.6g, %.6g]@ " i lo hi) bb_adv;
  pf "@]@."

let print_round_shape_affine () =
  pf "@[<v>== round / shape / affine on ex1 (cast to lin_t) ==@ ";
  let lin = Sys.poly_to_linear ex1 in
  let pts = all_points_for_norm () in
  List.iter
    (fun (name, f) ->
      let r : Ana.analysis_result_t = f lin in
      pf "* %s: status=%a@ " name Osdp.SdpRet.pp r.status;
      List.iter
        (fun (_, sa) -> pf "  %a@ " Check.pp_result (Check.check sa pts))
        r.postfixpoint)
    [ ("round", (fun sys -> Ana.round sys)); ("shape", (fun sys -> Ana.shape sys)); ("affine", (fun sys -> Ana.affine sys)) ];
  pf "@]@."

module QuadTemplates = Seal.QuadraticTemplates.Make (Sys)

(* Diagnostic: Analysis.round/shape/affine's postfixpoint wraps the raw
   ellipsoid matrix P via [Cast.poly_of_quadratic_form] with its *default*
   [is_homogenous=true], giving the bare homogeneous form [x'Px] with no
   constant subtracted -- but the actual proven claim is [x'Px <= 1], not
   [x'Px <= 0] (compare Analysis.piecewise_lin's wrapper, which explicitly
   does [- const alpha]). Check the raw matrix against the *correct*
   threshold directly, bypassing Analysis's wrapper, to see whether the
   underlying LMI computation is itself sound once the right threshold is
   used. *)
let print_quad_template_raw_check () =
  pf "@[<v>== round / shape / affine RAW check (x'Px <= 1, bypassing Analysis's wrapper) ==@ ";
  let lin = Sys.poly_to_linear ex1 in
  let pts = all_points_for_norm () in
  List.iter
    (fun (name, f) ->
      match f lin with
      | status, Some (p, _values) ->
        let quad = Sys.Cast.poly_of_quadratic_form ~is_homogenous:true p in
        let sa : Sys.semialgebraic_t = [ [ Sys.Poly.(quad - const Sys.Coeff.one) ] ] in
        pf "* %s: status=%a  %a@ " name Osdp.SdpRet.pp status Check.pp_result (Check.check sa pts)
      | status, None -> pf "* %s: status=%a (no result)@ " name Osdp.SdpRet.pp status)
    [ ("round", (fun s -> QuadTemplates.round s)); ("shape", (fun s -> QuadTemplates.shape s));
      ("affine", (fun s -> QuadTemplates.affine s)) ];
  pf "@]@."

(* Osdp.Lmi's own doc pins the sign convention: every matrix_expr in the lmi
   list must be PSD (not <=0 as one might guess from being called an
   "inequality"). Re-deriving round's constraints under that convention:
   exp1 = P - A'PA - eps*I >= 0 (PSD)  <=>  A'PA <= P - eps*I  <  P
   -- i.e. (Ax)'P(Ax) < x'Px strictly: energy decreases under x'=Ax, exactly
   the Lyapunov property this is supposed to prove. exp2 = P - I >= 0 <=>
   P >= I (not P<=I as I'd misread it before). shape's expr1 = lambda*P -
   A'PA >= 0 <=> (Ax)'P(Ax) <= lambda*x'Px, contraction rate lambda in
   [0,1] found by TUtils.dicho. This check verifies these two properties
   directly against the actual returned P/lambda (matrix arithmetic, no
   solver involved) and separately by simulating x'=Ax with u=0 (round/shape
   are only ever claimed for the driftless system) from points seeded on
   each ellipsoid's own boundary. *)
let print_round_shape_lyapunov_check () =
  pf "@[<v>== round/shape: core Lyapunov property check (u=0 only) ==@ ";
  let lin = Sys.poly_to_linear ex1 in
  let a =
    match QuadTemplates.get_sys_mat lin with
    | QuadTemplates.Aff (a, _) -> a
    | QuadTemplates.Lin a -> a
  in
  let to_2x2 m =
    match List.map (List.map Sys.Coeff.to_float) (Sys.Mat.to_list_list m) with
    | [ [ a00; a01 ]; [ a10; a11 ] ] -> (a00, a01, a10, a11)
    | _ -> assert false
  in
  let (a00, a01, a10, a11) as amat = to_2x2 a in
  pf "A = [[%.6g;%.6g];[%.6g;%.6g]]@ " a00 a01 a10 a11;
  let check name p lambda =
    let pmat = to_2x2 p in
    let m = sub_2x2 (scale_2x2 lambda pmat) (atpa amat pmat) in
    pf "* %s: P=%s@ " name (pp_2x2 pmat);
    pf "  lambda*P - A'PA = %s -> %s (PSD required)@ " (pp_2x2 m)
      (if is_psd m then "PSD (holds)" else "NOT PSD (Lyapunov claim FALSE)")
  in
  (match QuadTemplates.round lin with
   | _, Some (p, _) -> check "round (lambda=1, minus solver's own eps margin)" p 1.
   | _, None -> pf "* round: no result@ ");
  (match QuadTemplates.shape lin with
   | _, Some (p, values) ->
     let lambda = Sys.Coeff.to_float (QuadTemplates.Lmi.value QuadTemplates.lambda_id values) in
     pf "* shape: found lambda=%.6g@ " lambda;
     check "shape" p lambda
   | _, None -> pf "* shape: no result@ ");
  (* Now the same property empirically, simulating x'=Ax (u=0) from points
     seeded on each ellipsoid's own boundary x'Px=1. *)
  let simulate_energy name p =
    let p00, p01, _, p11 = to_2x2 p in
    let energy (x0, x1) = (p00 *. x0 *. x0) +. (2. *. p01 *. x0 *. x1) +. (p11 *. x1 *. x1) in
    List.iter
      (fun (dx0, dx1) ->
        (* scale (dx0,dx1) so that energy = 1 (on the ellipsoid boundary) *)
        let e0 = energy (dx0, dx1) in
        let s = sqrt (1. /. e0) in
        let x0 = ref (dx0 *. s) and x1 = ref (dx1 *. s) in
        let energies = ref [ energy (!x0, !x1) ] in
        for _ = 1 to 20 do
          let nx0 = (a00 *. !x0) +. (a01 *. !x1) and nx1 = (a10 *. !x0) +. (a11 *. !x1) in
          x0 := nx0;
          x1 := nx1;
          energies := energy (!x0, !x1) :: !energies
        done;
        let es = List.rev !energies in
        let rec pairwise_monotone = function
          | a :: (b :: _ as tl) -> b <= a +. 1e-9 && pairwise_monotone tl
          | _ -> true
        in
        let monotone = pairwise_monotone es in
        pf "  %s from (%.3g,%.3g)/boundary: energies=%s -> %s@ " name dx0 dx1
          (String.concat "," (List.map (Printf.sprintf "%.6g") es))
          (if monotone then "non-increasing (OK)" else "INCREASED at some step (Lyapunov claim FALSE)"))
      [ (1., 0.); (0., 1.); (1., 1.); (1., -1.) ]
  in
  (match QuadTemplates.round lin with _, Some (p, _) -> simulate_energy "round" p | _ -> ());
  (match QuadTemplates.shape lin with _, Some (p, _) -> simulate_energy "shape" p | _ -> ());
  pf "@]@."

(* Validates the common-Lyapunov generalization of round/shape: a single P
   is checked directly against *every* mode's own A_i (Sylvester, no
   solver involved) -- this is the actual mathematical guarantee, valid
   under arbitrary switching between modes, not just the switching
   sequences MignoneInvariance1's own quadrant guards happen to allow.
   Simulating the real guarded system on top is a weaker, complementary
   sanity check (confirms no implementation slip), since it only ever
   exercises guard-permitted switching. *)
let print_switched_round_shape_check () =
  pf "@[<v>== round/shape common Lyapunov check on MignoneInvariance1 (4 modes) ==@ ";
  let lin = Piecewise_linear_examples.mignone_invariance_1 in
  let a_list =
    List.map (function QuadTemplates.Lin a -> a | QuadTemplates.Aff (a, _) -> a) (QuadTemplates.get_sys_mats lin)
  in
  let a_mats = List.map to_2x2 a_list in
  List.iteri (fun i (a00, a01, a10, a11) -> pf "A%d = [[%.6g;%.6g];[%.6g;%.6g]]@ " i a00 a01 a10 a11) a_mats;
  let check name p lambda =
    let pmat = to_2x2 p in
    pf "* %s: P=%s@ " name (pp_2x2 pmat);
    List.iteri
      (fun i amat ->
        let m = sub_2x2 (scale_2x2 lambda pmat) (atpa amat pmat) in
        pf "  mode %d: lambda*P - A%d'PA%d = %s -> %s@ " i i i (pp_2x2 m)
          (if is_psd m then "PSD (holds)" else "NOT PSD (Lyapunov claim FALSE for this mode)"))
      a_mats
  in
  (match QuadTemplates.round lin with
   | status, Some (p, _) ->
     pf "* round: status=%a@ " Osdp.SdpRet.pp status;
     check "round (lambda=1, minus solver's own eps margin)" p 1.
   | status, None -> pf "* round: no result (status=%a)@ " Osdp.SdpRet.pp status);
  (match QuadTemplates.shape lin with
   | status, Some (p, values) ->
     let lambda = Sys.Coeff.to_float (QuadTemplates.Lmi.value QuadTemplates.lambda_id values) in
     pf "* shape: status=%a found common lambda=%.6g@ " Osdp.SdpRet.pp status lambda;
     check "shape" p lambda
   | status, None -> pf "* shape: no result (status=%a)@ " Osdp.SdpRet.pp status);
  (* Complementary sanity check: simulate the real guarded switched system
     (u=0, di=0) and confirm energy under shape's P is non-increasing
     along actually-reachable (guard-permitted) trajectories too. *)
  (match QuadTemplates.shape lin with
   | _, Some (p, _) ->
     let p00, p01, _, p11 = to_2x2 p in
     let energy (s : float array) = (p00 *. s.(0) *. s.(0)) +. (2. *. p01 *. s.(0) *. s.(1)) +. (p11 *. s.(1) *. s.(1)) in
     let poly_sys = Sys.linear_to_poly lin in
     let pts = Sim.run ~seed:5 ~input_mode:Sim.Zero poly_sys ~ntraj:200 ~nsteps:200 in
     let energies = List.map energy pts in
     let max_e = List.fold_left max 0. energies in
     pf "shape: simulated (guard-permitted) trajectories, max energy observed = %.6g (should stay <= energy at t=0, i.e. bounded)@ " max_e
   | _ -> ());
  pf "@]@."

(* Validates the switched+input generalization end-to-end: round/shape via
   direct per-mode Sylvester check (the actual mathematical guarantee), and
   affine via full simulation (guard-driven switching + random/adversarial
   input together) against the correct x'Px<=1 threshold, the same way the
   single-mode affine fix was validated earlier. *)
let print_switched_input_check () =
  pf "@[<v>== round/shape/affine common Lyapunov check on switched_input_example (2 modes + input) ==@ ";
  let lin = switched_input_example in
  let a_list =
    List.map (function QuadTemplates.Lin a -> a | QuadTemplates.Aff (a, _) -> a) (QuadTemplates.get_sys_mats lin)
  in
  let a_mats = List.map to_2x2 a_list in
  List.iteri (fun i (a00, a01, a10, a11) -> pf "A%d = [[%.6g;%.6g];[%.6g;%.6g]]@ " i a00 a01 a10 a11) a_mats;
  let check name p lambda =
    let pmat = to_2x2 p in
    pf "* %s: P=%s@ " name (pp_2x2 pmat);
    List.iteri
      (fun i amat ->
        let m = sub_2x2 (scale_2x2 lambda pmat) (atpa amat pmat) in
        pf "  mode %d: lambda*P - A%d'PA%d = %s -> %s@ " i i i (pp_2x2 m)
          (if is_psd m then "PSD (holds)" else "NOT PSD (Lyapunov claim FALSE for this mode)"))
      a_mats
  in
  (match QuadTemplates.round lin with
   | status, Some (p, _) ->
     pf "* round: status=%a@ " Osdp.SdpRet.pp status;
     check "round (lambda=1, minus solver's own eps margin)" p 1.
   | status, None -> pf "* round: no result (status=%a)@ " Osdp.SdpRet.pp status);
  (match QuadTemplates.shape lin with
   | status, Some (p, values) ->
     let lambda = Sys.Coeff.to_float (QuadTemplates.Lmi.value QuadTemplates.lambda_id values) in
     pf "* shape: status=%a found common lambda=%.6g@ " Osdp.SdpRet.pp status lambda;
     check "shape" p lambda
   | status, None -> pf "* shape: no result (status=%a)@ " Osdp.SdpRet.pp status);
  (match QuadTemplates.affine lin with
   | status, Some (p, _) ->
     let p2x2 = to_2x2 p in
     pf "* affine: status=%a P=%s@ " Osdp.SdpRet.pp status (pp_2x2 p2x2);
     let poly_sys = Sys.linear_to_poly lin in
     let quad = Sys.Cast.poly_of_quadratic_form ~is_homogenous:true p in
     let sa : Sys.semialgebraic_t = [ [ Sys.Poly.(quad - const Sys.Coeff.one) ] ] in
     let random_pts = Sim.run ~seed:7 ~input_mode:Sim.Uniform poly_sys ~ntraj:2000 ~nsteps:2000 in
     let energy_fun (s : float array) = Sim.eval quad s [||] in
     let adv_pts = Sim.run ~seed:8 ~input_mode:(Sim.Adversarial energy_fun) poly_sys ~ntraj:300 ~nsteps:2000 in
     pf "  simulated (random+adversarial, guard-driven switching) x'Px<=1 check: %a@ " Check.pp_result
       (Check.check sa (random_pts @ adv_pts))
   | status, None -> pf "* affine: no result (status=%a)@ " Osdp.SdpRet.pp status);
  pf "@]@."

(* Direct diagnostic of PiecewiseQuadraticTemplates.invariant on the paper's
   own "running example", bypassing Analysis.piecewise_lin's wrapper, with
   solver verbosity cranked up to see the pobj/dobj convergence trace. The
   paper reports alpha_opt=242.0155, beta_opt=2173.8501 for this system
   (sum ~2415.87) using the base (non-k-inductive, i.e. k=1) method; the
   existing run_examples.ml smoke test currently gets Unknown here. *)
let print_running_example_debug () =
  pf "@[<v>== DEBUG: PiecewiseQuadraticTemplates.invariant on running_example, k=1 ==@ ";
  let quiet = PQuad.Lmi.default in
  let try_fixed fixed_a fixed_b =
    let status, res =
      PQuad.invariant ~offsets:Piecewise_linear_examples.running_example_offsets ~options:quiet
        ~fixed_a:(Sys.Coeff.of_float fixed_a) ~fixed_b:(Sys.Coeff.of_float fixed_b) 1
        Piecewise_linear_examples.running_example
    in
    pf "  fixed alpha=%.6g beta=%.6g -> status=%a (%s)@ " fixed_a fixed_b Osdp.SdpRet.pp status
      (if Osdp.SdpRet.is_success status then "FEASIBLE" else "infeasible/unknown")
    ;
    ignore res
  in
  pf "* feasibility probe at the paper's own claimed optimum (alpha=242.0155, beta=2173.8501):@ ";
  try_fixed 242.0155 2173.8501;
  pf "* bisecting along the segment from the paper's point (infeasible) to (250,2300) (feasible):@ ";
  let paper_a, paper_b = (242.0155, 2173.8501) in
  let feas_a, feas_b = (250., 2300.) in
  List.iter
    (fun t ->
      let a = paper_a +. (t *. (feas_a -. paper_a)) and b = paper_b +. (t *. (feas_b -. paper_b)) in
      try_fixed a b)
    [ 0.1; 0.2; 0.3; 0.4; 0.5; 0.6; 0.7; 0.8; 0.9 ];
  pf "* NEW auto-search (bisection-based, default when no fixed_a/fixed_b given):@ ";
  (match
     PQuad.invariant ~offsets:Piecewise_linear_examples.running_example_offsets ~options:quiet 1
       Piecewise_linear_examples.running_example
   with
   | status, Some r ->
     pf "status=%a alpha=%a beta=%a (sum=%a) (paper: alpha=242.0155 beta=2173.8501 sum=2415.87)@ "
       Osdp.SdpRet.pp status Sys.Coeff.pp r.PQuad.a Sys.Coeff.pp r.PQuad.b Sys.Coeff.pp
       Sys.Coeff.(add r.PQuad.a r.PQuad.b)
   | status, None -> pf "status=%a (no result)@ " Osdp.SdpRet.pp status);
  pf "@]@."

let print_affine_hand_check () =
  pf "@[<v>== affine: minimal hand-check (one step from the origin) ==@ ";
  let lin = Sys.poly_to_linear ex1 in
  (match QuadTemplates.affine lin with
   | status, Some (p, _) ->
     pf "status=%a@ " Osdp.SdpRet.pp status;
     let mll = Sys.Mat.to_list_list p in
     List.iter (fun row -> pf "P row: %s@ "
                   (String.concat " " (List.map (fun c -> Printf.sprintf "%.6g" (Sys.Coeff.to_float c)) row)))
       mll;
     let quad = Sys.Cast.poly_of_quadratic_form ~is_homogenous:true p in
     let evalp (x0, x1) = Sim.eval quad [| x0; x1 |] [||] in
     pf "x'Px at (0,0) = %.6g@ " (evalp (0., 0.));
     pf "x'Px at (1.6,0) [one step, u=+1, from origin] = %.6g@ " (evalp (1.6, 0.));
     pf "x'Px at (-1.6,0) [one step, u=-1, from origin] = %.6g@ " (evalp (-1.6, 0.));
     (* iterate the worst of {u=+1,u=-1} greedily for a few steps from the origin *)
     let a00, a01 = 1.5, -0.7 and a10, a11 = 1., 0. in
     let step (x0, x1) u = (a00 *. x0 +. a01 *. x1 +. 1.6 *. u, a10 *. x0 +. a11 *. x1) in
     let rec go n state =
       if n <= 0 then ()
       else begin
         let cands = [ step state 1.; step state (-1.) ] in
         let best = List.fold_left (fun best c -> if evalp c > evalp best then c else best)
             (List.hd cands) cands in
         pf "step %d: x=(%.6g,%.6g) x'Px=%.6g@ " (11 - n) (fst best) (snd best) (evalp best);
         go (n - 1) best
       end
     in
     go 10 (0., 0.)
   | status, None -> pf "status=%a (no result)@ " Osdp.SdpRet.pp status);
  pf "@]@."

let prop_degrees = [ 2; 4; 6; 8 ]

let print_prop_driven () =
  pf "@[<v>== prop_driven_sos_lyap on ex1, degrees %s ==@ "
    (String.concat "," (List.map string_of_int prop_degrees));
  List.iter
    (fun deg ->
      pf "* degree=%d@ " deg;
      let run label kappa pts =
        let r : Ana.analysis_result_t = Ana.prop_driven_sos_lyap ?kappa ex1 deg in
        pf "  [%s] status=%a@ " label Osdp.SdpRet.pp r.status;
        List.iter (fun (_, sa) -> pf "    %a@ " Check.pp_result (Check.check sa pts)) r.postfixpoint
      in
      run "kappa=default (||x||^2)" None (all_points_for_norm ());
      for i = 0 to ex1.df - 1 do
        run (Printf.sprintf "kappa=x%d" i) (Some Ana.Sos.(?? i)) (all_points_for_axis i);
        run (Printf.sprintf "kappa=-x%d" i) (Some Ana.Sos.(~- (?? i))) (all_points_for_axis i)
      done)
    prop_degrees;
  pf "@]@."

let liouville_degrees = [ 2; 4; 6 ]

let print_liouville () =
  pf "@[<v>== liouville_method on ex1 (r_g=30), degrees %s ==@ "
    (String.concat "," (List.map string_of_int liouville_degrees));
  let r_g = match ex1.r_g with Some r -> Sys.Coeff.to_float r | None -> assert false in
  let domain = Check.within_origin_ball ~radius:r_g in
  let pts = all_points_for_norm () in
  List.iter
    (fun deg ->
      let r : Ana.analysis_result_t = Ana.liouville_method ex1 deg in
      pf "* degree=%d status=%a@ " deg Osdp.SdpRet.pp r.status;
      List.iter
        (fun (_, sa) -> pf "  %a (within ||x||<=%.4g only)@ " Check.pp_result (Check.check ~domain sa pts) r_g)
        r.postfixpoint)
    liouville_degrees;
  pf "@]@."

let print_piecewise_lin () =
  pf "@[<v>== piecewise_lin (k=1) on MignoneInvariance1 ==@ ";
  let lin = Piecewise_linear_examples.mignone_invariance_1 in
  let poly_sys = Sys.linear_to_poly lin in
  let pts = Sim.run ~seed:3 ~input_mode:Sim.Uniform poly_sys ~ntraj:ntraj_random ~nsteps in
  let r = Ana.piecewise_lin 1 lin in
  pf "status=%a, %d path(s)@ " Osdp.SdpRet.pp r.status (List.length r.postfixpoint);
  List.iteri
    (fun idx (guard, sa) ->
      let conj =
        List.map (fun (m, _strictness) -> Sys.Cast.poly_of_quadratic_form ~is_homogenous:false m) guard
      in
      let domain = Check.within_conjunction conj in
      let in_region = List.filter domain pts in
      pf "* path %d (guard: %d row(s), %d/%d sim points fall in this region): %a@ " idx
        (List.length guard) (List.length in_region) (List.length pts) Check.pp_result
        (Check.check ~domain sa pts))
    r.postfixpoint;
  pf "@]@."

let print_deg6_default_kappa_debug () =
  pf "@[<v>== DEBUG: prop_driven_sos_lyap ex1 degree=6 default kappa, bisection trace ==@ ";
  let r : Ana.analysis_result_t = Ana.prop_driven_sos_lyap ex1 6 in
  pf "status=%a@ " Osdp.SdpRet.pp r.status;
  let pts = all_points_for_norm () in
  List.iter (fun (_, sa) -> pf "%a@ " Check.pp_result (Check.check sa pts)) r.postfixpoint;
  pf "@]@."

(* Regression test for a real, previously-undetected bug: is_feasible used
   to route Motzkin's transposition alternative through Osdp.Lmi's general
   SDP solver, encoded entirely via paired equality constraints ([eq;
   Minus eq], forcing exact zero slack) with no genuine SDP-matrix
   structure anywhere -- a degenerate, zero-interior problem that CSDP's
   interior-point method couldn't handle (it explicitly logged "This is a
   pure dual feasibility problem" then "Declaring dual infeasibility" even
   when a valid, hand-verified dual certificate demonstrably existed). All
   three tests below used to report FEASIBLE regardless of the actual
   math, including test2/test3 which are unambiguously, trivially
   infeasible -- this predated the strict/weak generalization entirely
   (the same paired-equality pattern was already used by the original
   single-strict-row version). Fixed by LpFeasible, which checks the
   primal system directly via a real LP solver (ocplib-simplex) instead of
   routing an equality-heavy alternative through an SDP solver. Kept here
   as a permanent regression test. *)
let print_is_feasible_unit_tests () =
  pf "@[<v>== is_feasible isolated unit tests ==@ ";
  let c = Sys.Coeff.of_float in
  (* trivially feasible: exists x, x >= 0 (e.g. x=0) *)
  let r1 = PQuad.is_feasible [ [| c 1.; c 0. |] ] [ [| c 0.; c 1. |] ] 1 in
  pf "test1 (exists x: x>=0) expect true, got %b@ " r1;
  (* trivially infeasible: exists x, -1 >= 0 (never, doesn't depend on x) *)
  let r2 = PQuad.is_feasible [ [| c 1.; c 0. |] ] [ [| c (-1.); c 0. |] ] 1 in
  pf "test2 (exists x: -1>=0) expect false, got %b@ " r2;
  (* trivially infeasible via strict: exists x, x>0 strict AND -x>=0 weak (x>0 and x<=0) *)
  let r3 = PQuad.is_feasible [ [| c 1.; c 0. |]; [| c 0.; c 1. |] ] [ [| c 0.; c (-1.) |] ] 1 in
  pf "test3 (exists x: x>0 and -x>=0) expect false, got %b@ " r3;
  pf "@]@."

(* Solver-free: just the switch-graph adjacency + path enumeration, not a
   full invariant solve (which, at k=3/k=4, is now a genuinely large SDP
   -- hundreds of path certificates -- since the switch graph is finally
   sized correctly; that's a separate, expected performance question from
   whether the graph itself is *correct*, which this checks cheaply). *)
let print_path_counts_running_example () =
  pf "@[<v>== path counts for running_example, k=1..4 (paper: 4,17,73,314) ==@ ";
  List.iter
    (fun k ->
      let n =
        PQuad.count_paths ~offsets:Piecewise_linear_examples.running_example_offsets k
          Piecewise_linear_examples.running_example
      in
      pf "k=%d: %d paths@ " k n)
    [ 1; 2; 3; 4 ];
  pf "@]@."

let () =
  print_path_counts_running_example ();
  print_is_feasible_unit_tests ();
  print_empirical_box ();
  print_round_shape_lyapunov_check ();
  print_switched_round_shape_check ();
  print_switched_input_check ();
  print_round_shape_affine ();
  print_prop_driven ();
  print_liouville ();
  print_piecewise_lin ();
  ignore print_running_example_debug; ignore print_quad_template_raw_check;
  ignore print_affine_hand_check; ignore print_deg6_default_kappa_debug
