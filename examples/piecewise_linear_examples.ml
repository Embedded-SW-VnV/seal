(* Piecewise-linear (lin_t) discrete dynamical systems: x' = A_i x (+ B_i u)
   when x is in the region described by guard i.

   Ported from the Matlab PiecewiseLyapunov toolbox
   (.../PiecewiseLyapunov-version-journal/examples/*.m), whose [Contrainte]
   class represents a half-space [vector . x <= scalar] ([<] when strict).
   Two modeling choices had to be made to fit the current Seal.Dynsys.S API:

   - Matlab affine laws are asserted as [z' = M z] on a state [z] homogenized
     with a leading constant 1 (see Law.homogeneize); when an input appears,
     it is instead folded in as an extra, *frozen* state coordinate governed
     by an identity row (e.g. Example1Pierre's third row [0 0 1]), which
     amounts to treating the input as an unknown-but-time-invariant
     parameter rather than a true per-step disturbance. Seal's [di]/[input]
     mechanism natively models genuinely time-varying, per-step-resampled
     bounded inputs, which is the more standard (and stronger) robust
     reading, so that's what's used below instead of literally replaying the
     frozen-state encoding.
   - [quad_guard_t] and [ball_t] (used for [init]/[input]) can only represent
     ellipsoids/quadratic sublevel sets exactly, not general polytopes.
     Affine half-spaces (degree <= 1) embed into [quad_guard_t] exactly (see
     [affine_guard] below), so per-mode guards carry over faithfully. Boxes
     used for [init]/[input] regions, however, only carry over as an
     *inscribed ball approximation* -- a real representational gap when
     porting polytopic examples, worth keeping in mind. *)

module Sys = Seal.Dynsys.Float
module Mat = Sys.Mat

(* Coeff.t is abstract (that's what makes Dynsys generic in the scalar), so
   even here in the Float instance every numeric literal must go through
   Coeff.of_float rather than being used directly. *)
let c = Sys.Coeff.of_float
let carr = Array.map c
let crows = List.map (List.map c)

(* Encodes the half-space [a . x <= b] as p(x) = b - a.x, following the
   [p(x) >= 0] convention used throughout for guards/init/input (see how
   PropSOSTemplates.compute treats dynsys.init/guards as nonnegative
   multipliers). As a quadratic form (1,x)^T Q (1,x): Q_00 = b,
   Q_(0,i+1) = Q_(i+1,0) = -a_i / 2, everything else 0. Strict vs weak
   inequalities are not distinguished (Seal's semialgebraic sets are closed). *)
let affine_guard (a : Sys.coeff array) (b : Sys.coeff) : Mat.t =
  let n = Array.length a in
  let q = Array.make_matrix (n + 1) (n + 1) Sys.Coeff.zero in
  q.(0).(0) <- b;
  Array.iteri
    (fun i ai ->
      let v = Sys.Coeff.(div (neg ai) (of_int 2)) in
      q.(0).(i + 1) <- v;
      q.(i + 1).(0) <- v)
    a;
  Mat.of_array_array q

(* Mignone, invariance example 1: R^2 partitioned into its 4 quadrants, one
   linear law per quadrant (autonomous, no input). *)
let mignone_invariance_1 : Sys.lin_t =
  let g a b = affine_guard (carr a) (c b) in
  let quadrant_i = [ g [| -1.; 0. |] 0.; g [| 0.; -1. |] 0. ] in
  let quadrant_iv = [ g [| -1.; 0. |] 0.; g [| 0.; 1. |] 0. ] in
  let quadrant_iii = [ g [| 1.; 0. |] 0.; g [| 0.; 1. |] 0. ] in
  let quadrant_ii = [ g [| 1.; 0. |] 0.; g [| 0.; -1. |] 0. ] in
  let a1 = Mat.of_list_list (crows [ [ -0.04; -0.461 ]; [ -0.139; 0.341 ] ]) in
  let a2 = Mat.of_list_list (crows [ [ 0.936; 0.323 ]; [ 0.788; -0.049 ] ]) in
  let a3 = Mat.of_list_list (crows [ [ -0.857; 0.815 ]; [ 0.491; 0.62 ] ]) in
  let a4 = Mat.of_list_list (crows [ [ -0.022; 0.644 ]; [ 0.758; 0.271 ] ]) in
  {
    Sys.df = 2;
    di = 0;
    map = [ (quadrant_i, a1); (quadrant_iv, a2); (quadrant_iii, a3); (quadrant_ii, a4) ];
    (* Matlab's I = [0,1] x [0,1]; approximated here by its inscribed ball *)
    init = (carr [| 0.5; 0.5 |], c 0.5);
    input = None;
    (* placeholder domain-of-interest radius for Analysis.liouville_method
       (unused by round/shape/affine, which only read [map]) *)
    r_g = Some (c 1.5);
  }

(* Example1Pierre: single-mode, input-driven AR(2)-like law, with the input
   modeled as a genuine bounded, per-step input (see module comment above)
   rather than Matlab's frozen extra-state encoding. *)
let example1_pierre : Sys.lin_t =
  let update = Mat.of_list_list (crows [ [ 1.5; -0.7; 1.6 ]; [ 1.; 0.; 0. ] ]) in
  {
    Sys.df = 2;
    di = 1;
    map = [ ([], update) ];
    (* eps = 1e-8 box around the origin, approximated as a ball *)
    init = (carr [| 0.; 0. |], c 1e-8);
    (* u in [-1, 1] *)
    input = Some (carr [| 0. |], c 1.);
    (* matches Polynomial_examples.ex1 (Pierre1), the same underlying (A,B) *)
    r_g = Some (c 30.);
  }

(* The paper's "running example" (.../examples/runningexample.m): a 4-mode
   piecewise-*affine* system (each mode has a nonzero translation offset
   b_i, unlike every other example in this file) over (x,y) with a bounded
   input u in [-3,3], read fresh every loop iteration in the source
   pseudocode. Ported using Matlab's own encoding -- u folded in as an
   extra frozen state coordinate (row [0,0,1], u'=u), rather than the
   genuine per-step Dynsys.input treatment used for Example1Pierre above --
   because that's the only encoding Analysis.piecewise_lin (deliberately
   scoped to di=0, matching invariant.m itself) can run at all, and because
   reproducing the paper's own k-inductive result requires matching its own
   modeling choice, not a stronger one.

   Dynsys.lin_t has no way to represent a nonzero offset at all (see
   PiecewiseQuadraticTemplates's scope note), so the b_i are carried
   separately in [running_example_offsets], passed to
   [Analysis.piecewise_lin] via its [?offsets] parameter. Consequently:
   this system must NOT be run through round/shape/affine/liouville_method
   or cast via linear_to_poly/poly_to_linear -- all of those would silently
   drop the offset and analyze the wrong (through-the-origin) system. It's
   deliberately kept out of [examples] below for that reason. *)
let running_example : Sys.lin_t =
  let g a b = affine_guard (carr a) (c b) in
  let u_bounds = [ g [| 0.; 0.; 1. |] 3.; g [| 0.; 0.; -1. |] 3. ] in
  let guard1 = u_bounds @ [ g [| -9.; 7.; 6. |] 5.; g [| -4.; 8.; -8. |] 4. ] in
  let guard2 = u_bounds @ [ g [| -9.; 7.; 6. |] 5.; g [| 4.; -8.; 8. |] (-4.) ] in
  let guard3 = u_bounds @ [ g [| -4.; 8.; -8. |] 4.; g [| 9.; -7.; -6. |] (-5.) ] in
  let guard4 = u_bounds @ [ g [| 9.; -7.; -6. |] (-5.); g [| 4.; -8.; 8. |] (-4.) ] in
  let a1 = Mat.of_list_list (crows [ [ 0.4217; 0.1077; 0.5661 ]; [ 0.1162; 0.2785; 0.2235 ]; [ 0.; 0.; 1. ] ]) in
  let a2 = Mat.of_list_list (crows [ [ 0.4763; 0.0145; 0.9033 ]; [ 0.1315; 0.3291; 0.1459 ]; [ 0.; 0.; 1. ] ]) in
  let a3 = Mat.of_list_list (crows [ [ 0.2618; 0.1177; 0.0868 ]; [ 0.4014; 0.4161; 0.6320 ]; [ 0.; 0.; 1. ] ]) in
  let a4 = Mat.of_list_list (crows [ [ 0.3874; 0.0771; 0.5153 ]; [ 0.2430; 0.4028; 0.4790 ]; [ 0.; 0.; 1. ] ]) in
  {
    Sys.df = 3;
    di = 0;
    map = [ (guard1, a1); (guard2, a2); (guard3, a3); (guard4, a4) ];
    (* Matlab's I = [-9,9] x [-9,9] x [-3,3]; approximated by its largest
       axis-aligned inscribed ball (radius = tightest half-width, on u) *)
    init = (carr [| 0.; 0.; 0. |], c 3.);
    input = None;
    r_g = Some (c 13.); (* ~ sqrt(9^2+9^2+3^2), a loose outer bound *)
  }

let running_example_offsets : Sys.coeff array array =
  [| carr [| 0.; -1.; 0. |]; carr [| 0.; 9.; 0. |]; carr [| -4.; 4.; 0. |]; carr [| 10.; 7.; 0. |] |]

let examples : (string * Sys.lin_t) list =
  [ ("MignoneInvariance1", mignone_invariance_1); ("Example1Pierre", example1_pierre) ]
