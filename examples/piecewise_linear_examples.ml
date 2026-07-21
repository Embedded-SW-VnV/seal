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

let examples : (string * Sys.lin_t) list =
  [ ("MignoneInvariance1", mignone_invariance_1); ("Example1Pierre", example1_pierre) ]
