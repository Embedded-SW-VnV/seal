(* Polynomial (poly_t) discrete dynamical systems.

   Ported from measuressos/code/ocaml/examples.ml, adapted to the current
   Seal.Dynsys.S API:
   - the old record had [name], [init: coeff array], [r_g0], [r_gi], [r_g]
     (all floats); the current [poly_t] record has [init]/[input] as
     semialgebraic sets (conjunctions of [p_i(x) >= 0]) and [r_g] as an
     optional bound.
   - balls are rebuilt with [Cast.ball_to_semialg], which encodes
     "x within the ball of given center/radius" as [radius^2 - ||x-c||^2 >= 0],
     consistent with the [p_i(x) >= 0] convention used everywhere for guards
     and init/input regions (see how PropSOSTemplates.compute consumes
     [dynsys.init] as SOS multipliers on nonnegative constraints).
   - [Coeff.t] is kept abstract by [Dynsys.S] (on purpose: it's what makes the
     whole library generic in the scalar), so even in this [Float] instance
     raw float literals aren't [Coeff.t] values and must go through [c]
     below. *)

module Sys = Seal.Dynsys.Float
module Poly = Sys.Poly
module Cast = Sys.Cast

(* float -> Coeff.t, needed everywhere since Coeff.t is abstract *)
let c = Sys.Coeff.of_float
let carr = Array.map c

(* A single, unconditional mode: the guard (empty conjunction) is always true *)
let single_mode f : (Sys.poly_guard_t * Sys.poly_update_t) list = [ ([], f) ]

(* Henrion1 *)
let h1 : Sys.poly_t =
  let x0, x1 = Poly.(??0, ??1) in
  let f1 = Poly.(c 0.5 *. (x0 + (c 2. *. x0 * x1))) in
  let f2 = Poly.(c 0.5 *. (x1 - (c 2. *. (x0 ** 3)))) in
  {
    Sys.df = 2;
    di = 0;
    map = single_mode [| f1; f2 |];
    init = Cast.ball_to_semialg 0 (carr [| 0.5; 0.5 |], c 0.25);
    input = None;
    r_g = Some (c 1.);
  }

(* Pierre1: 2nd order AR system driven by a bounded input *)
let ex1 : Sys.poly_t =
  let x0, x1, x2 = Poly.(??0, ??1, ??2) in
  let f1 = Poly.((c 1.5 *. x0) - (c 0.7 *. x1) + (c 1.6 *. x2)) in
  let f2 = x0 in
  {
    Sys.df = 2;
    di = 1;
    map = single_mode [| f1; f2 |];
    init = Cast.ball_to_semialg 0 (carr [| 0.; 0. |], c 0.0001);
    input = Some (Cast.ball_to_semialg 2 (carr [| 0. |], c 1.));
    r_g = Some (c 30.);
  }

(* Thao Dang RCJournal12, 8.3: FitzHugh-Nagumo neuron model,
   Euler time discretization with step size 0.2 *)
let ex_thao8_3 : Sys.poly_t =
  let x0, x1 = Poly.(??0, ??1) in
  let h = c 0.2 in
  let f1 = Poly.(x0 + (h *. (x0 - (x0 ** 3) - x1 + !(c 0.875)))) in
  let f2 = Poly.(x1 + (h *. !(c 0.08) * (x0 + !(c 0.7) - (c 0.8 *. x1)))) in
  {
    Sys.df = 2;
    di = 0;
    map = single_mode [| f1; f2 |];
    init = Cast.ball_to_semialg 0 (carr [| 1.; 2.5 |], c 0.1);
    input = None;
    r_g = Some (c 3.);
  }

(* Cathala system *)
let ex_cathala : Sys.poly_t =
  let x0, x1 = Poly.(??0, ??1) in
  let f1 = Poly.(x0 + x1) in
  let f2 = Poly.(!(c (-0.5952)) + (x0 * x0) + x1) in
  {
    Sys.df = 2;
    di = 0;
    map = single_mode [| f1; f2 |];
    init = Cast.ball_to_semialg 0 (carr [| 0.; 0. |], c 1.);
    input = None;
    r_g = Some (c 1.6);
  }

(* Julia map (quadratic complex iteration z -> z^2 + c, c = -0.0986 - 0.65186i) *)
let ex_julia1 : Sys.poly_t =
  let x0, x1 = Poly.(??0, ??1) in
  let c1, c2 = c (-0.0986), c (-0.65186) in
  let f1 = Poly.((x0 * x0) - (x1 * x1) + !c1) in
  let f2 = Poly.((c 2. *. x0 * x1) + !c2) in
  {
    Sys.df = 2;
    di = 0;
    map = single_mode [| f1; f2 |];
    init = Cast.ball_to_semialg 0 (carr [| 0.; 0. |], c 0.5);
    input = None;
    r_g = Some (c 1.5);
  }

(* Trivial 1-dim contraction, useful as a minimal sanity check *)
let ex_id : Sys.poly_t =
  let x0 = Poly.(??0) in
  let f1 = Poly.(c 0.9999 *. x0) in
  {
    Sys.df = 1;
    di = 0;
    map = single_mode [| f1 |];
    init = Cast.ball_to_semialg 0 (carr [| 0. |], c 1.);
    input = None;
    r_g = Some (c 2.);
  }

let examples : (string * Sys.poly_t) list =
  [
    ("Henrion1", h1);
    ("Pierre1", ex1);
    ("Thao8.3", ex_thao8_3);
    ("Cathala", ex_cathala);
    ("Julia1", ex_julia1);
    ("Identity", ex_id);
  ]
