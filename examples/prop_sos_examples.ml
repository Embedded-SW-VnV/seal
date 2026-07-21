(* Systems for the property-directed SOS template search (Analysis.prop_driven_sos_lyap).

   Ported from /Users/ploc/Repositories/git/papers/2016-progcertos/script/examples/,
   which only define system data (gC/T/r/gT), not a kappa or an actual call
   to templatedesignprop -- kappa values are chosen at the call site
   (examples/run_examples.ml) to exercise the machinery and match each
   file's documented expectation, not transcribed from the source. *)

module Sys = Seal.Dynsys.Float
module Poly = Sys.Poly

let c = Sys.Coeff.of_float

(* cav10.m: "Sound compilation of reals" Fig. 9. Documented expectation:
   0 <= x <= 3. *)
let cav10 : Sys.poly_t =
  let x0 = Poly.(??0) in
  (* rif = x0^2 - x0 >= 0 (x0<=0 or x0>=1); relse = -rif >= 0 (0<=x0<=1) *)
  let rif = Poly.((x0 ** 2) - x0) in
  let relse = Poly.(x0 - (x0 ** 2)) in
  let t_if = Poly.(c 0.1 *. x0) in
  let t_else = Poly.((x0 ** 2) + !(c 2.)) in
  {
    Sys.df = 1;
    di = 0;
    map = [ ([ rif ], [| t_if |]); ([ relse ], [| t_else |]) ];
    init = [ Poly.(x0 * (!(c 10.) - x0)) ] (* 0 <= x0 <= 10 *);
    input = None;
    r_g = None (* not needed by prop_driven_sos_lyap *);
  }

(* perin.m: "Three linearization techniques for multivariate polynomials in
   static analysis using convex polyhedra", example 2. x2 tracks the
   product x0*x1 in the "if" mode, and is reset to 0 in the "else" mode. *)
let perin_x0, perin_x1, perin_x2 = Poly.(??0, ??1, ??2)

let perin : Sys.poly_t =
  let x0, x1, x2 = perin_x0, perin_x1, perin_x2 in
  let rif = Poly.(!(c 4.) - (x0 ** 2) - (x1 ** 2)) in
  let relse = Poly.((x0 ** 2) + (x1 ** 2) - !(c 4.)) in
  let t_if = [| x0; x1; Poly.(x1 * x0) |] in
  let t_else = [| x0; x1; Poly.zero |] in
  {
    Sys.df = 3;
    di = 0;
    map = [ ([ rif ], t_if); ([ relse ], t_else) ];
    init =
      [
        Poly.(x0 * (!(c 5.) - x0));
        Poly.(!(c 9.) - (x1 ** 2));
        Poly.(!(c 100.) - (x2 ** 2));
      ];
    input = None;
    r_g = None;
  }

(* Matches perin.m's gT: an assumed domain restriction (not itself proved
   here), passed as ?domain_restriction to prop_driven_sos_lyap. *)
let perin_domain_restriction : Sys.basic_semialgebraic_t =
  let x0, x1 = perin_x0, perin_x1 in
  [
    Poly.(x0 - !(c 1.));
    Poly.(x1 + !(c 2.));
    Poly.(x0 - x1);
    Poly.(!(c 5.) - x0 - x1);
  ]
