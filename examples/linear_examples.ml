(* Linear (lin_t), single-mode discrete dynamical systems x' = A x + B u.

   Ported from seal/trunk/examples/lin.ml (matrix data taken from the Osdp
   test suite). That file never got finished (it ends mid-way through a call
   to a [Seal.System.build] API that doesn't exist in the current codebase),
   so only the numeric (A, B) pairs are salvaged here; everything else
   (init/input balls, r_g) is new, since the source specified none.

   These systems have a single, unconditional mode (guard = [] = always
   true) so they exercise [lin_t] without piecewise switching; see
   piecewise_linear_examples.ml for guarded, multi-mode systems. *)

module Sys = Seal.Dynsys.Float
module Mat = Sys.Mat

(* Coeff.t is abstract (that's what makes Dynsys generic in the scalar), so
   even here in the Float instance every numeric literal must go through
   Coeff.of_int/of_float rather than being used directly. *)
let ratio p q = Sys.Coeff.div (Sys.Coeff.of_int p) (Sys.Coeff.of_int q)
let c = Sys.Coeff.of_float

(* One mode, unconditionally active, updating with the combined [A|B] matrix *)
let single_mode a_rows b_rows : Sys.lin_t =
  let df = List.length a_rows in
  let di = List.length (List.hd b_rows) in
  let combined = List.map2 ( @ ) a_rows b_rows in
  {
    Sys.df;
    di;
    map = [ ([], Mat.of_list_list combined) ];
    (* placeholders: the source data did not specify init/input regions *)
    init = (Array.make df (c 0.), c 0.1);
    input = Some (Array.make di (c 0.), c 1.);
    r_g = None;
  }

let a_1 = [ [ ratio 15 10; ratio (-7) 10 ]; [ ratio 1 1; ratio 0 1 ] ]
let b_1 = [ [ ratio 16 10 ]; [ ratio 0 10 ] ]

let a_2 =
  [
    [ ratio 15 10; ratio (-7) 10; ratio (-7) 10; ratio 4 10 ];
    [ ratio 1 1; ratio 0 1; ratio 0 1; ratio 0 1 ];
    [ ratio 0 1; ratio 0 1; ratio 0 1; ratio 0 1 ];
    [ ratio 0 1; ratio 0 1; ratio 1 1; ratio 0 1 ];
  ]

let b_2 = [ [ ratio 5 10 ]; [ ratio 0 1 ]; [ ratio 1 1 ]; [ ratio 0 1 ] ]
let a_3 = [ [ ratio 499 1000; ratio (-5) 100 ]; [ ratio 1 100; ratio 1 1 ] ]
let b_3 = [ [ ratio 1 1 ]; [ ratio 0 1 ] ]

let a_4 =
  [
    [ ratio 9379 10000; ratio (-381) 10000; ratio (-414) 10000 ];
    [ ratio (-404) 10000; ratio 968 1000; ratio (-179) 10000 ];
    [ ratio (-142) 10000; ratio (-197) 10000; ratio 9823 10000 ];
  ]

let b_4 = [ [ ratio 237 10000 ]; [ ratio 143 10000 ]; [ ratio 77 10000 ] ]

let a_5 =
  [
    [ ratio 6227 10000; ratio 3871 10000; ratio (-113) 1000; ratio 102 10000 ];
    [
      ratio (-3407) 10000;
      ratio 9103 10000;
      ratio (-3388) 10000;
      ratio 649 10000;
    ];
    [ ratio 918 10000; ratio (-265) 10000; ratio (-7319) 10000; ratio 2669 10000 ];
    [
      ratio 2643 10000;
      ratio (-1298) 10000;
      ratio (-9903) 10000;
      ratio 3331 10000;
    ];
  ]

let b_5 =
  [
    [ ratio 3064 10000; ratio 1826 10000 ];
    [ ratio (-54) 10000; ratio 6731 10000 ];
    [ ratio 494 10000; ratio 16138 10000 ];
    [ ratio (-531) 10000; ratio 4012 10000 ];
  ]

let a_6 =
  [
    [ ratio 4250 10000; ratio 0 1; ratio 0 1; ratio 0 1; ratio 0 1 ];
    [
      ratio 3167 10000;
      ratio 1016 10000;
      ratio (-4444) 10000;
      ratio 0 1;
      ratio 0 1;
    ];
    [
      ratio 1278 10000;
      ratio 4444 10000;
      ratio 8207 10000;
      ratio 0 1;
      ratio 0 1;
    ];
    [
      ratio 365 10000;
      ratio 1270 10000;
      ratio 5202 10000;
      ratio 4163 10000;
      ratio (-5714) 10000;
    ];
    [
      ratio 147 10000;
      ratio 512 10000;
      ratio 2099 10000;
      ratio 5714 10000;
      ratio 7694 10000;
    ];
  ]

let b_6 =
  [
    [ ratio 8131 10000 ];
    [ ratio 1807 10000 ];
    [ ratio 729 10000 ];
    [ ratio 208 10000 ];
    [ ratio 84 10000 ];
  ]

let sys_1 = single_mode a_1 b_1
let sys_2 = single_mode a_2 b_2
let sys_3 = single_mode a_3 b_3
let sys_4 = single_mode a_4 b_4
let sys_5 = single_mode a_5 b_5
let sys_6 = single_mode a_6 b_6

let examples : (string * Sys.lin_t) list =
  [
    ("osdp_2x2_a", sys_1);
    ("osdp_4x4_a", sys_2);
    ("osdp_2x2_b", sys_3);
    ("osdp_3x3", sys_4);
    ("osdp_4x4_b_2in", sys_5);
    ("osdp_5x5", sys_6);
  ]
