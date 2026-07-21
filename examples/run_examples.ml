(* Smoke-test driver: builds every example system and exercises the parts of
   Seal.Dynsys that they touch (is_piecewise / is_linear / linear_to_poly),
   to validate the representation layer end-to-end on real system data. *)

module Sys = Seal.Dynsys.Float
module Ana = Seal.Analysis.Make (Sys)

let pp_mode_count fmt map = Format.fprintf fmt "%d" (List.length map)

let print_poly_examples () =
  Format.printf "@[<v>== Polynomial systems (poly_t) ==@ ";
  List.iter
    (fun (name, (sys : Sys.poly_t)) ->
      Format.printf
        "%-12s df=%d di=%d modes=%a linear=%b piecewise=%b@ "
        name sys.df sys.di pp_mode_count sys.map
        (Sys.is_linear sys) (Sys.is_piecewise sys))
    Polynomial_examples.examples;
  Format.printf "@]@."

let print_linear_examples () =
  Format.printf "@[<v>== Linear systems (lin_t, single mode) ==@ ";
  List.iter
    (fun (name, (sys : Sys.lin_t)) ->
      let poly_sys = Sys.linear_to_poly sys in
      Format.printf
        "%-16s df=%d di=%d modes=%a piecewise=%b (cast to poly_t: linear=%b)@ "
        name sys.df sys.di pp_mode_count sys.map
        (Sys.is_piecewise sys) (Sys.is_linear poly_sys))
    Linear_examples.examples;
  Format.printf "@]@."

let print_piecewise_examples () =
  Format.printf "@[<v>== Piecewise-linear systems (lin_t, multi-mode) ==@ ";
  List.iter
    (fun (name, (sys : Sys.lin_t)) ->
      let poly_sys = Sys.linear_to_poly sys in
      Format.printf
        "%-16s df=%d di=%d modes=%a piecewise=%b (cast to poly_t: linear=%b)@ "
        name sys.df sys.di pp_mode_count sys.map
        (Sys.is_piecewise sys) (Sys.is_linear poly_sys);
      (* Print the first mode's guard/update once cast to polynomials, as a
         concrete check that MatrixPolynomialCast round-trips correctly. *)
      match poly_sys.map with
      | (guard, update) :: _ ->
          Format.printf "  mode 0 guard:  @[<hov>%a@]@ "
            (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt " /\\ ")
               (fun fmt p -> Format.fprintf fmt "%a >= 0" Sys.Poly.pp p))
            guard;
          Format.printf "  mode 0 update: @[<hov>%a@]@ "
            (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
               Sys.Poly.pp)
            (Array.to_list update)
      | [] -> ())
    Piecewise_linear_examples.examples;
  Format.printf "@]@."

(* round/shape/affine only handle a single, unconditional mode (they raise
   on genuinely piecewise systems), so this deliberately excludes
   MignoneInvariance1 (4 modes) and only covers pure linear systems: the
   lin_t examples, Example1Pierre (single mode, has an input), and the
   linear poly_t examples cast down via Dynsys.poly_to_linear. *)
let quadratic_template_examples : (string * Sys.lin_t) list =
  Linear_examples.examples
  @ [ ("Example1Pierre", Piecewise_linear_examples.example1_pierre) ]
  @ [
      ("Pierre1 (poly->lin)", Sys.poly_to_linear Polynomial_examples.ex1);
      ("Identity (poly->lin)", Sys.poly_to_linear Polynomial_examples.ex_id);
    ]

let run_and_print label f sys =
  Format.printf "  [%s] " label;
  match f sys with
  | result -> Format.printf "%a@ " Ana.pp_result result
  | exception e -> Format.printf "ERROR: %s@ " (Printexc.to_string e)

let run_quadratic_templates () =
  Format.printf "@[<v>== Quadratic templates (round / shape / affine) ==@ ";
  List.iter
    (fun (name, (sys : Sys.lin_t)) ->
      Format.printf "* %s (df=%d di=%d)@ " name sys.df sys.di;
      run_and_print "round" Ana.round sys;
      run_and_print "shape" Ana.shape sys;
      run_and_print "affine" Ana.affine sys)
    quadratic_template_examples;
  Format.printf "@]@."

(* kappa is an Ana.Sos.polynomial_expr, built with Sos's own (??)/(~-)
   operators rather than a Sys.Poly.t wrapped in Sos.Const: analysis.mli
   keeps Sos abstract (no sharing constraint tying Sos.Poly to Dynsys.Poly),
   so a Poly.t value built outside Analysis isn't known, from a caller's
   point of view, to be usable as an Ana.Sos.Poly.t. *)
let run_prop_sos_examples () =
  Format.printf "@[<v>== Property-directed SOS templates (prop_driven_sos_lyap) ==@ ";
  (* cav10 needs deg=4 to dominate its cubic "else" update (deg=2 comes
     back Unknown: too weak a template to be inductive). perin, conversely,
     needs deg=2: at deg=4 its per-mode multipliers reach degree 6 in 3
     variables, a large enough SOS block that csdp's Cholesky
     factorization fails ("Factorization of the system matrix failed")
     regardless of alpha or padding/scaling -- confirmed by hand this is
     not a tightness issue like the one search_alpha works around, csdp
     just cannot reliably factor a problem this large; deg=2 keeps the
     multipliers small enough to solve cleanly. *)
  let cav10_deg = 4 and perin_deg = 2 in
  Format.printf "* cav10 (df=1 di=0), deg=%d@ " cav10_deg;
  run_and_print "kappa=x0 (expect alpha ~ 3)"
    (fun sys -> Ana.prop_driven_sos_lyap Ana.Sos.(??0) sys cav10_deg)
    Prop_sos_examples.cav10;
  run_and_print "kappa=-x0 (expect alpha ~ 0)"
    (fun sys -> Ana.prop_driven_sos_lyap Ana.Sos.(~- ??0) sys cav10_deg)
    Prop_sos_examples.cav10;
  Format.printf "* perin (df=3 di=0), deg=%d@ " perin_deg;
  run_and_print "kappa=x2, no domain_restriction"
    (fun sys -> Ana.prop_driven_sos_lyap Ana.Sos.(??2) sys perin_deg)
    Prop_sos_examples.perin;
  run_and_print "kappa=x2, domain_restriction=gT"
    (fun sys ->
      Ana.prop_driven_sos_lyap
        ~domain_restriction:Prop_sos_examples.perin_domain_restriction
        Ana.Sos.(??2) sys perin_deg)
    Prop_sos_examples.perin;
  Format.printf "@]@."

(* piecewise_lin works directly on lin_t (no poly_t cast needed) but
   requires di=0 (see PiecewiseQuadraticTemplates's scope note) and affine
   guards, which only MignoneInvariance1 among lin_t examples satisfies
   (Example1Pierre has di=1, and every Linear_examples system has an
   input too). *)
let run_piecewise_lin () =
  Format.printf "@[<v>== k-inductive piecewise-quadratic invariant (piecewise_lin) ==@ ";
  let pp_guard fmt (g : Sys.quad_guard_t) = Format.fprintf fmt "%d guard rows" (List.length g) in
  List.iter
    (fun k ->
      Format.printf "* MignoneInvariance1, k=%d@ " k;
      (* k=2 is known to sometimes come back Unknown here: csdp's
         Cholesky factorization can fail right at the tail of convergence
         on the larger (more paths, more multiplier variables) k=2
         problem -- confirmed by hand primal/dual objectives were both
         already ~2.914 (essentially converged) when it happened, so this
         is the same class of solver-capacity limit seen with
         PropSOSTemplates.template, not a logic bug. k=1 (one path per
         cell, the same granularity as round/shape/affine) is reliable. *)
      match Ana.piecewise_lin k Piecewise_linear_examples.mignone_invariance_1 with
      | result -> Format.printf "%a@ " (Ana.pp_guarded_result pp_guard) result
      | exception e -> Format.printf "ERROR: %s@ " (Printexc.to_string e))
    [ 1; 2 ];
  (* The paper's own "running example" (see the module comment on
     Piecewise_linear_examples.running_example): a larger, less
     well-scaled problem (4 guard rows per mode instead of 2, offsets up
     to 10, domain up to 9) than MignoneInvariance1. Known limitation,
     left as-is for now rather than chased further: even k=1 comes back
     Unknown here -- verbose csdp output showed pobj/dobj both ~3050
     after 80 iterations (clearly converging) when "Factorization of the
     system matrix failed" hit, the same class of near-boundary
     solver-capacity issue seen elsewhere, just worse on this bigger
     problem. Reproducing the paper's own k=4/314-paths/beta~1574 result
     isn't reachable with the current csdp-based, non-bisected solve.
     Kept here so the gap stays visible rather than silently unexercised. *)
  Format.printf "* RunningExample (paper's example, df=3 di=0 via frozen u), k=1@ ";
  (match
     Ana.piecewise_lin ~offsets:Piecewise_linear_examples.running_example_offsets 1
       Piecewise_linear_examples.running_example
   with
  | result -> Format.printf "%a@ " (Ana.pp_guarded_result pp_guard) result
  | exception e -> Format.printf "ERROR: %s@ " (Printexc.to_string e));
  Format.printf "@]@."

(* Every poly_t example, whether authored directly as one (Polynomial_examples,
   including its nonlinear/genuinely-polynomial systems) or cast down from a
   lin_t via Sys.linear_to_poly (Linear_examples: single-mode; Piecewise_linear_examples:
   includes MignoneInvariance1, a genuinely piecewise -- 4-mode -- polynomial
   system once cast, unlike everything in Polynomial_examples which is
   single-mode). Both liouville_method and prop_driven_sos_lyap operate on
   poly_t and are agnostic to how many modes it has, so this is also the
   first time either gets exercised on a real multi-mode system. *)
let reachability_examples : (string * Sys.poly_t) list =
  Polynomial_examples.examples
  @ List.map (fun (name, sys) -> name, Sys.linear_to_poly sys) Linear_examples.examples
  @ List.map
      (fun (name, sys) -> name, Sys.linear_to_poly sys)
      Piecewise_linear_examples.examples

(* liouville_method needs dynsys.r_g populated (a bound on the state ball
   used to shrink/unshrink the SOS problem) -- every system above sets it
   (Polynomial_examples natively; Linear_examples/Piecewise_linear_examples
   carry a placeholder domain-of-interest radius added for this purpose,
   since round/shape/affine never read it). *)

(* Degree 2 (a quadratic template) is used uniformly below to keep this
   smoke test's total solve count manageable across ~14 systems x up to 5
   variables each: it's enough for the linear/piecewise-linear systems
   (cast down to poly_t, so genuinely linear updates) to fully succeed, and
   still exercises the machinery meaningfully on the nonlinear
   Polynomial_examples systems even where a higher degree would be needed
   for a tight/successful bound -- a mixed bag of Success/PartialSuccess/
   infeasible results here is expected, not a bug. *)
let reachability_deg = 2

let run_reachability_and_bounds () =
  Format.printf "@[<v>== Reachability invariant (liouville_method) and per-variable bounds (prop_driven_sos_lyap) ==@ ";
  List.iter
    (fun (name, (sys : Sys.poly_t)) ->
      Format.printf "* %s (df=%d di=%d modes=%a)@ " name sys.df sys.di pp_mode_count sys.map;
      run_and_print "invariant (liouville)"
        (fun s -> Ana.liouville_method s reachability_deg) sys;
      for i = 0 to sys.df - 1 do
        run_and_print (Printf.sprintf "x%d <= ? (kappa=x%d)" i i)
          (fun s -> Ana.prop_driven_sos_lyap Ana.Sos.(?? i) s reachability_deg) sys;
        run_and_print (Printf.sprintf "x%d >= ? (kappa=-x%d)" i i)
          (fun s -> Ana.prop_driven_sos_lyap Ana.Sos.(~- (?? i)) s reachability_deg) sys
      done)
    reachability_examples;
  Format.printf "@]@."

let () =
  print_poly_examples ();
  print_linear_examples ();
  print_piecewise_examples ();
  run_quadratic_templates ();
  run_piecewise_lin ();
  run_prop_sos_examples ();
  run_reachability_and_bounds ()
