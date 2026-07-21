(* Smoke-test driver: builds every example system and exercises the parts of
   Seal.Dynsys that they touch (is_piecewise / is_linear / linear_to_poly),
   to validate the representation layer end-to-end on real system data. *)

module Sys = Seal.Dynsys.Float

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

let () =
  print_poly_examples ();
  print_linear_examples ();
  print_piecewise_examples ()
