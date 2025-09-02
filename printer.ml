(* Naive print to check verification with Frama-C *)
open Format
open Dynsys.Float

let state_vars dynsys =
  List.init dynsys.df (fun idx -> "x" ^ string_of_int idx)

(*
Example:
typedef struct { double x0, x1, x2; } state; 
*)
let pp_typedef fmt dynsys =
  fprintf fmt
    "@[typedef struct { double @[<hov 0>%a; } state; @]"
    (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ", ") pp_print_string)
    (state_vars dynsys)  

(* Print polynomial while "unfolding" powers to support ACSL syntax *)
let pp_poly pp_name (* dynsys *) fmt poly =
  let pp_monomial fmt monomial =
    let powers = Osdp.Monomial.to_list monomial in
    let _, l =
      List.fold_left
        (fun (i,l) pow_i -> i+1, if pow_i > 0 then (List.init pow_i (fun _ -> i))@l else l )
        (0,[])
        powers
    in
    match l with
    | [] -> fprintf fmt "1"
    | _ -> 
       pp_print_list
         ~pp_sep:(fun fmt () -> fprintf fmt " * ")
         pp_name
         fmt
         (List.rev l)
  in
  pp_print_list
    ~pp_sep:(fun fmt () -> fprintf fmt " +@ ")
    (fun fmt (monomial, coeff) ->
      if Poly.Coeff.compare coeff Poly.Coeff.one = 0 then
        fprintf fmt "%a" pp_monomial monomial
      else if Osdp.Monomial.compare monomial Osdp.Monomial.one = 0 then
        fprintf fmt "%a" Poly.Coeff.pp coeff
      else
        fprintf fmt "%a * %a" Poly.Coeff.pp coeff pp_monomial monomial)
    fmt
    (Poly.to_list poly)
    
  

let pp_lhs dynsys fmt idx =
  if idx < dynsys.df then
    fprintf fmt "x%i" idx
  else
    fprintf fmt "in%i" (idx - dynsys.df)

let pp_rhs dynsys fmt idx =
  if idx < dynsys.df then
    fprintf fmt "pre_x%i" idx
  else
    fprintf fmt "in%i" (idx - dynsys.df)

(* Prints the list , in0, in1, ..., inn *)
let pp_input_list ?(prefix=" ") pp_lhs dynsys fmt =
  let nb = dynsys.di in
  pp_print_list
    ~pp_sep:(fun fmt () -> fprintf fmt " ")
    (fun fmt idx -> fprintf fmt ",%s%a" prefix pp_lhs (idx+dynsys.df))
    fmt
    (List.init nb (fun x -> x))

 (*
Example:
/*@ predicate inv(state *s) = 6.04 * s->x0 * s->x0 - 9.65 * s->x0 * s->x1
  @   - 2.26 * s->x0 * s->x2 + 11.36 * s->x1 * s->x1
  @   + 2.67 * s->x1 * s->x2 + 3.76 * s->x2 * s->x2 <= 1; */
 *)
let pp_poly_predicate dynsys fmt (idx, prop) =
  let name = prop.Properties.name in
  let poly = prop.poly in
  let pp_lhs = pp_lhs dynsys in
  
  let pp_name fmt idx = fprintf fmt "s.x%i" idx in
  fprintf fmt
    "@[/*@@ @[<hov 2>// Polynomial predicate of property %s@ predicate poly_%s_%i(state s%t, real lambda) = %a <= lambda;@] */@]@ "
    name
    name
    idx
    (fun fmt ->
      if not prop.state_only && dynsys.di > 0 then
        fprintf fmt "%t" (pp_input_list pp_lhs dynsys) 
      else
        ()
    )
    (pp_poly pp_name) poly
 

(*
Example:
/*@ requires \valid(s) && inv(s) && -1 <= in0 <= 1;
  @ ensures inv(s); */
void step(state *s, double in0) {
  double pre_x0 = s->x0, pre_x1 = s->x1, pre_x2 = s->x2;

  s->x0 = 0.9379 * pre_x0 - 0.0381 * pre_x1 - 0.0414 * pre_x2 + 0.0237 * in0;
  s->x1 = -0.0404 * pre_x0 + 0.968 * pre_x1 - 0.0179 * pre_x2 + 0.0143 * in0;
  s->x2 = 0.0142 * pre_x0 - 0.0197 * pre_x1 + 0.9823 * pre_x2 + 0.0077 * in0;
}
 *)
                  
let pp_behavior_invariants dynsys pp_cons fmt (idx, prop) =
  let id = prop.Properties.name in
  let assumes = prop.assumes in
  let pp_lhs = pp_lhs dynsys in
  fprintf fmt "@@ @[<v 2>behavior %s_inv_%i:@ " id idx;
  let _ = 
    match assumes with
    | None -> ()
    | Some cons -> pp_cons dynsys.df (fun pp fmt x -> fprintf fmt "@@ @[<hov 2>assumes %a >= 0.;@]@ " pp x) pp_lhs fmt cons
  in
  let pp_inputs fmt =
    if not prop.state_only && dynsys.di > 0 then
      fprintf fmt "%t" (pp_input_list pp_lhs dynsys) 
    else
      ()
  in  (* needs a 0 for polynomials, and a 1 or any constant for ellipsoids. TODO find a solution *)
  fprintf fmt "@@ assumes poly_%s_%i(*s%t,0.1);@ " id idx pp_inputs;
  fprintf fmt "@@ ensures poly_%s_%i(*s%t,0.1);@ " id idx pp_inputs;
  fprintf fmt "@]@ "

let pp_behavior_stability dynsys pp_cons fmt (idx, prop) =
  let id = prop.Properties.name in
  let assumes = prop.assumes in
  let pp_lhs = pp_lhs dynsys in
  fprintf fmt "@@ @[<v 2>behavior %s_stability_%i:@ " id idx;
  let _ = 
    match assumes with
    | None -> ()
    | Some cons -> pp_cons dynsys.df (fun pp fmt x -> fprintf fmt "@@ @[<hov 2>assumes %a >= 0.;@]@ " pp x) pp_lhs fmt cons
  in
  let pp_inputs fmt =
    if not prop.state_only && dynsys.di > 0 then
      fprintf fmt "%t" (pp_input_list pp_lhs dynsys) 
    else
      ()
  in  
  fprintf fmt "@@ ensures \\forall real lambda;  lambda > 1e-2 && lambda < 1e1000 ==> poly_%s_%i(\\old(*s)%t, lambda) ==> poly_%s_%i(*s%t, lambda);" id idx pp_inputs id idx pp_inputs;
  ;
  fprintf fmt "@]@ "

let pp_behavior dynsys pp_cons fmt (idx, prop) =
  match prop.Properties.kind with
  | Invariant -> pp_behavior_invariants dynsys pp_cons fmt (idx,prop)
  | Stability -> pp_behavior_stability dynsys pp_cons fmt (idx,prop)
          
let pp_contract pp_cons fmt (dynsys, props) =
  let pp_lhs = pp_lhs dynsys in 
  fprintf fmt "@[<v 2>/*";
  fprintf fmt "@@ @[<hov 2>requires \\valid(s);@]@ ";
  (* fprintf fmt "@@ @[<hov 2>requires \\valid(s) && inv(s);@]@ "; *)
  let _ = 
    match dynsys.input with
      None -> ()
    | Some cons ->
       (*fprintf fmt "@@ @[<hov 2>requires -1 <= in0 <= 1;@]@ ";*)
       pp_cons dynsys.df (fun pp fmt x -> fprintf fmt "@@ @[<hov 2>requires %a >= 0.;@]@ " pp x) pp_lhs fmt cons
  in
  pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "@ ") (pp_behavior dynsys pp_cons) fmt props;
  (* pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "@ ") (pp_behavior_invariants dynsys pp_cons) fmt props;
   * pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "@ ") (pp_behavior_stability dynsys pp_cons) fmt props; *)
  fprintf fmt "@]@ */@ ";
  (* fprintf fmt "@@ @[<hov 2>ensures inv(s);@ */@]@]@ " *)
  ()

  
  
let pp_step pp_guard pp_update pp_cons fmt (dynsys, props) =
  let pp_lhs = pp_lhs dynsys in
  let pp_rhs = pp_rhs dynsys in
  let pp_input_list = pp_input_list ~prefix:" double " pp_lhs dynsys in
  fprintf fmt "@[<v 0>";
  pp_contract pp_cons fmt (dynsys, props);
  fprintf fmt "@[<v 2>void step(state *s%t) {@ " pp_input_list  ;
  List.iter (fun x -> fprintf fmt "double pre_%s = s->%s;@ " x x) (state_vars dynsys);
  fprintf fmt "@ ";
  let _ =
    match dynsys.map with
    | [[], single_update] -> pp_update pp_lhs pp_rhs fmt single_update
    | _ ->
       let nb_cases = List.length dynsys.map in
       List.iteri (fun ith_case (guard, update) ->
           if ith_case > 0 then
             fprintf fmt "else ";
           if ith_case < nb_cases -1 then
             fprintf fmt "if (%a) " pp_guard guard;
           fprintf fmt "{ %a }" (pp_update pp_lhs pp_rhs) update
         ) dynsys.map
  in
  fprintf fmt "@]@ }@]@ ";
  fprintf fmt "@.@?"
  


let pp pp_guard pp_up
      (pp_cons(* : int -> ((Format.formatter -> Poly.t -> unit) ->
          *  Format.formatter -> Poly.t -> unit) ->
          * (Format.formatter -> int -> unit) ->
          * Format.formatter ->
          * Poly.Coeff.t array * Poly.Coeff.t -> unit *)) fmt (dynsys, props) =
  let props = List.mapi (fun idx x -> idx, x) props in
  fprintf fmt "@[<v 0>";
  pp_typedef fmt dynsys;
  fprintf fmt "@.@.";
  List.iter (pp_poly_predicate dynsys fmt) (* dynsys *) props;   
  fprintf fmt "@.@.";
  pp_step pp_guard pp_up pp_cons fmt (dynsys, props);
  fprintf fmt "@]"
  
