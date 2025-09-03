type status_t = Osdp.SdpRet.t

module type S = sig
  module Dynsys : Dynsys.S
  module Sos : Osdp.Sos.S
  (* type semialgebraic_t (\*: Dynsys.Poly.t list list*\) (\* disjunctive normal *)
  (* 						 form with zero *)
  (* 						 sublevel sets *\) *)

  type 'guard_t guarded_semialgebraic = 'guard_t * Dynsys.semialgebraic_t
    
  type 'guard_t guarded_analysis_result_t = {
    status: status_t;
    postfixpoint: 'guard_t guarded_semialgebraic list
  }
    
  type analysis_result_t = unit guarded_analysis_result_t 

  (** Printers *)
  val pp_result: Format.formatter -> analysis_result_t -> unit
  val pp_guarded_result: (Format.formatter -> 'guard_t -> unit) -> Format.formatter -> 'guard_t guarded_analysis_result_t -> unit

  (* (\* Linear systems analyses *\) *)
    
  (* val round: Dynsys.lin_t -> analysis_result_t *)
  (* val shape: Dynsys.lin_t -> analysis_result_t *)
  (* val affine: Dynsys.lin_t -> analysis_result_t *)
    
  (* (\* Piecewise linear systems *\) *)
    
  (* val piecewise_lin: *)
  (*   int -> (\* k rank for the k-long paths computation *\) *)
  (*   Dynsys.lin_t -> *)
  (*   Dynsys.quad_guard_t guarded_analysis_result_t *)

  (* Polynomial systems *)
      
 val prop_driven_sos_lyap:
    (Dynsys.poly_t -> Sos.polynomial_expr -> Dynsys.basic_semialgebraic_t) option
    -> (* the property that drives the search for the template *)
    Dynsys.poly_t -> (* system analyzed *)
    int -> (* targeted degree *)
    analysis_result_t


  val liouville_method:
    Dynsys.poly_t ->
    int ->
    analysis_result_t


  (** Narrowing with multiple templates *)

  (* Narrowing through min-policy iterations *)
  type quad_template_t = Dynsys.Mat.t 
  type poly_template_t = Dynsys.Poly.t
  type bound_t = Minf | Pinf | Fin of Dynsys.coeff
      
  val narrow_linsys:
    Dynsys.lin_t ->
    (quad_template_t * bound_t) array ->
    (quad_template_t * bound_t) array

  (* val narrow_piecewise_linsys: Dynsys.poly_t -> (poly_template_t *
     bound_t) array -> (poly_template_t * bound_t) array *)
      
  val narrow_sys: 
    Dynsys.poly_t ->
    (poly_template_t * bound_t) array ->
    (poly_template_t * bound_t) array      
end
  
module Make (_ : Dynsys.S) : S

