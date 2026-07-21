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

  (* Linear systems analyses *)

  (** Ellipsoid invariant x'Px <= 1 with P - A'PA >= eps.eye, ignoring any
      input/disturbance (B is dropped even if present). *)
  val round: Dynsys.lin_t -> analysis_result_t

  (** Ellipsoid invariant x'Px <= 1, minimal contraction rate lambda such
      that A'PA <= lambda.P, ignoring any input/disturbance (B is dropped
      even if present). *)
  val shape: Dynsys.lin_t -> analysis_result_t

  (** Like [shape], but for x' = Ax + Bu systems, accounts for a bounded
      input u through the B part of the system (falls back to [shape] when
      the system has no input). *)
  val affine: Dynsys.lin_t -> analysis_result_t
    
  (* (\* Piecewise linear systems *\) *)
    
  (* val piecewise_lin: *)
  (*   int -> (\* k rank for the k-long paths computation *\) *)
  (*   Dynsys.lin_t -> *)
  (*   Dynsys.quad_guard_t guarded_analysis_result_t *)

  (* Polynomial systems *)
      
  (** Property-directed template synthesis: searches for a polynomial
      template P and scalar alpha such that P >= kappa everywhere, P is
      inductive along every mode (optionally assuming [domain_restriction]
      holds throughout, in addition to the guards), and P <= alpha on the
      init region -- so alpha bounds kappa over all reachable states. *)
  val prop_driven_sos_lyap:
    ?domain_restriction:Dynsys.basic_semialgebraic_t ->
    ?solver:Osdp.Sdp.solver -> (* default: osdp's own default solver *)
    Sos.polynomial_expr -> (* kappa: the property to prove, P(x) >= kappa(x) *)
    Dynsys.poly_t -> (* system analyzed *)
    int -> (* targeted degree of the template P *)
    analysis_result_t


  val liouville_method:
    ?solver:Osdp.Sdp.solver -> (* default: osdp's own default solver *)
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
  
module Make (Dynsys: Dynsys.S) : S with module Dynsys = Dynsys
and type Dynsys.poly_t = Dynsys.poly_t

