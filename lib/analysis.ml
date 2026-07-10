type status_t = Osdp.SdpRet.t

module type S = sig
  module Dynsys : Dynsys.S
  module Sos : Osdp.Sos.S

  type 'guard_t guarded_semialgebraic = 'guard_t * Dynsys.semialgebraic_t
    
  type 'guard_t guarded_analysis_result_t = {
    status: status_t;
    postfixpoint: 'guard_t guarded_semialgebraic list
  }
    
  type analysis_result_t = unit guarded_analysis_result_t 

  (** Printers *)
  val pp_result: Format.formatter -> analysis_result_t -> unit
  val pp_guarded_result: (Format.formatter -> 'guard_t -> unit) -> Format.formatter -> 'guard_t guarded_analysis_result_t -> unit
    
  (** Template synthesis: postfixpoint computation *)

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
    int -> (* targeted degree *)
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

  
module Make (Dynsys: Dynsys.S) : (S with module Dynsys = Dynsys) = struct
    module Dynsys = Dynsys
    module Poly = Dynsys.Poly
    module Mat = Dynsys.Mat
    module Sos = Osdp.Sos.Make (Dynsys.Poly)

    (* module Cast = Dynsys.Cast (\*MatrixPolynomialCast.Make (Mat) (Poly) *\) *)

    type basic_semialgebraic = Poly.t list (* conjunction of zero sublevel sets *)

    type semialgebraic = basic_semialgebraic list (* disjunctive normal form
						     with zero sublevel sets *)
    type 'guard_t guarded_semialgebraic = 'guard_t * semialgebraic
    
    type 'guard_t guarded_analysis_result_t = {
      status: status_t;
      postfixpoint: 'guard_t guarded_semialgebraic list
    }
    
    type analysis_result_t = unit guarded_analysis_result_t 

    (* Printers *)
    let pp_basic_semialg fmt bsa =
      Format.fprintf fmt "(@[<v>%a@ @])"
	(Utils.pp_list ~sep:" /\\@ "
	   (fun fmt p -> Format.fprintf fmt "%a <= 0" Poly.pp p))
	bsa
	
    let pp_semialg fmt sa =
      Format.fprintf fmt "(@[<v>%a@ @])"
      (Utils.pp_list ~sep:" \\/@ " pp_basic_semialg) sa

    let pp_guarded_result pp_guard fmt res =
      Format.fprintf fmt "@[<v>status: %a@ invariant: @[<v>%a@]@]"
	Osdp.SdpRet.pp res.status
	(Utils.pp_list ~sep:"@ "
	   (fun fmt (g, sa) ->
	     Format.fprintf fmt "%a -> %a <= 0"
	       pp_guard g
	       pp_semialg sa 
	   ))
	res.postfixpoint
	
    let pp_result fmt res = pp_guarded_result (fun _fmt _ -> ()) fmt res

    (* (\* Linear systems analyses *\) *)
    (* module QuadTemplates = QuadraticTemplates.Make(Dynsys) *)
      
  (*   let build_result conv (status, result_opt) = *)
  (*     {  *)
  (*       status = status; *)
  (*       postfixpoint =  *)
  (*         match result_opt with *)
  (*         | None -> [] *)
  (*         | Some (template, values) -> [((), [[conv template]])] *)
  (*     } *)

  (* let round sys = build_result Dynsys.poly_of_quadratic_form (QuadTemplates.round sys) *)
  (* let shape sys = build_result Dynsys.poly_of_quadratic_form (QuadTemplates.shape sys) *)
  (* let affine sys = build_result Dynsys.poly_of_quadratic_form (QuadTemplates.affine sys) *)
  
  (* (\* Piecewise linear systems *\) *)
  (* module PQuadTemplates = PiecewiseQuadraticTemplates.Make(Dynsys)     *)
  (* let piecewise_lin k linsys = PQuadTemplates.piecewise_lin k linsys  *)
    
  (* Polynomial systems *)
   module PropSOSTemplates = PropSOSTemplates.Make(Dynsys) 
      
  let prop_driven_sos_lyap 
      (prop:     (Dynsys.poly_t -> Sos.polynomial_expr -> Dynsys.basic_semialgebraic_t) option)
      (sys : Dynsys.poly_t)
      (deg : int) : analysis_result_t = 
    let status, result_opt = PropSOSTemplates.template ?prop  sys deg in
    { 
      status = status;
      postfixpoint = 
	match result_opt with
	  | None -> []
	  | Some template -> [((), [[template]])]
      }


  let liouville_method sys deg =
    let _ = Liouville.template sys deg in
    {
      status = Osdp.SdpRet.Unknown;
      postfixpoint = []
    }

    
  (** Narrowing with multiple templates *)

  (* Narrowing through min-policy iterations *)
  type quad_template_t = Dynsys.Mat.t 
  type poly_template_t = Dynsys.Poly.t
  type bound_t = Minf | Pinf | Fin of Dynsys.coeff
      
  let narrow_linsys _lin_sys _templates = assert false

  (* val narrow_piecewise_linsys: Dynsys.poly_t -> (poly_template_t *
     bound_t) array -> (poly_template_t * bound_t) array *)
      
  let narrow_sys _sys _templates = assert false

  end 
