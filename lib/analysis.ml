type status_t = Osdp.SdpRet.t

(* Kept in sync with analysis.mli by hand: an .mli that spells out a
   [module type S] requires the .ml to declare a matching one (module types
   aren't inferred like values). A stale copy here previously caused
   [round]/[shape]/[affine] to silently disappear from [Make]'s result even
   after being implemented, because [Make] was sealed against this local,
   outdated copy before the .mli's check ever ran. *)
module type S = sig
  module Dynsys : Dynsys.S
  module Sos : Osdp.Sos.S

  type 'guard_t guarded_semialgebraic = 'guard_t * Dynsys.semialgebraic_t

  type 'guard_t guarded_analysis_result_t = {
    status: status_t;
    postfixpoint: 'guard_t guarded_semialgebraic list
  }

  type analysis_result_t = unit guarded_analysis_result_t

  val pp_result: Format.formatter -> analysis_result_t -> unit
  val pp_guarded_result: (Format.formatter -> 'guard_t -> unit) -> Format.formatter -> 'guard_t guarded_analysis_result_t -> unit

  val round: ?pad:float -> Dynsys.lin_t -> analysis_result_t
  val shape: ?pad:float -> Dynsys.lin_t -> analysis_result_t
  val affine: ?pad:float -> Dynsys.lin_t -> analysis_result_t

  val piecewise_lin:
    ?offsets:Dynsys.coeff array array ->
    ?solver:Osdp.Sdp.solver ->
    ?pad:float ->
    int ->
    Dynsys.lin_t ->
    Dynsys.quad_guard_t guarded_analysis_result_t

  val prop_driven_sos_lyap:
    ?domain_restriction:Dynsys.basic_semialgebraic_t ->
    ?solver:Osdp.Sdp.solver ->
    ?kappa:Sos.polynomial_expr ->
    ?pad:float ->
    Dynsys.poly_t ->
    int ->
    analysis_result_t

  val liouville_method:
    ?solver:Osdp.Sdp.solver ->
    ?pad:float ->
    Dynsys.poly_t ->
    int ->
    analysis_result_t

  type quad_template_t = Dynsys.Mat.t
  type poly_template_t = Dynsys.Poly.t
  type bound_t = Minf | Pinf | Fin of Dynsys.coeff

  val narrow_linsys:
    Dynsys.lin_t ->
    (quad_template_t * bound_t) array ->
    (quad_template_t * bound_t) array

  val narrow_sys:
    Dynsys.poly_t ->
    (poly_template_t * bound_t) array ->
    (poly_template_t * bound_t) array
end

module Make (Dynsys: Dynsys.S) = struct
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

    (* Linear systems analyses *)
    module QuadTemplates = QuadraticTemplates.Make(Dynsys)

    (* round/shape/affine actually prove [x'Px <= 1] (an ellipsoid, not a
       homogeneous cone), so the "1" must be subtracted here to match the
       [p(x) <= 0] convention used for every other analysis's postfixpoint
       (see pp_basic_semialg) -- mirroring piecewise_lin's own [- const
       alpha] just below. Without it, the returned invariant silently
       claimed the far stronger (and generally false) [x'Px <= 0]. *)
    let build_result conv (status, result_opt) =
      {
        status = status;
        postfixpoint =
          match result_opt with
          | None -> []
          | Some (template, _values) -> [((), [[Poly.(conv template - const Dynsys.Coeff.one)]])]
      }

    let options_of_pad = function
      | None -> QuadTemplates.Lmi.default
      | Some pad -> QuadTemplates.Lmi.{ default with pad }

    let round ?pad sys = build_result Dynsys.Cast.poly_of_quadratic_form (QuadTemplates.round ~options:(options_of_pad pad) sys)
    let shape ?pad sys = build_result Dynsys.Cast.poly_of_quadratic_form (QuadTemplates.shape ~options:(options_of_pad pad) sys)
    let affine ?pad sys = build_result Dynsys.Cast.poly_of_quadratic_form (QuadTemplates.affine ~options:(options_of_pad pad) sys)
  
  (* Piecewise linear systems *)
  module PQuadTemplates = PiecewiseQuadraticTemplates.Make(Dynsys)

  let piecewise_lin
      ?offsets
      ?solver
      ?pad
      (k : int)
      (sys : Dynsys.lin_t) : Dynsys.quad_guard_t guarded_analysis_result_t =
    let options = match pad with None -> None | Some pad -> Some PQuadTemplates.Lmi.{ default with pad } in
    let status, result_opt = PQuadTemplates.invariant ?offsets ?options ?solver k sys in
    let cells = Array.of_list sys.Dynsys.map in
    match result_opt with
    | None -> { status; postfixpoint = [] }
    | Some r ->
      let postfixpoint =
        Array.to_list
          (Array.mapi
             (fun i path ->
               let plast = path.(Array.length path - 1) in
               let guard = fst cells.(plast) in
               let invariant =
                 Poly.(
                   Dynsys.Cast.poly_of_quadratic_form ~is_homogenous:false
                     r.PQuadTemplates.certificates.(i)
                   - const r.PQuadTemplates.a)
               in
               (guard, [ [ invariant ] ]))
             r.PQuadTemplates.paths)
      in
      { status; postfixpoint }


  (* Polynomial systems *)
   module PropSOSTemplates = PropSOSTemplates.Make(Dynsys)
   module Liouville = Liouville.Make(Dynsys)

  let prop_driven_sos_lyap
      ?domain_restriction
      ?solver
      ?kappa
      ?pad
      (sys : Dynsys.poly_t)
      (deg : int) : analysis_result_t =
    let status, result_opt = PropSOSTemplates.template ?domain_restriction ?solver ?kappa ?pad sys deg in
    {
      status = status;
      postfixpoint =
	match result_opt with
	  | None -> []
	  | Some template -> [((), [[template]])]
      }


  (* Liouville.compute's own w satisfies [w >= 0] on reachable states (its
     "raw" w, before the internal -1 shift, satisfies [w_raw >= 1] -- see
     the note on [Liouville.compute]'s own doc comment): the OPPOSITE
     convention from every other Analysis method here, which all report
     "invariant holds where p <= 0" (see pp_basic_semialg). Negating it
     here keeps that convention uniform across all six entry points,
     instead of leaving liouville_method as a silent, easy-to-get-backwards
     exception (confirmed: this file's own earlier doc comment, and this
     module's first full_check_main.ml sweep, both got this backwards). *)
  let liouville_method ?solver ?pad (sys : Dynsys.poly_t) (deg : int) : analysis_result_t =
    let padding = match pad with None -> Liouville.default_params.Liouville.padding | Some p -> p in
    match Liouville.compute ~params:{ Liouville.default_params with deg; solver; padding } sys with
    | Some r -> { status = r.Liouville.ret; postfixpoint = [((), [[Poly.(sub zero r.Liouville.w)]])] }
    | None -> { status = Osdp.SdpRet.Unknown; postfixpoint = [] }

    
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
