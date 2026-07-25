
module type S =
sig
  
  (* Provides basic types and modules. Used to convert matrices to polynomials
     and vice-versa *)
  module Coeff : Osdp.Scalar.S
  module Mat : Osdp.Matrix.S with type Coeff.t = Coeff.t
  module Poly : Osdp.Polynomial.S with type Coeff.t = Coeff.t
  module Cast : MatrixPolynomialCast.S with type Coeff.t = Coeff.t and type Poly.Coeff.t = Coeff.t and type Mat.Coeff.t = Coeff.t and type Mat.t = Mat.t and type Poly.t = Poly.t
  module Properties : Properties.S with type Coeff.t = Coeff.t and type Poly.Coeff.t = Coeff.t and type Mat.Coeff.t = Coeff.t and type Mat.t = Mat.t and type Poly.t = Poly.t
       
  type coeff = Coeff.t

  (* module SA : MatrixPolynomialCast.SemiAlgS *)
(*
  type basic_semialgebraic_t = Poly.t list (* conjunction of zero sublevel sets *)
  type semialgebraic_t = basic_semialgebraic_t list (* disjunctive normal form
						   with zero sublevel sets *)
  type ball_t = coeff array * coeff   (* (center, radius) ball  *)
*)
      (** Basic datatypes: semialg, ball *)
    
  type basic_semialgebraic_t = Poly.t list (* conjunction of zero sublevel sets *)
  type semialgebraic_t = basic_semialgebraic_t list (* disjunctive normal form
						   with zero sublevel sets *)
  type ball_t = Coeff.t array * Coeff.t   (* (center, radius) ball  *)

  (* Guards *)
  type poly_guard_t = basic_semialgebraic_t
  (* Strict rows (p(x) > 0) must be told apart from weak ones (p(x) >= 0):
     this matters for testing whether a cell/switch is feasible at all
     (Motzkin's transposition theorem treats them differently -- see
     PiecewiseQuadraticTemplates.is_feasible), and for cells meant to
     partition state space without overlapping on their shared boundary
     (one side of the boundary strict, the other weak). It does NOT matter
     for the S-procedure/quadratization used in the actual invariance LMIs
     (both kinds get the same nonnegative-multiplier treatment there). *)
  type strictness = Strict | Weak
  type quad_guard_t = (Mat.t * strictness) list
    
  (* Updates *)
  type poly_update_t = Poly.t array (* array of size df *)
  type lin_update_t = Mat.t 
    
  type ('guard_t,'update_t, 'constraints_t) t = {
    df: int;                            (* Nb of State vars *)
    di: int;                            (* Nb of input vars *)
    map: ('guard_t * 'update_t) list; (* (guards, expr) list *)
    init: 'constraints_t;
    input: 'constraints_t option;
    r_g: Poly.Coeff.t option;           (* radius of state vars ball *)
  }

  type poly_t = (poly_guard_t, poly_update_t, basic_semialgebraic_t) t
  type lin_t  = (quad_guard_t, lin_update_t, ball_t) t
    
  val is_piecewise: ('a, 'b, 'c) t -> bool
  val is_linear: poly_t -> bool

  (** Only valid if [is_linear sys]; raises [Invalid_argument] otherwise.
      Note: [init]/[input] cannot be generically recovered as a [ball_t]
      from a [basic_semialgebraic_t] (not every semialgebraic set is a
      ball), so they are set to a degenerate, zero-radius placeholder.
      This is harmless for analyses that only look at [map] (e.g. the
      quadratic templates in [QuadraticTemplates]). *)
  val poly_to_linear: poly_t -> lin_t

  val linear_to_poly: lin_t -> poly_t

end 


module Make (C: Osdp.Scalar.S) = (
struct
  module Coeff = C
  module Poly = Osdp.Polynomial.Make (Coeff) 
  module Mat = Osdp.Matrix.Make (Coeff)

               
  module Cast = MatrixPolynomialCast.Make (C) (Poly) (Mat)
  module Properties = Properties.Make (C) (Poly) (Mat)
                    
  type coeff = Coeff.t
  (* module SA = MatrixPolynomialCast.Semialgebraic(Poly) *)

    (** Basic datatypes: semialg, ball *)
    
  type basic_semialgebraic_t = Poly.t list (* conjunction of zero sublevel sets *)
  type semialgebraic_t = basic_semialgebraic_t list (* disjunctive normal form
						   with zero sublevel sets *)
  type ball_t = Coeff.t array * Coeff.t   (* (center, radius) ball  *)


    
  (* Guards *)
  type poly_guard_t = basic_semialgebraic_t (* Poly.t list *) (* conjunction of constraints *)
  type strictness = Strict | Weak
  type quad_guard_t = (Mat.t * strictness) list
    
  (* Updates *)
  type poly_update_t = Poly.t array (* array of size df *)
  type lin_update_t = Mat.t  (* A  in R^{(df+di) * df}  *)
    
  type ('guard_t,'update_t, 'constraints_t) t = {
    df: int;                            (* Nb of State vars: x0 to x(df-1) *)
    di: int;                            (* Nb of input vars: x(df) to x(df+di-1) *)
    map: ('guard_t * 'update_t) list; (* (guards, expr) list *)
    init: 'constraints_t;
    input: 'constraints_t option;
    r_g: coeff option;           (* radius of state vars ball *)
  }

  type poly_t = (poly_guard_t, poly_update_t, basic_semialgebraic_t) t
  type lin_t  = (quad_guard_t, lin_update_t, ball_t) t
  
  let is_piecewise sys = List.length sys.map > 1 

  let is_linear (sys: poly_t) = List.for_all (fun (gl,ua) ->
    List.for_all (fun g -> Poly.degree g <= 2) gl (* up to quadratic guards *)
    && Array.fold_left (fun ok u -> ok && Poly.degree u <= 1) true ua (* up to linear update *)
  ) sys.map 

  let poly_to_linear (sys: poly_t) =
    if not (is_linear sys) then
      raise (Invalid_argument "poly_to_linear: system is not linear");
    let map = List.fold_right (fun (gl, ua) res ->
      (* poly_guard_t (Poly.t list) has no strict/weak distinction of its
         own, so there's nothing to preserve here: every row defaults to
         Weak, matching this cast's prior (pre-strictness) behavior. *)
      let gl' = List.fold_right (fun g gl_res -> (Cast.quadratic_form_of_poly g, Weak)::gl_res) gl [] in
      let u' = Cast.matrix_of_linear_map ua in
      (gl', u')::res
    ) sys.map [] in
    let degenerate_ball n : ball_t = (Array.make n Coeff.zero, Coeff.zero) in
    {
      sys with
      map = map;
      init = degenerate_ball sys.df;
      input = Utils.opt_map (fun _ -> degenerate_ball sys.di) sys.input;
    }

  let linear_to_poly (sys: lin_t) = 
    let map = List.fold_right (fun (gl, matA) res ->
      (* poly_guard_t can't represent strictness, so it's dropped here
         (the reverse direction of poly_to_linear's default-to-Weak). *)
      let gl' = List.fold_right (fun (g, _s) gl_res -> (Cast.poly_of_quadratic_form ~is_homogenous:false (g:Mat.t))::gl_res) gl [] in
      let up = Cast.linear_map_of_matrix matA in
      (gl', up)::res
    ) sys.map [] in
    { 
      sys 
      with
	map = map;
	init = Cast.ball_to_semialg 0 sys.init;
	input = Utils.opt_map (Cast.ball_to_semialg sys.df) sys.input;
    } 

    
end: S  )

module Float = Make (Osdp.Scalar.Float)
(* module Q = Make (Polynomial.Q) *)
