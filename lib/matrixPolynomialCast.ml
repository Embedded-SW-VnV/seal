module type S =
  sig
    module Coeff : Osdp.Scalar.S
    module Poly : Osdp.Polynomial.S 
    module Mat : Osdp.Matrix.S
  (* module Sos : Osdp.Sos.S   *)

           (** Basic datatypes: semialg, ball *)
    
  type basic_semialgebraic_t = Poly.t list (* conjunction of zero sublevel sets *)
  type semialgebraic_t = basic_semialgebraic_t list (* disjunctive normal form
						   with zero sublevel sets *)
  type ball_t = Coeff.t array * Coeff.t   (* (center, radius) ball  *)

  (** Conversion from (linear|quadratic) maps to matrices. All operations are
      exacts (no linearization). *)
    
  (** convert an array of linear assign into a matrix update : A x *)
  val matrix_of_linear_map: Poly.t array -> Mat.t

  (** convert a polynomial p into a quadratic form (1 x)^t A (1 x)
      p should, of course, be at most quadratic.
      A will be symmetric and of size (p.nb_vars + 1)^ 2  *)
  val quadratic_form_of_poly: Poly.t -> Mat.t

  (** convert a matrix to a polynomial rep : x^t A x *)    
  val poly_of_quadratic_form: ?is_homogenous:bool -> Mat.t -> Poly.t

  (** convert a matrix to an array of linear assign: A x. Ie. y_1 =
     A_(1,* ) x, y_2 = A_(2,* ) x ...
 *)
    
  val linear_map_of_matrix: Mat.t -> Poly.t array

  (** Simple functions *)

  val norm2_square_center: int -> Coeff.t array -> Poly.t
  val norm2_square: int -> int -> Poly.t
  val ball_to_semialg: int -> ball_t -> basic_semialgebraic_t

end

exception NonLinear
  
module Make (C: Osdp.Scalar.S)
          (P: Osdp.Polynomial.S with type Coeff.t = C.t) (M:Osdp.Matrix.S with type Coeff.t = C.t )  = (
  struct
    (* module Coeff = C
     * module Poly = P
     * module Mat = M *)
    module Coeff = C               
    (* module Poly = Osdp.Polynomial.Make (C) 
     * module Mat = Osdp.Matrix.Make (C) *)
    module Poly = P
    module Mat = M 

  (* module Sos = Osdp.Sos.Make (PolyO)  *)
    
  (** convert an array of linear assign into a matrix update : A x *)
  let matrix_of_linear_map la =
    (* let dim = Array.length la in *)
    let nb_vars = Array.fold_left (fun res poly -> max res (Poly.nb_vars poly)) 0 la in 
    (* we assume that the array defines variables x0 to x(dim-1) *)
    Mat.of_array_array (
      Array.map (
	fun poly ->
	  let monomes = Poly.to_list poly in
	  let sorted_coeffs =
	    List.fold_left (
	      fun accu (monomial, coeff) ->
		let m_degs = Osdp.Monomial.to_list monomial in
		(* we check linearity and extract the idx value *)
		let deg_sum, idx, _ =
		  List.fold_left (fun (deg_sum, fst_pos_idx, current_idx) d ->
		    d + deg_sum,
		    (if fst_pos_idx = None && d >0 then Some current_idx else fst_pos_idx),
		    current_idx + 1
		  )
		    (0, None, 0) m_degs
	      in
	      let idx =
		match deg_sum, idx with
		| 1, None -> assert false (* Should not happen, by construction *)
		| 1, Some idx -> idx
		| 0, _  (* this happen for affine update, ie. polynomial with a non null constant part *)
		|_ -> raise NonLinear
	      in
	      (idx, coeff):: accu 
	    ) [] monomes
	  in
	  (* We allocate an 0-filled array, and fill it with the computed coeffs *)
	  let lu_array = Array.make nb_vars (Mat.Coeff.of_int 0) in
	  List.iter (fun (idx, coeff) -> lu_array.(idx) <- coeff) sorted_coeffs;
	  lu_array
      )
	la
    )

  (** convert a polynomial p into a quadratic form (1 x)^t A (1 x)
     p should, of course, be at most quadratic.
     A will be symmetric and of size (p.nb_vars + 1)^ 2
  *)
  let quadratic_form_of_poly p =
    let dim = Poly.nb_vars p in
    let mat = Array.make_matrix (dim+1) (dim+1) (Coeff.of_int 0) in
    List.iter (fun (m,c) ->
      let m_degs = Osdp.Monomial.to_list m in
      let vars_deg, _ = List.fold_left (fun (res, current_idx) d ->
	(if d > 0 then (current_idx, d)::res else res),
	current_idx+1
      ) ([], 0) m_degs in
      (* because of non homegenous vector (ie. affine part) we have to
	 add 1 to indices account for it *)
      match vars_deg with
      | [] -> mat.(0).(0) <- c (* would appear for affine form *)
      | [v_idx, 2] -> mat.(v_idx+1).(v_idx+1) <- c
      | [v1, 1; v2, 1] -> let c_half = Coeff.div c (Coeff.of_int 2) in
			  mat.(v1+1).(v2+1) <- c_half; mat.(v2+1).(v1+1) <- c_half
      | [v1, 1] -> let c_half = Coeff.div c (Coeff.of_int 2) in
		   mat.(v1+1).(0) <- c_half; mat.(0).(v1+1) <- c_half
      | _ -> raise NonLinear
	 
    ) (Poly.to_list p);
    Mat.of_array_array mat
      
  (** convert a matrix to a polynomial rep : x^t A x *)
  let poly_of_quadratic_form ?(is_homogenous=true) m =
    let elems, _ =
      Array.fold_left (
	fun (res, idx_x) linear_cond ->
	  let res',  _ =
	    Array.fold_left (fun (res, idx_y) c ->
	      let monomial = (* monomial x_{idx_x} * y_{idx_y} *)
		let sz = 1 + max idx_x idx_y in
		let arr = Array.make sz 0 in
		arr.(idx_x) <- 1;
		arr.(idx_y) <- arr.(idx_y) + 1; (* Handle the caase where idx_x = idx_y *)
		let monomial_l = Array.to_list arr in
		if is_homogenous then (* [1] means x_0 while it means 1 when not homogeneous *)
		  Osdp.Monomial.of_list monomial_l
		else 
		  begin
		    (* to account for constant
		       part, we remove the head
		       of list: [0;1]
		       describing x_0 and [1]
		       becomes [], hence
		       constant *)
		    match monomial_l with
		    | _::tl -> Osdp.Monomial.of_list tl
		    | _ -> assert false (* should never happen for non homogeneous matrix *)
		  end     
	      in
	      (monomial, c)::res,
	      idx_y+1
	    ) (res,0) linear_cond
	  in
	  res', idx_x+1
      ) ([], 0) (Mat.to_array_array m)
    in
    Poly.of_list elems
  
  (** convert a matrix to an array of linear assign: A x. Ie. y_1 = A_(1,* ) x, y_2 = A_(2,* ) x ... *) 
  let linear_map_of_matrix mat_to_poly_array  =
    Array.map (fun linear_assign ->
     let la = Array.to_list linear_assign in
      let elems, _ =
	List.fold_left (fun(res, current_idx) c ->
            let res' = 
              if Coeff.compare Coeff.zero c = 0 then
                res
              else (
                 let arr = Array.make (current_idx+1) 0 in
	         arr.(current_idx) <- 1;
	         let monomial = Osdp.Monomial.of_list (Array.to_list arr) in
	         (monomial, c)::res
              )
            in
            res', current_idx+1
	)
	  ([], 0) la
      in
      Poly.of_list elems
    ) (Mat.to_array_array mat_to_poly_array)



(* module type SemiAlgS = 
 sig 
   module Poly: Osdp.Polynomial.S 
  

  type basic_semialgebraic_t = Poly.t list (* conjunction of zero sublevel sets *)
  type semialgebraic_t = basic_semialgebraic_t list (* disjunctive normal form
						   with zero sublevel sets *)
  type ball_t = Poly.Coeff.t array * Poly.Coeff.t   (* (center, radius) ball  *)

  val norm2_center: Poly.Coeff.t array -> Poly.t
  val norm2_dim: int -> Poly.t
  val ball_to_semialg: ball_t -> basic_semialgebraic_t
  
end
  
module Semialgebraic (Poly : Osdp.Polynomial.S) = (
  struct
*)
    (* type coeff = Poly.Coeff.t *)
    (* module Poly = Poly *)
      
    type basic_semialgebraic_t = Poly.t list (* conjunction of zero sublevel sets *)
    type semialgebraic_t = basic_semialgebraic_t list (* disjunctive normal form
						   with zero sublevel sets *)
    type ball_t = Poly.Coeff.t array * Poly.Coeff.t   (* (center, radius) ball  *)
      
      
    let norm2_square_center start_idx center =
      List.fold_left (fun n (v,c) -> Poly.(n + (v - !c)**2)) Poly.zero 
	(Array.to_list (Array.mapi (fun idx center_i -> Poly.var (start_idx + idx), center_i) center))

    let norm2_square start_idx dim =
      norm2_square_center start_idx  (Array.make dim Poly.Coeff.zero)

    let ball_to_semialg start_idx ((center, radius) : ball_t) =   (* - norm2(x - center) + radius >= 0*)
      (* since we use norm2 squared, we have to use radius^2 *)
      let n2 = norm2_square_center start_idx center in
      [Poly.(- n2 + !radius * !radius)]


      

  (* (\* Could be done with the compose function but I am unsure of the variable order *\) *)
  (* let ball vars radius center = *)
  (*   if Array.length vars <> Array.length center then *)
  (*     raise (Invalid_argument "dim mismatch"); *)
  (*   let radius_square = radius**2. in *)
  (*   let init = Sos.Const (P.mult_scalar (P.Coeff.of_float radius_square) P.one) in *)
  (*   let res, _ = Array.fold_left ( *)
  (*     fun (accu,idx) v ->  *)
  (* 	let v_center = Sos.Const (P.mult_scalar (P.Coeff.of_float center.(idx)) P.one)  in *)
  (* 	Sos.( accu - (v-v_center)^2 ), idx+1) *)
  (*     (init,0)  *)
  (*     vars *)
  (*   in *)
  (*   res *)


        end:S  with type Coeff.t = C.t and type Poly.Coeff.t = C.t and type Mat.Coeff.t = C.t
      and type Poly.t = P.t and type Mat.t = M.t
)

(* end :SemiAlgS with module Poly = Poly (\* and module Mat = Mat *\))  *)
