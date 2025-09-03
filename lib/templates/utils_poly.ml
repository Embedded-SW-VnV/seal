
module Make (Sos : Osdp.Sos.S) =
  struct
    module P = Sos.Poly
    module C = P.Coeff
    let zero : Sos.polynomial_expr =
      Sos.( !(C.of_float 0.0 )) 
      
    let float_cst x = P.const (C.of_float x)  
    let sos_cst x = Sos.Const (P.mult_scalar (P.Coeff.of_float x) P.one) 

    let norm2_square = 
      try
        List.fold_left (fun accu e -> Sos.( accu + (e ** 2) )) Sos.( !(C.of_float 0.0 ) )
      with _ -> assert false

    (* 1 - x^2 - y^2 ... *)  
    let centered_ball (vars: Sos.polynomial_expr array) (radius:float) =
      (* Format.eprintf "Centered ball vars: %a@." (fun fmt arr -> Array.iter (fun v -> Sos.pp fmt v) arr) vars; *)
      let radius_square = radius**2. in
      let init = Sos.Const (P.mult_scalar (P.Coeff.of_float radius_square) P.one) in
      Array.fold_left (fun accu v -> 
          (*let v = Sos.( v ) in*)
          Sos.( accu - (v ** 2) )
        ) 
        init
        vars

    let hypercube vars =
      (* We encode each interval in a quadratic way: 
       x in [a,b] --> (x-(b+a)/2)^2 <= (b-a)/2
       expressed as a positive cons: (b-a)/2 - (x-(b+a)/2)^2 >= 0
       TODO enrich the code with [a,b] intervals, 
       for the moment default value: a=-1, b=1, 1 - x^2 
       *)
      Array.fold_left (
          fun accu v ->
          (Sos.( !(C.of_float 1. ) - ( v ** 2) ))::accu
        ) [] vars


    (* Could be done with the compose function but I am unsure of the
       variable order *)
    let ball vars radius center =
      if Array.length vars <> Array.length center then
        raise (Invalid_argument "dim mismatch");
      let radius_square = radius**2. in
      let init = Sos.Const (P.mult_scalar (P.Coeff.of_float radius_square) P.one) in
      let res, _ = Array.fold_left (
                       fun (accu,idx) v -> 
                       let v_center = Sos.Const (P.mult_scalar (P.Coeff.of_float center.(idx)) P.one)  in
                       Sos.( accu - (v-v_center)** 2 ), idx+1)
                     (init,0) 
                     vars
      in
      res
  
    let linear_map_ball vars radius center lin_map =
      if Array.length vars <> Array.length center || Array.length center <> Array.length lin_map then
        raise (Invalid_argument "dim mismatch");
      let radius_square = radius**2. in
      let init = Sos.Const (P.mult_scalar (P.Coeff.of_float radius_square) P.one) in
      let fold2 f init a1 a2 =
        let l = Array.length a1 in
        let rec aux accu idx =
          if idx >= l then
	    accu
          else
	    try
	      aux (f accu (Array.get a1 idx) (Array.get a2 idx)) (idx+1)
	    with Invalid_argument _ -> raise (Invalid_argument "dim mismatch")
        in
        aux init 0
      in
      let res, _ = fold2 (
                       fun (accu,idx) v (ai, bi) -> 
                       let v_center = sos_cst center.(idx) in
                       let ai = sos_cst ai and bi = sos_cst bi in
                       Sos.( accu - ((ai * v + bi)-v_center)** 2 ), idx+1)
                     (init,0) 
                     vars
                     lin_map
      in
      res


    let solver_name s = 
      match s with
      | Osdp.Sdp.Mosek -> "Mosek"
      | Osdp.Sdp.Csdp -> "Csdp"
      | Osdp.Sdp.Sdpa -> "Sdpa"
      | _ -> assert false

    let list_init sz f =
      (* List.init sz f *)
      let rec aux i =
        if i >= sz then []
        else f i :: aux (i+1)
      in
      aux 0


    (* Following functions allow to apply scaling to a polynomial *)
       
    (* Returns the degree in sys_vars. Ie the nb_vars-th first
       variables of the monomial vars *)
    let monomial_deg_sv m nb_sys_vars =
      let nb_occ, _ = 
        List.fold_left (
            fun (accu, (cpt:int)) var_occ -> 
	    if cpt < nb_sys_vars then 
	      (accu+var_occ), (cpt+1) 
	    else
	      accu, (cpt+1)
          ) (0, 0) (Osdp.Monomial.to_list m)
      in
      nb_occ

    let rec r_pow_n r n =
      if n < 0 then
        C.mult (C.div C.one r) (r_pow_n r (n+1))
      else if n= 0 then C.one else
        C.mult r (r_pow_n r (n-1))
  
    let transform_poly (f:Sos.Poly.t) r nb_vars : Sos.Poly.t =
      let coeff_mon_l = Sos.Poly.to_list f in
      Sos.Poly.of_list (
          List.map 
            (fun (m, c) -> 
	      (* We multiply c by r_g^{nb occurences of sys_var in monomial} *)
	      let nb_occ = monomial_deg_sv m nb_vars in
              (m, C.mult c (r_pow_n r (nb_occ - 1))) (* TODO check the -1 *)
            ) coeff_mon_l
        ) 

    let unshrink_poly f r nb_vars = 
      let coeff_mon_l = Sos.Poly.to_list f in
      Sos.Poly.of_list (
          List.map 
            (fun (m, c) -> 
	      (* We multiply c by r_g^{nb occurences of sys_var in monomial} *)
	      let nb_occ = monomial_deg_sv m nb_vars in
	      (m, C.div c (r_pow_n r nb_occ))
            ) coeff_mon_l
        ) 

let rec transform_poly_expr e r nbvars =  
  let app e = transform_poly_expr e r nbvars in
  Sos.(match e with 
  |Const p -> Const (transform_poly p r nbvars)
  | Var _ (*v*) -> e
  | Mult_scalar (c, e) -> Mult_scalar (c, app e)
  | Add (e1, e2) -> Add (app e1, app e2)
  | Sub (e1, e2) -> Sub (app e1, app e2)
  | Mult (e1, e2) -> Mult (app e1, app e2)
  | Power (e, d) -> Power (app e, d)
  | Compose (e, el) -> Compose (app e, List.map app el)
  | Derive (e, i) -> Derive (app e, i)
  )



    
end
