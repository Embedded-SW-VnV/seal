

               
           
module Make (Dynsys: Dynsys.S) = 
  struct

  
  (* open Dynsys *)
  module Mat = Dynsys.Mat 
  module Coeff = struct
    include Mat.Coeff
    let of_int x = of_float (float_of_int x)
    let lt = (<)
    let gt = (>)
  end 
  module Lmi = Osdp.Lmi.Make (Mat)
    
  module TUtils = TemplatesUtils.Make (Coeff)
    
  type sys_lin_t = Lin of Mat.t | Aff of Mat.t * Mat.t
      
  let get_sys_mat lin_sys = ( 
    (* System should be linear and not piecewise *)
    match lin_sys.Dynsys.map with
      [_(*unit*), m] ->
	let lin = Mat.nb_lines m in
	let col = Mat.nb_cols m in
        Format.eprintf "Matrix in R^(%i,%i)@." lin col;
	if lin = col then
	  Lin m
	else if col > lin then
	  let mll = Mat.to_list_list m in
	  let a,b = List.fold_right  (
	    fun mline (a, b) ->
	      let arr = Array.of_list mline in
	      let la = Array.sub arr 0 lin in
	      let lb = Array.sub arr lin (-lin + Array.length arr) in
	      (Array.to_list la)::a, (Array.to_list lb)::b
	  ) mll ([], []) 
	  in
	  Aff(Mat.of_list_list a, Mat.of_list_list b)
	else
	  assert false
    | _ -> assert false (* pas le bon format TODO *)
  )

  let value_mat var values = try Some (Lmi.value_mat var values, values) with Not_found -> None
    
  let round ?(options=Lmi.default) (lin_sys: Dynsys.lin_t) = 

    (* Unknowns *)
    let _, unknown_P = Lmi.var_var "P" lin_sys.Dynsys.df in (* the template *)
    let _ (*lambda_var*), lambda_id = Lmi.var_var "lambda" 1 in (* a scalar *)

    (* system def *)
    let a = match get_sys_mat lin_sys with Lin a -> a | Aff(a, _) -> a in

    let obj, lmis= 
      let open Lmi in
      let minicoeff = ! (Coeff.div (Coeff.of_int 1) (Coeff.of_int 1000)) in
      let eye = Eye (Mat.nb_lines a) in 

      (* P - A' * P * A - 0.0001 eye *)
      let exp1 = unknown_P - (~: !! a) * unknown_P * !! a - minicoeff * eye in

      (* P - eye *)
      let exp2 = unknown_P - eye in

      (* lambda * eye - P *) 
      let exp3 = lambda_id * eye - unknown_P in
      
      let lmis = [exp1; exp2; exp3]  in

      let obj = Minimize lambda_id in  (* minimize lambda *) 
      obj, lmis 

    in
    
    let ret, _ (*objs*), values = Lmi.solve ~options obj lmis in
    
    ret, value_mat unknown_P values

      
  let lambda_var, lambda_id = Lmi.var_var "lambda" 1  (* a scalar *)
    
 (* compute an ellipsoid such that A'PA-lambda*P < 0 with lambda
     minimal performs dichotomy on lambda returns both tP and the
     lanbda *)
  let shape ?(options=Lmi.default) lin_sys =
    
    (* Unknowns *)
    let _, unknown_P  = Lmi.var_var "P" lin_sys.Dynsys.df in (* the template *)
 
    (* system def *)
    let a = match get_sys_mat lin_sys with Lin a -> a | Aff(a, _) -> a in
    
    let compute_P lambda =
      let obj, lmis= 
	let open Lmi in
	let eye = Eye (Mat.nb_lines a) in 

	(* lambda*P-A'*P*A *)
	let expr1 = ! lambda * unknown_P - (~: !! a) * unknown_P * !! a in
	
	(* P - eye *)
	let expr2 = unknown_P - eye in

	let obj = Purefeas in

	let lmis= [expr1; expr2] in
	obj, lmis
      in
      let ret, _ (*objs*), values = Lmi.solve ~options obj lmis in
      (* we record the choosen lambda *)
      let values = Lmi.register_value lambda_var lambda values in
      if Osdp.SdpRet.is_success ret then (
	ret, value_mat unknown_P values
      )
      else (
	ret, None
      )
    in
    TUtils.dicho (Coeff.of_int 0) (Coeff.of_int 1) compute_P 
        
      

  (* all in one *)
  let affine ?(options=Lmi.default) lin_sys =

    (* Unknowns *)
    let _, unknown_P = Lmi.var_var "P" lin_sys.Dynsys.df in (* the template *)
    let tau_var, _ = Lmi.var_var "tau" 1 in 

    let lambda_i n = Lmi.var_var ("lambda_" ^ string_of_int n) 1 in (* a scalar *)

    
    (* System *)
    match get_sys_mat lin_sys with
    | Lin _ ->         Format.eprintf "Linear sys@."; shape lin_sys (* call shape *) 
    | Aff(a, b) -> begin
        Format.eprintf "Affine sys@.";
      let dim_p = Mat.nb_lines a in
      let nb_inputs = Mat.nb_cols b in
      let eye_P = Lmi.eye (Mat.nb_lines a) in 
      
      (* gives the least lambda fixpoint for a given tau *)
      let compute_tau tau =
	
	let term1 =
	  let open Lmi in
	  block
	    [|
	      [| -  (~: !! a) * unknown_P * !! a; -(~: !! a) * unknown_P * !! b; zeros dim_p 1 |];
	      [| -(~: !! b) * unknown_P * !! a; -(~: !! b) * unknown_P * !! b; zeros nb_inputs 1 |];
	      [| zeros 1 dim_p; zeros 1 nb_inputs; eye 1|];
	    |] 
	in
	(* Report.debugf ~kind:"policy"  ~level:10 *)
	(* 	(fun fmt -> Format.fprintf fmt "@.@.Computing term2 (nb inputs=%i)@." nb_inputs); *)
	let term2 =
	  let open Lmi in
	  let block_mat = 
	    [|
	      [| -unknown_P ; zeros dim_p nb_inputs; zeros dim_p 1 |];
	      [| zeros nb_inputs dim_p; zeros nb_inputs nb_inputs; zeros nb_inputs 1 |];
	      [| zeros 1 dim_p; zeros 1 nb_inputs; eye 1 |];
	    |]
	  in
	  - !tau * block block_mat
	in
	let rec build_terms n (lambda_is, terms) = 
	  if n <= 0 then (lambda_is, terms)
	  else (
	    (* Report.debugf ~kind:"policy" ~level:10
	     *   (fun fmt -> Format.fprintf fmt "@.@.Computing term3/%i@." n); *)
	    let n_1 = n - 1 in
	    let open Lmi in
	    let mat_n = 
	      [|
		[| zeros dim_p dim_p; zeros dim_p nb_inputs; zeros dim_p 1 |];
		[| zeros nb_inputs dim_p; -kron_sym nb_inputs (n_1) (n_1); zeros nb_inputs 1 |];
		[| zeros 1 dim_p; zeros 1 nb_inputs; eye 1 |]
	      |]
	    in
	    let _, lambda_i_n = lambda_i n in
	    let lambda_is' = (lambda_i_n * eye 1) :: lambda_is in
	    let terms' = (-lambda_i_n * block mat_n) :: terms in
	    build_terms (n_1) (lambda_is', terms')
	  )
	in
	
	let lambda_is, terms = build_terms nb_inputs ([], []) in
	(* Report.debugf ~kind:"policy" ~level:10 *)
	(* 	(fun fmt -> Format.fprintf fmt "Done with terms@."); *)
	let lmi1 = 
	  match List.rev ( term1::term2::terms) with
	  | [] -> assert false (* it never happens *)
	  | hd::tl -> List.fold_left (fun x y -> Lmi.add x y) hd tl
	in
	(* P - lambda eye *)
	let lmi2 = let open Lmi in unknown_P - lambda_id * eye_P in

	let lmis = [lmi1; lmi2] @ lambda_is in  (* All lambda_i are positive *)
	let obj = Lmi.Maximize lambda_id in
	let ret, _, values = Lmi.solve ~options obj lmis in
	if Osdp.SdpRet.is_success ret then
	  (* let template = try Lmi.value_mat unknown_P values with Not_found -> assert false in *)
	  ret, value_mat unknown_P (Lmi.register_value tau_var tau values)
	else
	  ret, None
      in

      (* We compute an initial value for tau, this is tau_min  *)
      let shape_status, shape_result = shape lin_sys in
      match shape_result with
      | Some (_, shape_values) ->
         let tau_min = Lmi.value lambda_id shape_values in
	 let has_improved new_res_values res_values =
	   let lambda_res    = try Lmi.value lambda_id res_values with _ ->assert false in
	   let lambda_newres = try Lmi.value lambda_id new_res_values with _ ->assert false in
	   Coeff.gt lambda_newres lambda_res
	 in
         Format.eprintf "Running sampled search@.";
    	 TUtils.sampled_search tau_min (shape_status, shape_result) (Coeff.of_int 1) compute_tau has_improved
      | None -> 
	 (* No chance to improve it *)
	 shape_status, shape_result
    end
       
end 
