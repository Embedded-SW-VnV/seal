

               
           
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

  let split_mat m =
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

  (* One (A_i[,B_i]) per mode of a (possibly switched/piecewise) system,
     in [lin_sys.map] order, guards dropped: a common Lyapunov function is
     sought that holds for every mode's update regardless of which guard
     selects it (i.e. sound for arbitrary/adversarial switching, not just
     the guarded switching sequences the guards actually allow -- the same
     kind of deliberate over-approximation [round]/[shape] already make by
     dropping input). *)
  let get_sys_mats lin_sys = List.map (fun (_guard, m) -> split_mat m) lin_sys.Dynsys.map

  let get_sys_mat lin_sys =
    (* Single-mode convenience wrapper, kept for any caller that knows it
       only ever deals with a one-mode system. *)
    match get_sys_mats lin_sys with
    | [ m ] -> m
    | _ -> assert false (* pas le bon format TODO *)

  let value_mat var values = try Some (Lmi.value_mat var values, values) with Not_found -> None
    
  (* A single P shared by every mode's own [exp1] constraint: P is a common
     Lyapunov function for the whole switched system iff each mode's own
     update decreases the same energy x'Px, so it works no matter which
     mode is active at any given step (a strictly stronger, guard-agnostic
     property than a per-mode/per-path certificate). Reduces to the
     original single-mode LMI when there's exactly one mode. *)
  let round ?(options=Lmi.default) (lin_sys: Dynsys.lin_t) =

    (* Unknowns *)
    let _, unknown_P = Lmi.var_var "P" lin_sys.Dynsys.df in (* the template *)
    let _ (*lambda_var*), lambda_id = Lmi.var_var "lambda" 1 in (* a scalar *)

    (* system def: one A_i per mode *)
    let a_list = List.map (function Lin a -> a | Aff(a, _) -> a) (get_sys_mats lin_sys) in

    let obj, lmis=
      let open Lmi in
      let minicoeff = ! (Coeff.div (Coeff.of_int 1) (Coeff.of_int 1000)) in
      let eye = Eye (Mat.nb_lines (List.hd a_list)) in

      (* P - A_i' * P * A_i - 0.0001 eye, for every mode i *)
      let mode_lmis = List.map (fun a -> unknown_P - (~: !! a) * unknown_P * !! a - minicoeff * eye) a_list in

      (* P - eye *)
      let exp2 = unknown_P - eye in

      (* lambda * eye - P *)
      let exp3 = lambda_id * eye - unknown_P in

      let lmis = mode_lmis @ [exp2; exp3]  in

      let obj = Minimize lambda_id in  (* minimize lambda *)
      obj, lmis

    in

    let ret, _ (*objs*), values = Lmi.solve ~options obj lmis in

    ret, value_mat unknown_P values

      
  let lambda_var, lambda_id = Lmi.var_var "lambda" 1  (* a scalar *)
    
 (* compute an ellipsoid such that A_i'PA_i-lambda*P < 0 for every mode i,
    with a single shared P and the same lambda minimal for all modes at
    once (a common contraction rate for the whole switched system) --
    performs dichotomy on lambda, returns both P and the lambda *)
  let shape ?(options=Lmi.default) lin_sys =

    (* Unknowns *)
    let _, unknown_P  = Lmi.var_var "P" lin_sys.Dynsys.df in (* the template *)

    (* system def: one A_i per mode *)
    let a_list = List.map (function Lin a -> a | Aff(a, _) -> a) (get_sys_mats lin_sys) in

    let compute_P lambda =
      let obj, lmis=
	let open Lmi in
	let eye = Eye (Mat.nb_lines (List.hd a_list)) in

	(* lambda*P-A_i'*P*A_i, for every mode i *)
	let mode_lmis = List.map (fun a -> ! lambda * unknown_P - (~: !! a) * unknown_P * !! a) a_list in

	(* P - eye *)
	let expr2 = unknown_P - eye in

	let obj = Purefeas in

	let lmis= mode_lmis @ [expr2] in
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
        
      

  (* all in one, lifted to a common Lyapunov function across every mode of
     a (possibly switched) system: same P, same tau, same per-input
     lambda_i's shared by all modes -- only the mode-specific term1 (which
     alone depends on that mode's own A_i, B_i) is replicated once per
     mode. term2 and the lambda_i/mat_n multiplier terms encode global,
     mode-independent hypotheses (x'Px<=1, ||u||_inf<=1) so they're built
     once and reused for every mode's constraint. Sound for arbitrary
     switching between modes (guards are ignored, same over-approximation
     [round]/[shape] already make by dropping input on a single mode). *)
  let affine ?(options=Lmi.default) lin_sys =

    (* Unknowns *)
    let _, unknown_P = Lmi.var_var "P" lin_sys.Dynsys.df in (* the template *)
    let tau_var, _ = Lmi.var_var "tau" 1 in

    let lambda_i n = Lmi.var_var ("lambda_" ^ string_of_int n) 1 in (* a scalar *)

    let modes = get_sys_mats lin_sys in

    (* System *)
    match modes with
    | [] -> assert false (* a lin_t always has at least one mode *)
    | Lin _ :: _ -> Format.eprintf "Linear sys@."; shape lin_sys (* no mode has an input: call shape *)
    | Aff (a0, b0) :: _ -> begin
        Format.eprintf "Affine sys@.";
      let a_b_list =
        List.map
          (function
            | Aff (a, b) -> (a, b)
            | Lin _ ->
              (* A mix of modes with/without input isn't handled: every
                 mode of a lin_t shares the same di, so this shouldn't
                 arise from a well-formed system. *)
              assert false)
          modes
      in
      let dim_p = Mat.nb_lines a0 in
      let nb_inputs = Mat.nb_cols b0 in
      let eye_P = Lmi.eye dim_p in

      (* gives the least lambda fixpoint for a given tau *)
      let compute_tau tau =

	let term1_for (a, b) =
	  let open Lmi in
	  block
	    [|
	      [| -  (~: !! a) * unknown_P * !! a; -(~: !! a) * unknown_P * !! b; zeros dim_p 1 |];
	      [| -(~: !! b) * unknown_P * !! a; -(~: !! b) * unknown_P * !! b; zeros nb_inputs 1 |];
	      [| zeros 1 dim_p; zeros 1 nb_inputs; eye 1|];
	    |]
	in
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
        (* term2 + sum_n(-lambda_n*mat_n): shared, mode-independent extra
           terms, computed once and added to each mode's own term1. *)
        let shared_extra =
          match terms with
          | [] -> term2
          | hd :: tl -> List.fold_left (fun x y -> Lmi.add x y) (Lmi.add term2 hd) tl
        in
        let mode_lmis = List.map (fun ab -> Lmi.add (term1_for ab) shared_extra) a_b_list in

	(* P - lambda eye *)
	let lmi2 = let open Lmi in unknown_P - lambda_id * eye_P in

	let lmis = mode_lmis @ [lmi2] @ lambda_is in  (* All lambda_i are positive *)
	let obj = Lmi.Maximize lambda_id in
	let ret, _, values = Lmi.solve ~options obj lmis in
	if Osdp.SdpRet.is_success ret then
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
