module Make (Dynsys: Dynsys.S) = (
  struct
  module Matrix = Dynsys.Mat
  module Lmi = Osdp.Lmi.Make (Matrix)

  let int_ratio i j = Matrix.Coeff.div (Matrix.Coeff.of_int i) (Matrix.Coeff.of_int j)

(* Contents:
   - over-approximation feasible transitions btw cells 
   - quadratization of quards
   - enumerate paths of length up to n
   - for each path, introduce two families of lmis:
     - path is bounded (1 lmi)
     - all transitions from path to cell j constrain the results
     - special cond for path of length one starting in initial cell
*)


(*
    path=paths(i); %first letter of paths(i)
    path=path{1};
    first=path(1);
    first=str2double(first);
    plast=path(length(path));
    plast=str2double(plast);
    
    P{i}=sdpvar(d,d);
    if(nonhom)
        q{i}=sdpvar(d,1);
    else
        q{i}=zeros(d,1);
    end
    M{i}=[0 q{i}';q{i} P{i}];
    W{i}=sdpvar(size(Q{plast},1),size(Q{plast},1));
    Z0{i}=sdpvar(d+1,d+1);
    Const=Const+[M{i}-Q{plast}'*W{i}*Q{plast}+Bound-R==Z0{i},W{i}(:)>=tol,Z0{i}>=0];
    % If the cell i has a non empty intersection with initial conditions
    % then add a new constraint
    if(I(first)==1 && (~all_subpaths || length(path)==1))
        X{i}=sdpvar(size(IL{first},1),size(IL{first},1));
        Z1{i}=sdpvar(d+1,d+1);
        Const=Const+[R-M{i}-IL{first}'*X{i}*IL{first}==Z1{i},X{i}(:)>=tol,Z1{i}>=0];
    end
*)

(*    let lmi_bounded_eq laws_x laws_u laws_a guards_mat guards_vect gamma i=


      let i_str = string_of_int(i) in
      let dim_x = Matrix.nb_cols laws_x in 
      let dim_u = Matrix.nb_cols laws_u in
      let dim_P = dim_x + dim_u in
      let dim_g = Matrix.nb_lines guards_vect in 
      let onehalf = int_ratio 1 2 in 

      (* Convert input matrices *)
      let _T_i = Lmi.const guards_mat in
      let _T_i_t = Lmi.transpose (Lmi.const guards_mat) in
      let c_i_t = Lmi.transpose (Lmi.const guards_vect) in

      (* Unknowns *)
      let beta = "beta"^i_str in
      let mu = Lmi.vector("mu"^i_str,dim_g) in
      let mu_t = Lmi.trans_vector("mu"^i_str,dim_g) in
      let tau = Lmi.vector ("tau"^i_str, (Matrix.nb_cols laws_u)) in
      let unknown_P = Lmi.symmat ("P"^i_str, dim_P) in

      (* Basic blocks *)
      let trans_one_dim_u = Lmi.trans_one dim_u in (*line vector with only 1 *)
      let const1 = Lmi.eye 1 in (*constant scalar equal to 1 *)
      let gammasq = Num.square_num gamma in (*bound on input *)
      let sum_tau = Lmi.mult trans_one_dim_u tau in (*sum of coordinates of tau*) 
      let gsq_tau = Lmi.const_mult gammasq sum_tau in (*gamma^2*Sum_k tau_k*)

      (* let guard_tau = Lmi.mult (Lmi.transpose guards_mat) tau in    *)

      (* \beta^i - (1 + c_i^t \mu^i + \gamma^2 (one^dim_u^t tau^i)) *)
      let term1_1 = 
	Lmi.sub
	  (Lmi.scal_mult beta (Lmi.eye 1)) 
	  (Lmi.add
	     const1
	     (Lmi.add 
		(Lmi.mult c_i_t mu)
		gsq_tau
	     )
	  )
      in

      (* .5 \mu^i^t T_i *)
      let term1_2 = Lmi.const_mult onehalf (Lmi.mult mu_t _T_i) in

      (* .5 T_i^t \mu^i *)
      let term2_1 = Lmi.const_mult onehalf (Lmi.mult _T_i_t mu) in

      (* P_i - Id(dim_P) + [[0(dim_x, dim_x); 0(dim_x, dim_u)]; [0(dim_u, dim_x); \tau^i * Id(dim_u) ]]*)
      let term2_2 = 
	Lmi.add 
	  (Lmi.sub unknown_P (Lmi.eye dim_P))
	  (Lmi.of_array_array [|[|Lmi.zeros dim_x dim_x; Lmi.zeros dim_x dim_u|];
				    [|Lmi.zeros dim_u dim_x;Lmi.mult tau (Lmi.eye dim_u)|]|]) 
      in
      
      let lmi1 = Lmi.of_array_array
	[| [|term1_1 ; term1_2|]; [|term2_1 ; term2_2|] |]
      in
      
      let lmi2 = 
	Lmi.diag [Lmi.scal_mult beta (Lmi.eye 1); mu; tau]
      in
      let lmi = Lmi.diag [lmi1;lmi2] in 
      lmi
  
    let lmi_stability_eq laws_i_x laws_i_u laws_i_a guards_i_mat guards_i_vec guards_j_mat guards_j_vec gamma i j= 
      let i_str = string_of_int(i) in 
      let j_str = string_of_int(j) in
      let i_j_str = i_str^"_"^j_str in 
      let dim_x = Matrix.nb_cols laws_i_x in
      let dim_u = Matrix.nb_cols laws_i_u in
      let dim_gi = Matrix.nb_lines guards_i_mat in
      let dim_gj = Matrix.nb_lines guards_j_mat in
      let onehalf = int_ratio 1 2 in 

      (* Convert input matrices *)
      let _A_i = Lmi.const laws_i_x in
      let _B_i = Lmi.const laws_i_u in
      let _A_i_t = Lmi.transpose laws_i_x in 
      let _B_i_t = Lmi.transpose laws_i_u in 
      let b_i = Lmi.const laws_i_a in 
      let b_i_0 = Lmi.of_array_array [|[|b_i|];[|Lmi.zeros dim_u 1 |]|] in  
      let b_i_t = Lmi.transpose laws_i_a in
      let b_i_0_t = Lmi.of_array_array [|[|b_i_t;Lmi.zeros 1 dim_u|]|] in  
      let _T_i = Lmi.const guards_i_mat in
      let _T_j = Lmi.const guards_j_mat in
      let _T_i_t = Lmi.transpose guards_i_mat in
      let _T_j_t = Lmi.transpose guards_j_mat in 
      let c_i = Lmi.const guards_i_vec in
      let c_j = Lmi.const guards_j_vec in 

      (* Auxilary matrices  *)      
      (* c_ij=[c_i;c_j-T_j*b_i_0] *)
      let c_i_j = Lmi.of_array_array 
	[|
	  [|c_i|];
	  [|Lmi.sub c_j (Lmi.mult _T_j b_i_0) |]
	|] 
      in
      (* F_i=[A_i B_i;0 Id] *)
      let _F_i = Lmi.of_array_array 
	[| 
	  [|_A_i;_B_i|] ;
	  [| Lmi.zeros dim_u dim_x ; Lmi.eye dim_u |] 
	|]  
      in
      (*F_i^t = [A_i^t 0;B_i^t Id] *)
      let _F_i_t = Lmi.of_array_array 
	[| 
	  [| _A_i_t; Lmi.zeros dim_x dim_u |] ;
	  [| _B_i_t; Lmi.eye dim_u |]
	|] 
      in 
      (*M_ij=[T_i;T_j F_i] *)
      let _M_i_j = Lmi.of_array_array [| [|_T_i|]; [|Lmi.mult _T_j _F_i |]|] in
      (*M_ij^t = [T_i F_i_t T_j_t] *)         
      let _M_i_j_t = Lmi.of_array_array [| [|_T_i_t; Lmi.mult _F_i_t _T_j_t|] |] in  
      (* Unknowns *)
      let unknown_Pi = Lmi.symmat("P"^i_str,dim_x+dim_u) in
      let unknown_Pj = Lmi.symmat("P"^j_str,dim_x+dim_u) in
      let beta = "beta"^i_j_str in
      let mu = Lmi.vector("mu"^i_j_str,dim_gi+dim_gj) in 
      let mu_t = Lmi.trans_vector("mu"^i_j_str,dim_gi+dim_gj) in 
      let tau = Lmi.vector("tau"^i_j_str,dim_u) in
      
      (* Basic blocks *)
      let trans_one_dim_u = Lmi.trans_one dim_u in
      let const1 = Lmi.eye 1 in 
      let gammasq = Num.square_num gamma in 
      let sum_tau = Lmi.mult trans_one_dim_u tau in 
      let gsq_tau = Lmi.const_mult gammasq sum_tau in 
      (* let guard_tau = Lmi.mult (Lmi.transpose guards_mat) tau in *)
      
      (* \beta^ij - (1 + \mu^ij^t . c_i_j + \gamma^2 (\one^dim_u^t *\tau^ij)+b_i_0^T Pj b_i_0) *)
      let term1_1 = 
        Lmi.sub
          (Lmi.scal_mult beta (Lmi.eye 1)) 
          (Lmi.add
	     const1
	     (Lmi.add 
	        (Lmi.mult mu_t c_i_j)
                (Lmi.add 
	           gsq_tau
                   (Lmi.mult 
                      b_i_0_t
                      (Lmi.mult
                         unknown_Pj 
                         b_i_0
                      )
                   )
                )
             )                                   
	  )
      in
      (* 0.5 \mu^{ij}^t M^{ij} -b_i_0^t P_j F_i *)
      let term1_2 = Lmi.sub 
        (Lmi.const_mult 
           onehalf 
           (Lmi.mult mu_t _M_i_j)
        )
        (Lmi.mult 
           b_i_0_t
           (Lmi.mult unknown_Pj _F_i)
        ) 
      in 
      (* 0.5  M^{ij}^t\mu^{ij} -F_i^t P_j b_i_0 *)
      let term2_1 = Lmi.sub 
        (Lmi.const_mult
           onehalf
           (Lmi.mult
              _M_i_j_t
              mu
           )
        )
        (Lmi.mult
           _F_i_t
           (Lmi.mult unknown_Pj b_i_0)
        )   
      in
      (* P_i+ [[0(dim_x, dim_x); 0(dim_x, dim_u)]; [0(dim_u, dim_x); \tau^i * Id(dim_u) ]]-F_i^t P_j F_i  *)
      let term2_2 = Lmi.sub  
        (Lmi.add
           unknown_Pi
           (Lmi.diag [Lmi.zeros dim_x dim_x; 
                          Lmi.mult tau (Lmi.eye dim_u)])
        )
        (Lmi.mult
           _F_i_t
           (Lmi.mult unknown_Pj _F_i) 
        )          
      in
      let lmi1 = Lmi.of_array_array [| [|term1_1;term1_2 |];[|term2_1;term2_2 |] |];                      in
      let lmi2 = Lmi.diag [Lmi.scal_mult beta (Lmi.eye 1); mu; tau] 
      in 
      let lmi = Lmi.diag [lmi1;lmi2] in 
      lmi


    let main =
      let lmis_zone_i, _ = List.fold_left (
      fun (accu, cpt) (laws_x, laws_u, laws_a, guards_mat, guards_vect) ->
	let lmi = 
	  Multi_lyapunov.lmi_bounded_eq 
	    laws_x laws_u laws_a guards_mat guards_vect input_bound cpt
	in
	lmi::accu, cpt+1
    ) ([], 1) zone

    in

    let lmis_zone_i_j, _ = 
      List.fold_left (
	fun (accu, cpt_i) (x_i, u_i, a_i, gm_i, gv_i) ->
	  let i_js, _ =
	    List.fold_left (
	      fun (accu2, cpt_j) (_, _, _, gm_j, gv_j) ->
		let lmi = 
		  Multi_lyapunov.lmi_stability_eq 
		    x_i u_i a_i gm_i gv_i gm_j gv_j input_bound cpt_i cpt_j
		in
		(if (cpt_i = 3 && cpt_j = 3 ) then
		    lmi :: accu2 else accu2) , cpt_j + 1
	    ) (accu, 1) zone
	  in
	  i_js, cpt_i + 1
      ) ([], 1) zone

    in


    let lmis = lmis_zone_i  @ lmis_zone_i_j in
    let obj = None in
    let lambda = Num.num_of_int 0 in 
    match Lmi.solve lmis obj with
      ret_v, None -> (
	Format.eprintf 
	  "@.Computing solution for lambda = %a: no result (%f)@?" 
	  Lmi.Mat.pp_elem lambda ret_v
      )
    | ret_v, Some res -> (
      Format.eprintf "@.Computed solution %a@?" 
	(Utils.fprintf_list ~sep:"@." (
	  fun fmt (id, value) ->
	    Format.fprintf fmt "%s: %a"
	      id
	      (fun fmt v -> match v with 
	      | LMI.Scalar s -> Format.pp_print_float fmt (Lmi.Mat.Elem.to_float s)
	      | LMI.Mat m -> Format.fprintf fmt "[@[<hov 2>%a@]]" 
		(Utils.fprintf_list ~sep:"@ " (
		  fun fmt line -> Format.fprintf fmt "[@[<h 2>%a@]]@ " (
		    Utils.fprintf_list ~sep:"@ " (fun fmt e -> Format.pp_print_float fmt (Lmi.Mat.Elem.to_float e))
		  ) line
		 )) (Lmi.Mat.matrix_to_list_list m)
	      ) value
	 )) res;
    )
*)
  let piecewise_lin _ (*k*) _ (*lin_sys*) = assert false
      
end)
