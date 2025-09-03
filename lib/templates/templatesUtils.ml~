module Make (Coeff: Osdp.Scalar.S) =
struct

  let min_digits = 15
  let nb_try = 12
  let error_bound = 12

  let dicho inf sup func =
    let rec dicho inf sup last_ok last_nok last_call_ok nb_digits =
      if nb_digits <= min_digits || ( (not last_call_ok) && nb_digits <= error_bound) then
	let new_pivot = Coeff.add inf (Coeff.div (Coeff.sub sup inf) (Coeff.of_int 2)) in
	let ret, result = func new_pivot in
	match result with
	  | Some _ -> dicho inf       new_pivot (Some (ret, result)) last_nok true  (nb_digits+1)
	  | None ->   dicho new_pivot sup       last_ok              (Some ret)      false (nb_digits+1)
      else
	match last_ok, last_nok with
	  Some result, _ -> result
	| None, Some ret -> ret, None (*raise (Failure "impossible to find such P") *)
	| _ -> assert false (* should never happen *)
    in
    let nb_digits_init = 0 in
    let last_call_ok_init = false in
    dicho inf sup None None last_call_ok_init nb_digits_init
      
  let sampled_search init_tau init_res max_tau compute_tau has_improved =
    let tau_delta = Coeff.div (Coeff.sub max_tau init_tau) (Coeff.of_int nb_try) in
    let rec aux tau res =
      let tau' = Coeff.add tau tau_delta in
      if not(Coeff.lt tau max_tau) then
	match res with Some res -> res  | None -> assert false (* we reached max_tau (=1) *)
      else
	let (tau_ret, tau_res) as new_res = compute_tau tau in
	match res, tau_res with
	| None, None -> assert false
	| Some res, None -> res (* current tau fails, we stop here. Should not happen. *) 
	| None, Some _ -> aux tau' (Some new_res) 
	| Some (_, Some (_, old_values)), Some (_, tau_values) when has_improved tau_values old_values ->
	   aux tau' (Some new_res)
	| Some _, Some _ -> aux tau' res
    in
    aux init_tau (Some init_res)
    
end
  
