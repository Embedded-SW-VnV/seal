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
    (* [best] tracks the best *affine-search* candidate found so far, kept
       separate from [init_res] (typically shape's driftless-only result):
       comparing via [has_improved] only ever makes sense between two
       results produced by the same [compute_tau], since the value it reads
       (e.g. quadraticTemplates.ml's lambda_id) can mean something entirely
       different in [init_res] (there, it's whatever the caller stashed
       under that slot for its own bookkeeping). Comparing against
       [init_res] directly here previously made [has_improved] compare
       incompatible quantities, silently discarding every genuine solution
       found by [compute_tau] in favor of [init_res]. Falling back to
       [init_res] only happens once, at the very end, and only if no tau in
       the whole range yielded any feasible result at all. Also: a single
       infeasible tau no longer aborts the whole search (every tau in
       [init_tau, max_tau) is still tried). *)
    let rec aux tau best =
      let tau' = Coeff.add tau tau_delta in
      if not(Coeff.lt tau max_tau) then
	match best with Some res -> res | None -> init_res
      else
	let (_ (*tau_ret*), tau_res) as new_res = compute_tau tau in
	match best, tau_res with
	| None, None -> aux tau' None
	| None, Some _ -> aux tau' (Some new_res)
	| Some _, None -> aux tau' best
	| Some (_, Some (_, old_values)), Some (_, tau_values) when has_improved tau_values old_values ->
	   aux tau' (Some new_res)
	| Some _, Some _ -> aux tau' best
    in
    aux init_tau None
    
end
  
