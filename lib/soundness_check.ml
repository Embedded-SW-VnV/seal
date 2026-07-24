(* Empirical soundness checking: given an analysis result's claimed
   invariant (a Dynsys.semialgebraic_t) and a set of simulated/sampled state
   points, check whether any point violates it.

   Sign convention: a Dynsys.semialgebraic_t used as an analysis *result* is
   a DNF of conjunctions of [p_i(x) <= 0] (see Analysis.pp_basic_semialg,
   the only place this convention is pinned down in code -- init/input/guard
   uses of the same [basic_semialgebraic_t] type go the other way, [p_i(x)
   >= 0], see Polynomial_examples.ml's header comment). A point is "inside"
   the invariant if *some* disjunct has *every* conjunct <= 0. *)

module Make (Dynsys : Dynsys.S) = struct
  module Sim = Simulate.Make (Dynsys)

  let eval_state p state = Sim.eval p state [||]

  type violation = { point : float array; value : float }

  type result = {
    n_checked : int;
    n_in_domain : int;
    violations : violation list;
    worst : violation option;
  }

  let sound (r : result) = r.violations = []

  (* Smallest, over disjuncts, of the worst (max) conjunct value within that
     disjunct: <= 0 means some disjunct is fully satisfied (point covered by
     the invariant); > 0 is the violation's magnitude. *)
  let violation_degree (sa : Dynsys.semialgebraic_t) (state : float array) : float =
    match sa with
    | [] -> infinity
    | _ ->
      List.fold_left
        (fun best conj ->
          let worst_conjunct =
            List.fold_left (fun acc p -> max acc (eval_state p state)) neg_infinity conj
          in
          min best worst_conjunct)
        infinity sa

  let check ?(domain = fun (_ : float array) -> true) ?(tol = 1e-6)
      (sa : Dynsys.semialgebraic_t) (points : float array list) : result =
    let in_domain = List.filter domain points in
    let violations =
      List.filter_map
        (fun state ->
          let d = violation_degree sa state in
          if d > tol then Some { point = state; value = d } else None)
        in_domain
    in
    let worst =
      List.fold_left
        (fun best v ->
          match best with
          | Some b when b.value >= v.value -> best
          | _ -> Some v)
        None violations
    in
    { n_checked = List.length points; n_in_domain = List.length in_domain; violations; worst }

  (* Domain restrictions, for analyses whose claim only holds on a
     sub-region (e.g. liouville_method's invariant is only claimed within
     the r_g-ball it was computed on). *)
  let within_ball ~center ~radius (state : float array) =
    let d2 = Array.fold_left (fun acc (x, c) -> acc +. ((x -. c) ** 2.)) 0.
        (Array.map2 (fun x c -> (x, c)) state center)
    in
    d2 <= radius *. radius

  let within_origin_ball ~radius (state : float array) =
    within_ball ~center:(Array.make (Array.length state) 0.) ~radius state

  (* [p_i(x) >= 0] convention (guards/init/input), for filtering points to a
     piecewise_lin path's guard region. *)
  let within_conjunction ?(tol = 1e-6) (conj : Dynsys.basic_semialgebraic_t)
      (state : float array) =
    List.for_all (fun p -> eval_state p state >= -.tol) conj

  let pp_point fmt (p : float array) =
    Format.fprintf fmt "[%s]"
      (String.concat "; " (Array.to_list (Array.map (Printf.sprintf "%.6g") p)))

  let pp_result fmt (r : result) =
    if sound r then
      Format.fprintf fmt "PASS (%d/%d in-domain points checked)" r.n_in_domain r.n_checked
    else
      match r.worst with
      | None -> assert false
      | Some w ->
        Format.fprintf fmt "FAIL: %d/%d in-domain points violated (worst=%.6g at %a)"
          (List.length r.violations) r.n_in_domain w.value pp_point w.point
end
