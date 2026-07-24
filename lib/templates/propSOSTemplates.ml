(* Property-directed polynomial template synthesis via SOS.

   Ported from
   /Users/ploc/Repositories/git/papers/2016-progcertos/script/templatedesignprop.m
   (function templatedesignout, objL1norm=0 path, the only one exercised by
   the paper's example scripts), generalized from Matlab's fixed two-branch
   if/else to Dynsys.poly_t's N-way piecewise map, and from a single global
   guard per branch to a conjunction (as Dynsys.poly_guard_t already is),
   plus universal quantification over a bounded input (Dynsys.di/input),
   which Matlab's script has no equivalent for.

   Given a property kappa(x) and a target degree, searches for a polynomial
   template P and a scalar alpha such that:
   - P(x) >= kappa(x) everywhere (P dominates the property to prove);
   - P is inductive along every mode of the system (doesn't increase
     stepping through any guarded update), optionally strengthened by a
     domain_restriction assumption (matches the paper's gT: a known
     invariant that doesn't itself need to be (re)proved here);
   - P(x) <= alpha on the init region (matches the paper's gC).
   so alpha is a proven bound on kappa(x) over all states reachable from
   the init region, and {x : P(x) - alpha <= 0} is an inductive invariant
   witnessing it. *)

module Make (Dynsys: Dynsys.S) =
struct
  module Poly = Dynsys.Poly
  module Sos = Osdp.Sos.Make (Dynsys.Poly)

  (* Round a nonnegative degree up to the nearest even number, matching
     Matlab's 2*ceil(d/2): the degree of an SOS polynomial is always even. *)
  let ceil2 d = 2 * ((d + 1) / 2)

  (* Degree to give a fresh SOS multiplier so that [multiplier * constraint]
     can reach [target_deg] (Matlab's 2*k0-dj / 2*ceil(degTP/2)-2*ceil(deg r/2)
     pattern). Clamped to 0 (constant multiplier) if the constraint is
     already at or above the target degree. *)
  let multiplier_deg target_deg constraint_deg =
    max 0 (ceil2 target_deg - ceil2 constraint_deg)

  (* P(T(x)): substitutes each of P's df variables by the corresponding
     component of T (a concrete polynomial update), expanding monomial by
     monomial rather than using Sos.Compose. This mirrors the paper's own
     manual "PT" construction (templatedesignout.m loops over P's monomial
     basis and multiplies each coefficient by the corresponding power of T)
     -- and sidesteps a real osdp limitation: [Sos.solve] can raise
     [Not_found] internally (in PreSdp's sparse conversion) when a
     [Compose]-containing constraint is solved alongside a [Minimize]
     objective on a variable that doesn't itself appear inside that
     [Compose] (confirmed with a minimal repro against osdp directly; not
     specific to this system). *)
  let substitute df (p_expr : Sos.polynomial_expr) (update : Poly.t array) =
    (* Note: avoids Sos's local-open operators here since its [(!)] means
       "const from coeff", clashing with plain ref dereference. *)
    List.fold_left
      (fun acc (m, coeff) ->
        let degs = Array.make df 0 in
        List.iteri (fun i d -> if i < df then degs.(i) <- d) (Osdp.Monomial.to_list m);
        let term = ref coeff in
        for k = 0 to df - 1 do
          if degs.(k) > 0 then
            term := Sos.mult !term (Sos.power (Sos.const update.(k)) degs.(k))
        done;
        Sos.add acc !term)
      (Sos.const Poly.zero)
      (Sos.to_list p_expr)

  (* Bisection search for the minimal feasible alpha, replacing a single
     [Sos.Minimize alpha] solve.

     Why: minimizing alpha directly pushes the solver's interior-point
     iteration right up against the true optimum -- exactly where the SOS
     problem becomes numerically degenerate. In practice (confirmed by
     hand against this same encoding) csdp's Cholesky factorization can
     fail to converge there ("Factorization of the system matrix failed")
     even though the problem is perfectly well-posed and solves cleanly
     via [Purefeas] at concrete alpha values comfortably on either side of
     that boundary. [alpha - P - sum s_j.g0_j >= 0] is monotonic in alpha
     (increasing alpha only relaxes it), so the minimal feasible alpha can
     be found by a standard galloping-then-bisection search over
     [Purefeas] checks instead -- the same style of search already used
     by [QuadraticTemplates.shape]/[affine] (see [TemplatesUtils.dicho]),
     just without requiring an a priori bracket: it gallops outward from 0
     (in whichever direction is needed) to find one, then bisects it down.
     [bracket_steps]/[bisect_steps] mirror [TemplatesUtils]'s own
     precision choices (12 / 15). *)
  let bracket_steps = 12
  let bisect_steps = 15

  let search_alpha (feasible : Sos.Poly.Coeff.t -> Osdp.SdpRet.t * Sos.Poly.t option) =
    let module C = Sos.Poly.Coeff in
    let two = C.of_int 2 in
    let rec grow delta n =
      if n <= 0 then None
      else
        match feasible delta with
        | ret, Some p -> Some (delta, ret, p)
        | _, None -> grow (C.mult delta two) (n - 1)
    in
    match
      match feasible C.zero with
      | ret, Some p -> Some (C.zero, ret, p)
      | _, None -> grow C.one bracket_steps
    with
    | None -> Osdp.SdpRet.Unknown, None
    | Some (hi0, ret0, p0) ->
      (* Gallop downward from the known-feasible hi0 until infeasible,
         tightening hi to the smallest feasible point found along the way. *)
      let rec gallop_down delta lo hi ret p n =
        if n <= 0 then lo, hi, ret, p
        else
          let cand = C.sub hi delta in
          match feasible cand with
          | ret', Some p' -> gallop_down (C.mult delta two) lo cand ret' p' (n - 1)
          | _, None -> cand, hi, ret, p
      in
      let lo, hi, ret, p = gallop_down C.one hi0 hi0 ret0 p0 bracket_steps in
      let rec bisect lo hi ret p n =
        if n <= 0 then hi, ret, p
        else
          let mid = C.div (C.add lo hi) two in
          match feasible mid with
          | ret', Some p' -> bisect lo mid ret' p' (n - 1)
          | _, None -> bisect mid hi ret p (n - 1)
      in
      let alpha, ret, p = bisect lo hi ret p bisect_steps in
      ret, Some Poly.(p - const alpha)

  (* Default property when none is supplied: the squared norm of the
     state, sum_i x_i^2. Dominating it (P >= kappa) and bounding P by
     alpha on init then gives ||x||^2 <= alpha over all reachable states,
     i.e. a single ball bound from which every state variable is directly
     bounded (|x_i| <= sqrt alpha) -- a cheap one-solve alternative to
     calling this same method once per variable/direction with
     kappa = +/- x_i. *)
  let default_kappa df =
    List.fold_left
      (fun acc i -> Sos.(acc + ??i ** 2))
      Sos.( !Sos.Poly.Coeff.zero )
      (List.init df (fun i -> i))

  let template
      ?(domain_restriction : Dynsys.basic_semialgebraic_t = [])
      ?solver (* None: let osdp pick its own default (Sos.default.sdp.solver) *)
      ?kappa (* None: default to [default_kappa] (squared norm of the state) *)
      (sys : Dynsys.poly_t)
      (deg : int) =
    let df = sys.Dynsys.df in
    let kappa = match kappa with Some k -> k | None -> default_kappa df in
    let p_expr = Sos.make ~n:df ~d:deg "P" in
    let zero = Sos.( !Sos.Poly.Coeff.zero ) in

    (* Init (matches gC): alpha - P - sum_j s_j.g0_j must be SOS, each s_j SOS.
       alpha itself is a concrete value plugged in by search_alpha, not a
       free decision variable (see search_alpha above for why). *)
    let init_multipliers, init_terms =
      List.fold_left
        (fun (mults, terms) g0_j ->
          let d = multiplier_deg deg (Poly.degree g0_j) in
          let s_j = Sos.make ~n:df ~d "sC" in
          s_j :: mults, Sos.(terms + s_j * Const g0_j))
        ([], zero) sys.Dynsys.init
    in

    (* Per mode (guard_i, update_i): P - P(T_i) - sum Gamma_ij.guard_ij
       - sum Q_ik.domain_k - sum H_ik.input_k must be SOS *)
    let mode_multipliers, mode_constraints =
      List.fold_left
        (fun (mults, constraints) (guard_i, update_i) ->
          let deg_t_i =
            Array.fold_left (fun d u -> max d (Poly.degree u)) 0 update_i
          in
          let deg_tp_i = deg_t_i * deg in
          let pt_i = substitute df p_expr update_i in
          let mults, guard_terms =
            List.fold_left
              (fun (mults, terms) g ->
                let d = multiplier_deg deg_tp_i (Poly.degree g) in
                let gamma = Sos.make ~n:df ~d "Gamma" in
                gamma :: mults, Sos.(terms + gamma * Const g))
              (mults, zero) guard_i
          in
          let mults, domain_terms =
            List.fold_left
              (fun (mults, terms) d_k ->
                let d = multiplier_deg deg_tp_i (Poly.degree d_k) in
                let q = Sos.make ~n:df ~d "Q" in
                q :: mults, Sos.(terms + q * Const d_k))
              (mults, zero) domain_restriction
          in
          let mults, input_terms =
            match sys.Dynsys.input with
            | None -> mults, zero
            | Some input_l ->
              List.fold_left
                (fun (mults, terms) h_k ->
                  let d = multiplier_deg deg_tp_i (Poly.degree h_k) in
                  let h = Sos.make ~n:df ~d "H" in
                  h :: mults, Sos.(terms + h * Const h_k))
                (mults, zero) input_l
          in
          let cons = Sos.(p_expr - pt_i - guard_terms - domain_terms - input_terms) in
          mults, cons :: constraints)
        ([], []) sys.Dynsys.map
    in

    (* Property: P - kappa must be SOS, unconditioned (matches the paper:
       sos(P - kappa) carries no multiplier). *)
    let prop_constraint = Sos.(p_expr - kappa) in

    let base_constraints =
      mode_constraints @ [ prop_constraint ] @ init_multipliers @ mode_multipliers
    in
    let options = Sos.({ default with pad = 0.; scale = false }) in

    (* Osdp.Sos.solve can itself raise Not_found for certain constraint
       combinations, from a bug in its preSdp.ml constraint-elimination
       preprocessing (a variable can get eliminated in terms of another,
       already-eliminated variable that was never re-substituted into its
       definition, so it's later missing from the solved result map;
       fixed upstream in osdp, kept here as a defensive fallback in case
       an older osdp is linked). Caught so it degrades to an infeasible
       result for that particular alpha instead of crashing the caller. *)
    let feasible alpha_val =
      let init_constraint = Sos.(Const (Poly.const alpha_val) - p_expr - init_terms) in
      match
        Sos.solve ~options ?solver Sos.Purefeas (init_constraint :: base_constraints)
      with
      | exception Not_found -> Osdp.SdpRet.Unknown, None
      | ret, _obj, vars, _witnesses ->
        if Osdp.SdpRet.is_success ret then
          (try ret, Some (Sos.value_poly p_expr vars) with Not_found -> ret, None)
        else ret, None
    in
    search_alpha feasible
end
