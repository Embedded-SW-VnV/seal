(* Liouville-based reachable-states over-approximation.

   Given a piecewise-polynomial discrete dynamical system and a target
   degree, searches for two polynomials v and w such that v is inductive
   along every mode (alpha.v(f(x)) >= v(x) on the guarded region) and w
   dominates v plus a constant on the domain, so that {x : w(x) <= 0}
   over-approximates the states reachable from dynsys.init.

   Ported from
   /Users/ploc/Repositories/git/cavale/measuressos/code/ocaml/reachable_states.ml.

   Kept separate from PropSOSTemplates (the Positivstellensatz-style
   property-directed template search in this same directory): the two rely
   on different techniques (this one minimizes a moments-based volume proxy
   rather than searching for a template dominating a given property), and
   this file may eventually be unified with the similar moments-based
   approach in saimcop/code/approx (which has no Liouville equation of its
   own).

   KNOWN ISSUE (documented, not fixed): checked against this exact
   encoding's own source paper (the "Image measure method" chapter,
   Problem (eq:lpstrength): v = sigma_0 - sum sigma_j^0 r_j^in; w-1-v =
   sigma_1 - sum sigma_j^1 r_j^X; alpha.v(f(x))-v = sigma_2 - sum sigma_j^2
   r_j^X; w = sigma_3 - sum sigma_j^3 r_j^X; minimize the volume of w)
   equation by equation, including the same r_j<=0 vs this codebase's
   g_j>=0 sign flip already noted in PropSOSTemplates.ml -- [compute]'s
   [_Q1l]/[_Q2]/[_Q3]/[_Q4] and its [volume_fun w_elems] minimization
   objective are a faithful implementation of that problem. Yet
   empirically (see examples/full_check_main.ml's sweep) the returned w
   measurably violates w<=0 on Henrion1/Pierre1/Thao8.3, with violations
   in the modest-but-nonzero 0.08-0.63 range (much smaller than
   PropSOSTemplates.ml's blowups, plausibly because this method already
   has a shrink/unshrink normalization the other one lacks -- see below --
   but not eliminated by it).

   One concrete inconsistency was found and tested: [g0] (the init region,
   just below) is used as-is, unlike every other set here (guards, the
   domain ball) which are explicitly rescaled to the same shrunk
   y=x/r_g coordinate system that [v]/[w] and the whole SOS problem are
   solved in via [transform_poly] (see [shrinked_map] just below and
   [unshrink_poly] at the end of [compute]). For any system with r_g != 1
   this means the "v>=0 on init" constraint is, as literally encoded, a
   constraint on the WRONG scale (Thao8.3's init ball, r_g=3, ends up
   asserted at its original radius/center directly against the shrunk y
   coordinates instead of being scaled down by r_g first).

   Tested the obvious fix (wrapping [g0] in the same [transform_poly g
   r_g dynsys.df] as the guards get): it left Henrion1 unchanged (r_g=1,
   so the transform is an identity there, as expected) and, more
   tellingly, left Pierre1's low-degree violations completely unchanged
   too (its actual worst violating point sits at ~(6e-7,-1e-6), deep
   inside both the original and the correctly-shrunk init ball alike --
   nowhere near the boundary that scaling would affect), while newly
   breaking Pierre1's higher degrees (Unknown/no result where the
   original code found a valid, passing certificate) and giving mixed
   results on Thao8.3 (better at some degrees, worse at others) --
   probably because correctly shrinking Pierre1's already-tiny init ball
   (radius 1e-4, r_g=30) down further (to ~3e-6) makes that S-procedure
   constraint itself nearly degenerate for CSDP. So this inconsistency is
   real, but it isn't the (or at least isn't the whole) explanation for
   the observed violations, and a narrow local fix trades one failure
   mode for another instead of clearly improving things -- left as-is,
   flagged here rather than patched in isolation.

   The likely dominant cause is the same monomial-basis/solver-precision
   conditioning problem diagnosed in detail in PropSOSTemplates.ml: even
   with the domain X's own shrink/unshrink normalization already in place
   here, a degree-10 polynomial's high-power terms still amplify whatever
   residual CSDP's [PartialSuccess] solutions carry (nearly every failing
   row here is [PartialSuccess], and even the two [Success] rows still
   show small violations). Not fixed; reproduces the same still-unresolved
   soundness investigation as PropSOSTemplates.ml. *)

module Make (Dynsys: Dynsys.S) =
struct
  module Sos = Osdp.Sos.Make (Dynsys.Poly)
  include Utils_poly.Make (Sos)

  type params = {
    alpha: float;
    padding: float;
    deg: int;
    solver: Osdp.Sdp.solver option; (* None: let osdp pick its own default (Sos.default.sdp.solver) *)
    hypercube_mode: bool;
  }

  type result = {
    v: Sos.Poly.t;
    w: Sos.Poly.t;
    ret: Osdp.SdpRet.t;
  }

  (* Main options *)
  let purefeas = false (* do not optimize for volume, just check purefeas *)
  let min_volume_on_v = false (* activate the SOS cons vol v > 1 *)
  let sos_verbose = 0
  let sdp_verbose = 0
  let null_on_fixpoint = false (* if true, then the inductiveness prop is enforced
				   over v' = ||x -f(x)||_2^2 v *)
  let debug = true

  (* Default values *)
  let default_params =
    {
      alpha = 2.;
      padding = 0.;
      deg = 2;
      solver = None;
      hypercube_mode = false;
    }

  let cst_liouville = 1.

  let xi idx =
    Sos.Const (Sos.Poly.of_list ([Osdp.Monomial.var idx, C.one]))

  (* Returns the semi albegraic definition of the compact set considered and the
     volume function per monomial *)
  let compact_definition p sv =
    let dim = Array.length sv in
    let volume moments elems =
      List.fold_left
        (fun accu (m, w_c) ->
          let coeff = C.of_float (moments m dim) in
          let coeff = Sos.Mult_scalar (coeff, Sos.( !(C.one) )) in
          Sos.( accu + coeff * w_c )
        )
        zero
        elems
    in

    if p.hypercube_mode then
      let g1_l = hypercube sv in
      let _X_relax name target_deg =
        let vl, e, _ =
          List.fold_left (fun (multipliers_l, expr, idx) v_cons ->
              let sos_multiplier = Sos.make ~n:dim ~d:(target_deg-2) name in
              let sos_expr = Sos.( sos_multiplier * v_cons ) in
              sos_multiplier::multipliers_l, Sos.( expr + sos_expr ), idx+1
            ) ([], Sos.( !C.zero ), 1) g1_l
        in
        vl, e
      in
      _X_relax, volume Moments.volume_hypercube

    else (* Ball mode *)
      let g1 = centered_ball sv 1.0 in
      let _X_relax name target_deg =
        let sos_multiplier = Sos.make ~n:dim ~d:(target_deg-2) name in
        let sos_expr = Sos.( sos_multiplier * g1 ) in
        [sos_multiplier], sos_expr
      in

      _X_relax, volume Moments.volume_ball

  (** Liouville version: overapproximate reachable states *)

  (* considering the function maps from X -> Y
     and defined by a vector of function f_i: X -> R
     where maps=(f_i)_n  and n = dim(Y)

     We compute the image of the semialgebraic set setx by maps.

     This computation is restricted to the ball of radius r_gX of X: setx cap ball_rgX
     and the image restricted to the ball of radius r_gY
  *)
  let compute ?(params=default_params) (dynsys:Dynsys.poly_t) =
    let r_g = match dynsys.Dynsys.r_g with
      | Some x -> x
      | None -> assert false in (*TODO cannot applyt that method if not provided with a bound on states *)
    let deg = params.deg in
    let alpha_sos = Sos.(Const (Poly.mult_scalar (C.of_float params.alpha) Poly.one)) in
    let cst_liouville_sos = Sos.(Const (Poly.mult_scalar (C.of_float cst_liouville) Poly.one)) in

    (* Building sys vars: x0 to x_{df-1} *)
    let sys_vars = Array.init dynsys.Dynsys.df (fun idx -> xi idx)
    in
    (* Building input vars: x_df to x_{df+di-1} *)
    let _ (*input_vars*) = Array.init dynsys.di (fun idx -> xi (dynsys.df + idx)) in
    (* let all_vars = Array.append sys_vars input_vars in *)

    (* Main compact
       - either a ball: centered in 0, radius 1, on sys vars
       - or an hypercube: [-1;1]^on sys vars *)
    let _X_relax, volume_fun = compact_definition params sys_vars in

    (* Input ball: centered in 0, radius r_gi, on input vars *)
    (* TODO *)
    (*let gin = centered_ball input_vars dynsys.r_gi in *)

    (* Init vall: centered in init, radius r_g0, on sys_vars *)
    let g0 = (* ball sys_vars (\* TODO remettre la contrainte dynsys.r_g0 *\) 0.25 *) dynsys.init in

    (* Compute a shrinked version of map *)
    let shrinked_map =
      List.map (fun (gl, f) ->
          (* All occurences of sys_vars in guard are scaled by r_g. They are stored /shrinked/ *)
          let unshrink_gl = List.map (fun g -> transform_poly(*_expr*) g r_g dynsys.df ) gl in
          let shrink_f = List.map (fun f_i -> transform_poly f_i r_g (dynsys.df:int)) (Array.to_list f) in
          unshrink_gl, shrink_f
        ) dynsys.map
    in

    let pp_map fmt l =
      let pp_switch fmt (polyexpr_l, poly_l) =
        Format.fprintf fmt "%a -> [%a]"
          (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt " and ") Sos.Poly.pp) polyexpr_l
          (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ";@ ") Sos.Poly.pp) poly_l
      in
      List.iter (pp_switch fmt) l
    in
    Format.eprintf "Orig     map: %a@." pp_map (List.map (fun (gl,up) -> gl, Array.to_list up) dynsys.map);
    Format.eprintf "Shrinked map: %a@." pp_map shrinked_map;

    (* Declaring polynomial variables v and w over sys vars *)

    let v = Sos.make ~n:dynsys.df ~d:deg "v" in
    let v_elems = Sos.to_list v in
    let w = Sos.make ~n:dynsys.df ~d:deg "w" in
    let w_elems = Sos.to_list w in

    (* (\* Filtering out odd monomials from v and w *\) *)
    (* let v, _ = filter_odd_polyvar v_elems in *)
    (* let w, w_elems = filter_odd_polyvar w_elems in *)

    (* Declaration of multipliers *)

    (* Fold_right to preserve the order. N-th element corresponds to n-th piecewise def *)
    let multipliers, xi_relax_l, input_relax_l =
      List.fold_right (fun (gl,_) (multipliers, xi_relax_l, input_relax_l) ->
          let q13, _X_relax_expr = _X_relax "q13" deg in
          let q11l, xi_relax =
            List.fold_left (fun (q11l, accu) g ->
                let q11 = Sos.make ~n:(dynsys.df+dynsys.di) ~d:(deg(* TODO -(degree g)*)) "q11" in
                q11l, Sos.( accu + q11 * Const g )
              ) ([], _X_relax_expr) gl
          in
          let multipliers = q13@q11l@multipliers in
          let xi_relax_l = xi_relax::xi_relax_l in
          let multipliers, input_relax_l =
            match dynsys.input with
            | None -> multipliers, input_relax_l
            | Some gin_l -> (* TODO: shall we declare fresh q12 and q13 for each element ? *)
              List.fold_left (fun (multipliers, input_relax_l) gin ->
                  let q12 = Sos.make ~n:(dynsys.df+dynsys.di) ~d:(deg-2) "q12" in
                  let input_relax = Sos.( q12 * Const gin ) in
                  q12::multipliers, input_relax::input_relax_l
                ) (multipliers, input_relax_l) gin_l
          in
          multipliers, xi_relax_l, input_relax_l
        ) shrinked_map ([], [], [])
    in

    (**** Main constraints:
	  alpha v o f - v >= 0 on X (piecewise definition (f_i, X_i))
	  v >= 0 on Init
	  w >= cst ° v on X
	  w >= 0 on X
    ****)

    let _Q1l =
      List.mapi (
        fun idx (_ (*g*), f) ->
          let v' = if null_on_fixpoint then
              let x_minus_f_2 =
                norm2_square
                  (List.map2
                     (fun v f_i -> let f_i = Sos.Const f_i in try Sos.( v -f_i ) with _ -> assert false)
                     (Array.to_list sys_vars) f
                  )
              in
              Sos.( x_minus_f_2 * v )
            else v
          in
          let vf = try Sos.(Compose (v', List.map (fun p -> Const p) f)) with _ -> assert false in
          let xi_relax = List.nth xi_relax_l idx in
          if dynsys.di > 0 then (* alpha vf >= v on (X cap X_i) x X_input *)
            let input_relax = List.nth input_relax_l idx in
            Sos.( alpha_sos*vf -v' - xi_relax - input_relax )
          else  (* alpha vf >= v on (X cap X_i) *)
            Sos.( alpha_sos*vf -v' - xi_relax )
      ) shrinked_map
    in

    (* v >= 0 on ball init *)
    let _, q21l, expr = List.fold_left (fun (cpt, q21l, accu) g0_i ->
        let q21_i = Sos.make ~n:dynsys.df ~d:(deg-2) ("q21_" ^ string_of_int cpt) in
        cpt+1, q21_i::q21l, Sos.( accu + q21_i * Const g0_i )
      ) (1, [], Sos.Const Sos.Poly.zero) g0 in
    let _Q2= Sos.( v - expr ) in

    (* w >= cst + v on X *)
    let q31, _X_relax_expr_31 = _X_relax "q31" deg in
    let _Q3= Sos.( w - cst_liouville_sos - v - _X_relax_expr_31 ) in

    (* w >= 0 on X *)
    let q41, _X_relax_expr_41 = _X_relax "q41" deg in
    let _Q4= Sos.( w - _X_relax_expr_41 ) in

    (**** This part is optionnal and activate only with option min_volume *****)
    let vol_v = volume_fun v_elems in
    let _Q5= Sos.( vol_v - !C.one ) in        (* vol_X v  >= cst, here cst = 1 *)
    (**** This part is optionnal and activate only with option min_volume *****)

    (* Building constraint list *)
    let constraints =
      _Q1l @ [_Q2; _Q3; _Q4]                    (* main constraints *)
      @ (if min_volume_on_v then [_Q5] else []) (* optional feature *)
      @ (q21l@q31@q41@multipliers)            (* SOS multipliers *)
    in

    let goal = volume_fun w_elems in

    if debug then begin
      let _ = Format.printf "Goal = %a@." Sos.pp goal in
      let _ = List.iter (fun cons -> Format.printf "Cons: %a (deg=%i, nbvars=%i)@."
                             Sos.pp cons
                             (Sos.degree cons)
                             (Sos.nb_vars cons)
                         ) constraints in
      ()
    end;

    let ret, (pobj, dobj), vars, _ =
      Sos.solve
        ~options:(Sos.({ default with
                          pad = params.padding;
                          scale = false;
                          verbose = sos_verbose;
                          sdp = {
                            default.sdp with Osdp.Sdp.verbose=sdp_verbose
                          }
                        }))
        ?solver:params.solver
        (if purefeas then Sos.Purefeas else Sos.Minimize goal)
        constraints
    in

    let () = Format.printf "ret = %a@." Osdp.SdpRet.pp ret in
    let () = Format.printf "pobj, dobj = %g, %g@." pobj dobj in

    (* w is replaced by w - cst to simplify the following use of it as a simple O-superlevel set *)
    let w = Sos.( w - cst_liouville_sos ) in

    try
      (* Obtain the polynomial result. This may fail is a failure has occured *)
      let v_val = Sos.value_poly v vars in
      let w_val = Sos.value_poly w vars in

      if debug then begin
        Format.printf "v=%a@." Sos.Poly.pp v_val;
        Format.printf "w=%a@." Sos.Poly.pp w_val;
      end;

      (* Unscale v and w *)

      let v_val = unshrink_poly v_val r_g dynsys.df in
      let w_val = unshrink_poly w_val r_g dynsys.df in

      if debug then begin
        Format.printf "v=%a@." Sos.Poly.pp v_val;
        Format.printf "w=%a@." Sos.Poly.pp w_val;
      end;

      Some {
        v = v_val;
        w = w_val;
        ret = ret;
      };
    with Not_found -> (
        Format.printf "SDP error.@.";
        None
      )
end
