(* Direct LP feasibility check for a system of strict/weak affine
   inequalities, via ocplib-simplex -- a proper bounds-based simplex with
   native strict-vs-weak support (a symbolic epsilon offset on bounds, see
   its Rat2 module: [x > r] is asserted as the bound [r + epsilon]).

   Why this exists: PiecewiseQuadraticTemplates.is_feasible used to answer
   exactly this question (is a cell/switch's guard conjunction satisfiable)
   by routing Motzkin's transposition-theorem alternative through
   Osdp.Lmi's general SDP solver. That alternative system is characterized
   entirely by *equality* constraints (encoded as paired [expr>=0;
   -expr>=0] inequalities, forcing exact zero slack everywhere), with no
   genuine matrix-valued SDP structure to lean on -- a degenerate,
   zero-interior problem that CSDP's interior-point method cannot handle
   (confirmed empirically: it reports "dual infeasible" even for a
   trivially, hand-verifiably feasible input). Solving the *original*
   (primal) feasibility question directly, as a plain LP, sidesteps that
   failure mode entirely instead of working around it -- there's no
   Motzkin duality, no homogenization, no equality-as-inequality-pair
   trick needed at all. *)

module Var = struct
  type t = int

  let compare = Stdlib.compare
  let is_int _ = false
  let print fmt v = Format.fprintf fmt "v%d" v
end

module Ex = struct
  type t = unit

  let empty = ()
  let union () () = ()
  let print _ () = ()
end

module R = struct
  type t = Q.t

  let zero = Q.zero
  let one = Q.one
  let m_one = Q.minus_one
  let sign = Q.sign
  let compare = Q.compare
  let equal = Q.equal
  let is_zero t = Q.sign t = 0
  let is_one = Q.equal Q.one
  let is_m_one = Q.equal Q.minus_one
  let add = Q.add
  let sub = Q.sub
  let div = Q.div
  let mult = Q.mul
  let abs = Q.abs
  let is_int t = Z.equal (Q.den t) Z.one
  let print fmt t = Format.pp_print_string fmt (Q.to_string t)
  let to_string = Q.to_string
  let min = Q.min
  let minus = Q.neg
  let floor t = Q.of_bigint (Z.fdiv (Q.num t) (Q.den t))
  let ceiling t = minus (floor (minus t))
end

module Lp = OcplibSimplex.Basic.Make (Var) (R) (Ex)

(* [is_feasible strict weak d] checks whether there exist real x_0..x_(d-1)
   such that every row [c; a_0; ...; a_(d-1)] in [strict] satisfies
   [c + sum a_i x_i > 0], and every row in [weak] satisfies [c + sum a_i
   x_i >= 0]. Each row has length [d+1] (a constant term followed by one
   coefficient per variable). *)
let is_feasible (strict : Q.t array list) (weak : Q.t array list) (d : int) : bool =
  let open Lp in
  let env = ref (Core.empty ~is_int:false ~check_invs:false) in
  let next_slack = ref d in
  let trivially_infeasible = ref false in
  let assert_row (row : Q.t array) (is_strict : bool) =
    if not !trivially_infeasible then begin
      let c = row.(0) in
      let terms =
        List.filter_map
          (fun i -> let a = row.(i + 1) in if Q.equal a Q.zero then None else Some (i, a))
          (List.init d (fun i -> i))
      in
      match terms with
      | [] ->
        (* constant row, doesn't depend on any variable: either always
           true (drop it) or always false (the whole system is
           immediately infeasible, regardless of every other row) *)
        let ok = if is_strict then Q.sign c > 0 else Q.sign c >= 0 in
        if not ok then trivially_infeasible := true
      | [ (i, a) ] ->
        (* single-variable row: c + a*x_i (>=|>) 0, i.e. x_i (>=|>|<=|<)
           -c/a depending on a's sign (dividing by a negative a flips the
           inequality direction) *)
        let bound_val = Q.div (Q.neg c) a in
        let env', _ =
          if Q.sign a > 0 then
            let bvalue = if is_strict then Core.R2.lower bound_val else Core.R2.of_r bound_val in
            Assert.var !env ~min:{ Core.bvalue; explanation = () } i
          else
            let bvalue = if is_strict then Core.R2.upper bound_val else Core.R2.of_r bound_val in
            Assert.var !env ~max:{ Core.bvalue; explanation = () } i
        in
        env := env'
      | _ :: _ :: _ ->
        (* genuine multi-variable row: bound a fresh slack variable
           standing for [sum a_i x_i] from below by [-c] *)
        let poly = Core.P.from_list terms in
        let slack = !next_slack in
        incr next_slack;
        let bound_val = Q.neg c in
        let bvalue = if is_strict then Core.R2.lower bound_val else Core.R2.of_r bound_val in
        let env', _ = Assert.poly !env poly ~min:{ Core.bvalue; explanation = () } slack in
        env := env'
    end
  in
  List.iter (fun row -> assert_row row true) strict;
  List.iter (fun row -> assert_row row false) weak;
  if !trivially_infeasible then false
  else
    let env = Solve.solve !env in
    (* Solve.solve always resolves UNK to SAT or UNSAT; treating a
       hypothetical residual UNK as feasible mirrors the sound,
       over-approximating default used everywhere else in this codebase
       for an inconclusive solve. *)
    match env.Core.status with Core.UNSAT _ -> false | Core.SAT | Core.UNK -> true
