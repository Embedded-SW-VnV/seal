(* Full soundness/regression sweep across every Analysis method, every
   example system, every degree/k parameter the method is parametrized by,
   and (via the CLI's pad-mode argument) either pad=0 (the paper/Matlab
   experiments' setting, less conservative) or each method's own regular
   default (round/shape/affine/piecewise_lin: Osdp.Lmi.default's pad=2.;
   prop_driven_sos_lyap/liouville_method: their own existing default of 0.,
   already the "sound" choice they were shipping with before this ?pad
   plumbing existed -- see PropSOSTemplates.template's and
   Liouville.default_params's own doc comments). For each (example, method,
   parameter) combination:
     1. forward-simulate concrete trajectories from the example's init
        region (Simulate.run) as ground truth to check against;
     2. compute the invariant (and, for prop_driven_sos_lyap, per-axis
        bounds via kappa=+/-x_i, at one representative degree, since a full
        bounds sweep at every degree would multiply the already-heavy SOS
        solve count);
     3. check the invariant against the simulated points
        (Soundness_check.check) and record status/runtime/validity/the
        invariant itself as one CSV row.

   Two systems (piecewise_lin's k-induction, and the SOS-degree-parametrized
   methods on the 3-state "perin" example) can blow up combinatorially/in
   solve time -- see [max_paths] and [perin_max_degree] below for the
   deliberate, documented caps kept for this to stay a routine, runnable
   sanity check rather than an hours-long solve; both are still exercised up
   to the requested k=4 / degree=10 where that stays tractable. *)

module Sys = Seal.Dynsys.Float
module Ana = Seal.Analysis.Make (Sys)
module Sim = Seal.Simulate.Make (Sys)
module Check = Seal.Soundness_check.Make (Sys)
module PQuad = Seal.PiecewiseQuadraticTemplates.Make (Sys)

let pf = Printf.printf

(* ---------------------------------------------------------------- *)
(* CSV plumbing *)

type record = {
  example : string;
  method_ : string;
  param : string;
  pad_mode : string;
  status : string;
  runtime_s : float;
  valid : string; (* PASS | FAIL | N/A | SKIPPED *)
  n_checked : int;
  n_in_domain : int;
  n_violations : int;
  worst_violation : string;
  invariant : string;
  note : string;
}

let records : record list ref = ref []

let csv_escape s =
  if String.exists (fun c -> c = ',' || c = '"' || c = '\n' || c = '\r') s then
    "\"" ^ String.concat "\"\"" (String.split_on_char '"' s) ^ "\""
  else s

let csv_header =
  "example,method,param,pad_mode,status,runtime_s,valid,n_checked,n_in_domain,n_violations,worst_violation,invariant,note"

let csv_row r =
  String.concat ","
    [ csv_escape r.example; csv_escape r.method_; csv_escape r.param; csv_escape r.pad_mode;
      csv_escape r.status; Printf.sprintf "%.4f" r.runtime_s; csv_escape r.valid;
      string_of_int r.n_checked; string_of_int r.n_in_domain; string_of_int r.n_violations;
      csv_escape r.worst_violation; csv_escape r.invariant; csv_escape r.note ]

(* Opened once, right after CLI args are parsed (see [main] below), and
   appended to as each row is produced -- not buffered in memory and
   written once at the end. A single sweep can run for a very long time
   (some individual SDP solves take minutes, see affine's dichotomy
   search), so a row must survive a kill/crash partway through rather than
   being silently lost. *)
let csv_channel : out_channel option ref = ref None

let open_csv path =
  let oc = open_out path in
  output_string oc (csv_header ^ "\n");
  flush oc;
  csv_channel := Some oc

(* Printed (and appended to the CSV) as each row is produced, not just at
   the end: with the SDP solves dominating runtime, a routine `make
   full-check` run needs live progress feedback rather than long silences
   broken only by the library's own unrelated debug eprintfs. *)
let add r =
  Printf.printf "  [%-8s] %-24s %-24s %-28s status=%-14s %6.2fs %s\n%!"
    r.pad_mode r.example r.method_ r.param r.status r.runtime_s r.valid;
  (match !csv_channel with
   | Some oc -> output_string oc (csv_row r ^ "\n"); flush oc
   | None -> ());
  records := r :: !records

(* ---------------------------------------------------------------- *)
(* Small helpers shared by every method group *)

let time_it f =
  let t0 = Unix.gettimeofday () in
  let x = f () in
  let t1 = Unix.gettimeofday () in
  (x, t1 -. t0)

let status_str status = Format.asprintf "%a" Osdp.SdpRet.pp status

let string_of_semialg (sa : Sys.semialgebraic_t) =
  let pp_conj fmt c =
    Format.fprintf fmt "%s"
      (String.concat " && " (List.map (fun p -> Format.asprintf "%a <= 0" Sys.Poly.pp p) c))
  in
  String.concat " || " (List.map (fun c -> Format.asprintf "%a" pp_conj c) sa)

(* Builds one CSV record from a (possibly absent) semialgebraic invariant
   checked against [pts], restricted to [domain] (default: all points). *)
let record_of_check ~example ~method_ ~param ~pad_mode ~status ~runtime_s ~note
    ?domain (sa_opt : Sys.semialgebraic_t option) (pts : float array list) =
  match sa_opt with
  | None ->
    { example; method_; param; pad_mode; status; runtime_s; valid = "N/A";
      n_checked = 0; n_in_domain = 0; n_violations = 0; worst_violation = "-";
      invariant = ""; note = (if note = "" then "no invariant returned" else note) }
  | Some sa ->
    let r = Check.check ?domain sa pts in
    let valid = if Check.sound r then "PASS" else "FAIL" in
    let worst =
      match r.Check.worst with None -> "-" | Some w -> Printf.sprintf "%.6g" w.Check.value
    in
    { example; method_; param; pad_mode; status; runtime_s; valid;
      n_checked = r.Check.n_checked; n_in_domain = r.Check.n_in_domain;
      n_violations = List.length r.Check.violations; worst_violation = worst;
      invariant = string_of_semialg sa; note }

let skip_record ~example ~method_ ~param ~pad_mode ~note =
  { example; method_; param; pad_mode; status = "skipped"; runtime_s = 0.; valid = "SKIPPED";
    n_checked = 0; n_in_domain = 0; n_violations = 0; worst_violation = "-"; invariant = ""; note }

(* Simulation batch sizes: deliberately much smaller than the exploratory
   diagnostics in soundness_check_main.ml (2000x2000) -- this harness is
   meant to run routinely (Makefile target), and the dominant cost here is
   always the SDP solves, not the (cheap) simulation itself. *)
let ntraj = 300
let nsteps = 300

(* ---------------------------------------------------------------- *)
(* Group A: round / shape / affine on lin_t examples (no degree/k param;
   validated via common-Lyapunov generalization for the switched ones).

   None of the three ties its claim to sys.init at all (grep confirms
   quadraticTemplates.ml never references it): what they actually prove is
   that the found ellipsoid {x : x'Px <= 1} is itself forward-invariant
   (and, for round/shape, non-increasing) under the one-step dynamics --
   round/shape under u=0 only ("ignoring any input/disturbance", see their
   doc comments in analysis.mli), affine under any admissible bounded
   input. Every example here uses a placeholder init ball of arbitrary,
   example-independent radius (see Linear_examples.ml's own doc comment:
   "the source data did not specify init/input regions"), unrelated to the
   scale of whatever ellipsoid the solver happens to find -- so simulating
   from sys.init and checking against the ellipsoid (this module's first
   draft) mostly measures whether that arbitrary placeholder happens to sit
   inside the found ellipsoid, not whether the analysis is sound. The
   correct check, matching what's actually proved, is to seed points on the
   claimed ellipsoid's own boundary and forward-simulate from there (u=0 for
   round/shape, bounded random u for affine) -- exactly the property the
   LMI itself encodes. *)

let lin_examples : (string * Sys.lin_t) list =
  Linear_examples.examples @ Piecewise_linear_examples.examples

let n_boundary_seeds = 300

(* Random directions rescaled onto the boundary of {x : p(x) <= 0} where
   p(x) = x'Px - 1 is round/shape/affine's own postfixpoint invariant (see
   Analysis.build_result): p(d) = d'Pd - 1, so d'Pd = p(d) + 1, and scaling
   d by 1/sqrt(d'Pd) lands exactly on p=0. *)
let ellipsoid_boundary_seeds ~seed ~df (p : Sys.Poly.t) ~n : float array list =
  let rng = Random.State.make [| seed |] in
  List.filter_map
    (fun _ ->
      let d = Array.init df (fun _ -> Random.State.float rng 2. -. 1.) in
      let qd = Sim.eval p d [||] +. 1. in
      if qd <= 1e-9 then None
      else
        let s = 1. /. sqrt qd in
        Some (Array.map (fun x -> x *. s) d))
    (List.init n (fun i -> i))

let simulate_from ~seed ~input_mode (sys : Sys.poly_t) ~nsteps (starts : float array list) :
    float array list =
  let rng = Random.State.make [| seed |] in
  List.concat_map
    (fun start ->
      let state = ref start in
      let pts = ref [ start ] in
      for _ = 1 to nsteps do
        let next, _ = Sim.step rng sys ~input_mode ~input_fallback_half_width:10. !state in
        state := next;
        pts := !state :: !pts
      done;
      !pts)
    starts

let run_group_a ~pad_mode ~pad =
  List.iter
    (fun (name, lin) ->
      let poly_sys = Sys.linear_to_poly lin in
      List.iter
        (fun (method_, f, input_mode) ->
          let (status, postfix), dt =
            time_it (fun () ->
                let r : Ana.analysis_result_t = f ?pad lin in
                (r.Ana.status, r.Ana.postfixpoint))
          in
          match postfix with
          | [ ((), [ [ p ] ]) ] ->
            let starts = ellipsoid_boundary_seeds ~seed:1 ~df:lin.Sys.df p ~n:n_boundary_seeds in
            let pts = simulate_from ~seed:2 ~input_mode poly_sys ~nsteps starts in
            add
              (record_of_check ~example:name ~method_ ~param:"-" ~pad_mode
                 ~status:(status_str status) ~runtime_s:dt
                 ~note:"checked by forward-simulating from the claimed ellipsoid's own boundary"
                 (Some [ [ p ] ]) pts)
          | [] ->
            add
              (record_of_check ~example:name ~method_ ~param:"-" ~pad_mode
                 ~status:(status_str status) ~runtime_s:dt ~note:"" None [])
          | _ ->
            (* round/shape/affine always return exactly one disjunct with
               exactly one conjunct (see Analysis.build_result); anything
               else would indicate a real, separate wiring change there. *)
            assert false)
        [ ("round", (fun ?pad sys -> Ana.round ?pad sys), Sim.Zero);
          ("shape", (fun ?pad sys -> Ana.shape ?pad sys), Sim.Zero);
          ("affine", (fun ?pad sys -> Ana.affine ?pad sys), Sim.Uniform) ])
    lin_examples

(* ---------------------------------------------------------------- *)
(* Group B: piecewise_lin (k-inductive piecewise-quadratic), k=1..4.

   count_paths is solver-free (pure graph enumeration), so it's always
   computed and reported even when the actual solve is skipped: paths
   growing combinatorially with k is an expected, correct property of the
   method (see PiecewiseQuadraticTemplates), not a bug, but a solve over
   more than [max_paths] path-certificates at once is a genuinely large SDP
   (confirmed to take upwards of an hour on this machine for
   RunningExample's k=4, 314 paths) -- unsuitable for a routine sanity
   check. Raise max_paths (2nd CLI arg) for an occasional, slower, more
   thorough run. *)

(* piecewise_lin (PiecewiseQuadraticTemplates.invariant) is scoped to di=0
   systems only (no input concept in the source method), so Example1Pierre
   (di=1) -- otherwise a fine lin_t example, exercised via Group A above --
   is excluded here. *)
let piecewise_examples : (string * Sys.lin_t * Sys.coeff array array option) list =
  List.filter_map
    (fun (n, s) -> if s.Sys.di = 0 then Some (n, s, None) else None)
    Piecewise_linear_examples.examples
  @ [ ("RunningExample", Piecewise_linear_examples.running_example,
       Some Piecewise_linear_examples.running_example_offsets) ]

(* Which cell of [cells] a state/input pair falls into, replicating
   Simulate.pick_mode's own first-match semantics exactly (so this always
   agrees with which update was actually applied at that point). *)
let mode_index_of (cells : (Sys.poly_guard_t * Sys.poly_update_t) array) state input =
  let n = Array.length cells in
  let rec find i =
    if i >= n then (if n = 1 then 0 else failwith "mode_index_of: no guard matched")
    else if Sim.satisfies (fst cells.(i)) state input then i else find (i + 1)
  in
  find 0

(* A length-k path's certificate (see PiecewiseQuadraticTemplates' module
   doc) bounds states reached via that *exact* sliding window of the last k
   modes visited, not just "currently in the last cell of the path" --
   e.g. on MignoneInvariance1, the certificate for path [1] (cell 1, no
   predecessor) only concerns trajectories that *start* in cell 1, which
   never happens here since init only touches cell 0; states genuinely
   reached in cell 1 arrive via some other path (e.g. [2,1]) with its own,
   different certificate. Checking a path's certificate against every point
   merely sitting in its last cell's guard (regardless of how it got there)
   tests a strictly stronger claim than what was actually proved. This
   simulates while tracking each visited point's own true mode-history
   window (via PQuad.extend_path, the library's own sliding-window logic),
   so each certificate can be checked against exactly the points it was
   proved for. *)
let simulate_with_paths ~seed ~k (sys : Sys.poly_t) ~ntraj ~nsteps :
    (int array * float array) list =
  let rng = Random.State.make [| seed |] in
  let cells = Array.of_list sys.Sys.map in
  let points = ref [] in
  for _ = 1 to ntraj do
    let state = ref (Sim.sample_init rng sys ~init_fallback_half_width:10.) in
    let window = ref [| mode_index_of cells !state (Array.make sys.Sys.di 0.) |] in
    points := (!window, !state) :: !points;
    for _ = 1 to nsteps do
      let next, input = Sim.step rng sys ~input_mode:Sim.Uniform ~input_fallback_half_width:10. !state in
      window := PQuad.extend_path !window (mode_index_of cells next input) k;
      state := next;
      points := (!window, !state) :: !points
    done
  done;
  !points

(* Calls PQuad.invariant directly (rather than going through
   Analysis.piecewise_lin) solely to keep each certificate's actual path
   (int array, the mode-history window) alongside it -- Analysis's
   postfixpoint wrapper only keeps the last cell's guard, which is exactly
   the information that isn't enough to check a path correctly (see
   simulate_with_paths above). Otherwise mirrors Analysis.piecewise_lin's
   own construction (options_of_pad, the "- a" threshold) exactly. *)
let options_of_pad = function
  | None -> PQuad.Lmi.default
  | Some pad -> PQuad.Lmi.{ default with pad }

let run_group_b ~pad_mode ~pad ~max_paths =
  List.iter
    (fun (name, lin, offsets) ->
      let poly_sys = Sys.linear_to_poly lin in
      List.iter
        (fun k ->
          let npaths = PQuad.count_paths ?offsets k lin in
          let param = Printf.sprintf "k=%d (%d paths)" k npaths in
          if npaths > max_paths then
            add
              (skip_record ~example:name ~method_:"piecewise_lin" ~param ~pad_mode
                 ~note:(Printf.sprintf "skipped: %d paths > max_paths=%d" npaths max_paths))
          else begin
            let (status, result_opt), dt =
              time_it (fun () -> PQuad.invariant ?offsets ~options:(options_of_pad pad) k lin)
            in
            let status_s = status_str status in
            match result_opt with
            | None ->
              add
                { example = name; method_ = "piecewise_lin"; param; pad_mode; status = status_s;
                  runtime_s = dt; valid = "N/A"; n_checked = 0; n_in_domain = 0; n_violations = 0;
                  worst_violation = "-"; invariant = ""; note = "no invariant returned" }
            | Some r ->
              let tagged_pts = simulate_with_paths ~seed:2 ~k poly_sys ~ntraj ~nsteps in
              Array.iteri
                (fun idx path ->
                  let invariant =
                    Sys.Poly.(
                      Sys.Cast.poly_of_quadratic_form ~is_homogenous:false r.PQuad.certificates.(idx)
                      - const r.PQuad.a)
                  in
                  let pts = List.filter_map (fun (w, s) -> if w = path then Some s else None) tagged_pts in
                  add
                    (record_of_check ~example:name ~method_:"piecewise_lin"
                       ~param:(Printf.sprintf "%s path=%d [%s]" param idx
                                 (String.concat "," (Array.to_list (Array.map string_of_int path))))
                       ~pad_mode ~status:status_s ~runtime_s:(if idx = 0 then dt else 0.)
                       ~note:"checked only against sim points whose actual mode-history matches this path"
                       (Some [ [ invariant ] ]) pts))
                r.PQuad.paths
          end)
        [ 1; 2; 3; 4 ])
    piecewise_examples

(* ---------------------------------------------------------------- *)
(* Group C: prop_driven_sos_lyap / liouville_method on poly_t examples,
   degrees 2,4,6,8,10.

   [perin] (3 state vars, piecewise, +domain_restriction) is the one example
   here whose SOS solves grow steeply with degree (degree=6 alone already
   ~20s per solve; degree=8/10 extrapolate to many minutes each) -- capped
   at [perin_max_degree] for the same routine-runtime reason as Group B's
   [max_paths]; every other example here stays well under a second per
   solve even at degree=10. *)

let poly_examples : (string * Sys.poly_t * Sys.basic_semialgebraic_t option * int) list =
  List.map (fun (n, s) -> (n, s, None, 10)) Polynomial_examples.examples
  @ [ ("cav10", Prop_sos_examples.cav10, None, 10);
      ("perin", Prop_sos_examples.perin, Some Prop_sos_examples.perin_domain_restriction, 6) ]

let sos_degrees = [ 2; 4; 6; 8; 10 ]
let bounds_degree = 4 (* representative degree used for the per-axis kappa=+/-x_i bounds sweep *)

let run_prop_driven ~pad_mode ~pad =
  List.iter
    (fun (name, sys, domain_restriction, max_degree) ->
      let pts = Sim.run ~seed:3 ~input_mode:Sim.Uniform sys ~ntraj ~nsteps in
      let domain =
        match domain_restriction with
        | None -> None
        | Some dr -> Some (Check.within_conjunction dr)
      in
      let note =
        match domain_restriction with
        | None -> ""
        | Some _ -> "checked only within the assumed domain_restriction region"
      in
      List.iter
        (fun deg ->
          if deg > max_degree then
            add
              (skip_record ~example:name ~method_:"prop_driven_sos_lyap"
                 ~param:(Printf.sprintf "deg=%d kappa=default" deg) ~pad_mode
                 ~note:(Printf.sprintf "skipped: degree %d > max_degree=%d for this example" deg max_degree))
          else begin
            let (status, postfix), dt =
              time_it (fun () ->
                  let r : Ana.analysis_result_t = Ana.prop_driven_sos_lyap ?domain_restriction ?pad sys deg in
                  (r.Ana.status, r.Ana.postfixpoint))
            in
            let sa_opt = match postfix with [] -> None | (_, sa) :: _ -> Some sa in
            add
              (record_of_check ~example:name ~method_:"prop_driven_sos_lyap"
                 ~param:(Printf.sprintf "deg=%d kappa=default" deg) ~pad_mode
                 ~status:(status_str status) ~runtime_s:dt ~note ?domain sa_opt pts)
          end)
        sos_degrees;
      (* Per-axis bounds, at one representative degree only (see module doc). *)
      if bounds_degree <= max_degree then
        for i = 0 to sys.Sys.df - 1 do
          List.iter
            (fun (sign_name, kappa) ->
              let (status, postfix), dt =
                time_it (fun () ->
                    let r : Ana.analysis_result_t =
                      Ana.prop_driven_sos_lyap ?domain_restriction ?pad ~kappa sys bounds_degree
                    in
                    (r.Ana.status, r.Ana.postfixpoint))
              in
              let sa_opt = match postfix with [] -> None | (_, sa) :: _ -> Some sa in
              add
                (record_of_check ~example:name ~method_:"prop_driven_sos_lyap_bounds"
                   ~param:(Printf.sprintf "deg=%d kappa=%sx%d" bounds_degree sign_name i) ~pad_mode
                   ~status:(status_str status) ~runtime_s:dt ~note ?domain sa_opt pts))
            [ ("+", Ana.Sos.(?? i)); ("-", Ana.Sos.(~- (?? i))) ]
        done)
    poly_examples

let run_liouville ~pad_mode ~pad =
  List.iter
    (fun (name, sys, _domain_restriction, max_degree) ->
      match sys.Sys.r_g with
      | None ->
        add
          (skip_record ~example:name ~method_:"liouville_method" ~param:"-" ~pad_mode
             ~note:"skipped: system has no r_g (required by Liouville.compute)")
      | Some r_g_coeff ->
        let r_g = Sys.Coeff.to_float r_g_coeff in
        let domain = Check.within_origin_ball ~radius:r_g in
        let pts = Sim.run ~seed:4 ~input_mode:Sim.Uniform sys ~ntraj ~nsteps in
        List.iter
          (fun deg ->
            if deg > max_degree then
              add
                (skip_record ~example:name ~method_:"liouville_method" ~param:(Printf.sprintf "deg=%d" deg)
                   ~pad_mode ~note:(Printf.sprintf "skipped: degree %d > max_degree=%d for this example" deg max_degree))
            else begin
              let (status, postfix), dt =
                time_it (fun () ->
                    let r : Ana.analysis_result_t = Ana.liouville_method ?pad sys deg in
                    (r.Ana.status, r.Ana.postfixpoint))
              in
              let sa_opt = match postfix with [] -> None | (_, sa) :: _ -> Some sa in
              add
                (record_of_check ~example:name ~method_:"liouville_method" ~param:(Printf.sprintf "deg=%d" deg)
                   ~pad_mode ~status:(status_str status) ~runtime_s:dt
                   ~note:(Printf.sprintf "checked only within ||x||<=%.4g (r_g)" r_g) ~domain sa_opt pts)
            end)
          sos_degrees)
    poly_examples

(* ---------------------------------------------------------------- *)

let () =
  let argv = Stdlib.Sys.argv in
  let pad_mode = if Array.length argv > 1 then argv.(1) else "default" in
  let out_path = if Array.length argv > 2 then argv.(2) else "full_check_results.csv" in
  let max_paths = if Array.length argv > 3 then int_of_string argv.(3) else 100 in
  let pad = match pad_mode with "zero" -> Some 0. | "default" -> None
    | m -> failwith (Printf.sprintf "full_check_main: unknown pad mode %S (expected \"zero\" or \"default\")" m)
  in
  pf "== full check: pad_mode=%s (pad=%s) max_paths=%d -> %s ==\n%!" pad_mode
    (match pad with None -> "<method default>" | Some p -> Printf.sprintf "%.1f" p) max_paths out_path;
  open_csv out_path;
  run_group_a ~pad_mode ~pad;
  run_group_b ~pad_mode ~pad ~max_paths;
  run_prop_driven ~pad_mode ~pad;
  run_liouville ~pad_mode ~pad;
  (match !csv_channel with Some oc -> close_out oc | None -> ());
  let total = List.length !records in
  let n_fail = List.length (List.filter (fun r -> r.valid = "FAIL") !records) in
  let n_pass = List.length (List.filter (fun r -> r.valid = "PASS") !records) in
  let n_skip = List.length (List.filter (fun r -> r.valid = "SKIPPED") !records) in
  let n_na = List.length (List.filter (fun r -> r.valid = "N/A") !records) in
  pf "== done: %d rows (%d PASS, %d FAIL, %d N/A, %d SKIPPED) written to %s ==\n%!" total n_pass n_fail n_na n_skip
    out_path;
  if n_fail > 0 then begin
    pf "!! %d FAIL row(s):\n%!" n_fail;
    List.iter
      (fun r -> if r.valid = "FAIL" then
          pf "  %s / %s / %s (pad=%s): worst_violation=%s\n%!" r.example r.method_ r.param r.pad_mode r.worst_violation)
      (List.rev !records);
    exit 1
  end
