(* Reads one or more full_check_main.ml CSVs (the columns defined by its own
   [csv_header]) and prints a categorized, human-readable summary: overall
   PASS/FAIL/SKIPPED/N-A counts, then every FAIL grouped by (example,
   method) and classified as UNSOUND (some run in the group has a large or
   infinite violation -- a genuinely wrong invariant, not just an
   imprecise one) or IMPRECISE (every run in the group has a small, bounded
   violation). Grouping (rather than classifying each row alone) matters:
   a family like prop_driven_sos_lyap on cav10 has a modest violation at
   its lowest degree but blows up at higher degrees -- the whole family is
   the same root cause, so it's classified as a whole by its worst member,
   not split awkwardly row by row. Decoupled from re-running the sweep
   itself: point it at any existing full_check_main.ml CSV. *)

(* Minimal RFC4180 CSV row parser: handles quoted fields, embedded commas,
   escaped ("") quotes, and embedded newlines within a quoted field (a
   single CSV "line" can span multiple text lines when a field is quoted
   and contains a newline, e.g. full_check_main.ml's multi-line polynomial
   pretty-prints). *)
let parse_csv (path : string) : string list list =
  let ic = open_in_bin path in
  let len = in_channel_length ic in
  let s = really_input_string ic len in
  close_in ic;
  let n = String.length s in
  let rows = ref [] in
  let fields = ref [] in
  let field = Buffer.create 256 in
  let i = ref 0 in
  let in_quotes = ref false in
  let push_field () =
    fields := Buffer.contents field :: !fields;
    Buffer.clear field
  in
  let push_row () =
    push_field ();
    rows := List.rev !fields :: !rows;
    fields := []
  in
  while !i < n do
    let c = s.[!i] in
    if !in_quotes then begin
      if c = '"' then
        if !i + 1 < n && s.[!i + 1] = '"' then begin
          Buffer.add_char field '"';
          i := !i + 2
        end
        else begin
          in_quotes := false;
          incr i
        end
      else begin
        Buffer.add_char field c;
        incr i
      end
    end
    else begin
      match c with
      | '"' -> in_quotes := true; incr i
      | ',' -> push_field (); incr i
      | '\n' -> push_row (); incr i
      | '\r' -> incr i
      | c -> Buffer.add_char field c; incr i
    end
  done;
  if Buffer.length field > 0 || !fields <> [] then push_row ();
  List.rev !rows

type row = {
  example : string;
  method_ : string;
  param : string;
  pad_mode : string;
  valid : string;
  worst_violation : string;
}

let row_of_fields = function
  | [ example; method_; param; pad_mode; _status; _runtime_s; valid; _n_checked; _n_in_domain;
      _n_violations; worst_violation; _invariant; _note ] ->
    { example; method_; param; pad_mode; valid; worst_violation }
  | fields ->
    failwith (Printf.sprintf "summarize_full_check: unexpected column count (%d)" (List.length fields))

(* [inf]/[nan] parse fine via float_of_string; "-" (no violation recorded)
   and any other unparseable text map to 0 (never triggers UNSOUND). *)
let violation_magnitude (s : string) : float =
  match float_of_string_opt s with
  | Some f when Float.is_nan f -> 0.
  | Some f -> Float.abs f
  | None -> 0.

let unsound_threshold = 2.0
(* A violation of this magnitude or more marks a whole (example, method)
   group UNSOUND rather than merely IMPRECISE. Chosen empirically: it sits
   comfortably between the largest observed genuinely-imprecise violation
   (~1.0, e.g. liouville_method on Thao8.3) and the smallest observed
   genuinely-unsound one (e.g. prop_driven_sos_lyap on cav10 at its lowest
   failing degree, ~23) -- see full_check_main.ml's own module doc and
   propSOSTemplates.ml/liouville.ml's KNOWN ISSUE comments for the
   underlying findings this is summarizing. *)

module SMap = Map.Make (String)

let read_all_rows (paths : string list) : row list =
  List.concat_map
    (fun path ->
      match parse_csv path with
      | [] -> []
      | _header :: rows -> List.map row_of_fields rows)
    paths

let () =
  let paths = List.tl (Array.to_list Stdlib.Sys.argv) in
  let paths = if paths = [] then [ "full_check_pad0.csv"; "full_check_pad_default.csv" ] else paths in
  let rows = read_all_rows paths in
  let total = List.length rows in
  let count v = List.length (List.filter (fun r -> r.valid = v) rows) in
  Printf.printf "== full_check summary (%s) ==\n" (String.concat ", " paths);
  Printf.printf "%d rows total: %d PASS, %d FAIL, %d N/A, %d SKIPPED\n\n"
    total (count "PASS") (count "FAIL") (count "N/A") (count "SKIPPED");

  let fails = List.filter (fun r -> r.valid = "FAIL") rows in
  let groups =
    List.fold_left
      (fun acc r ->
        let key = r.example ^ " / " ^ r.method_ in
        let prev = try SMap.find key acc with Not_found -> [] in
        SMap.add key (prev @ [ r ]) acc)
      SMap.empty fails
  in
  let group_max_violation members =
    List.fold_left (fun acc r -> Float.max acc (violation_magnitude r.worst_violation)) 0. members
  in
  let unsound, imprecise =
    SMap.fold
      (fun key members (u, i) ->
        if group_max_violation members >= unsound_threshold then ((key, members) :: u, i)
        else (u, (key, members) :: i))
      groups ([], [])
  in
  let sort_by_max l =
    List.sort (fun (_, a) (_, b) -> compare (group_max_violation b) (group_max_violation a)) l
  in
  (* Group by [param] and merge pad modes that hit the exact same
     violation into one line, since pad0 and the default pad have so far
     always produced identical results (see full_check_main.ml's module
     doc) -- printing every row twice, once per pad file, would just be
     noise. Pad modes that genuinely disagree are still shown separately. *)
  let print_group (key, members) =
    Printf.printf "  %s\n" key;
    (* Preserve the CSV's own row order (numeric-ascending by degree/k,
       since that's the order full_check_main.ml iterates them in) rather
       than an alphabetic param sort, which would put "deg=10" before
       "deg=4". *)
    let params_in_order =
      List.fold_left (fun acc r -> if List.mem r.param acc then acc else acc @ [ r.param ]) [] members
    in
    List.iter
      (fun param ->
        let pad_violations =
          List.filter_map (fun r -> if r.param = param then Some (r.pad_mode, r.worst_violation) else None) members
        in
        let by_violation =
          List.fold_left
            (fun acc (pad_mode, wv) ->
              let prev = try SMap.find wv acc with Not_found -> [] in
              SMap.add wv (pad_mode :: prev) acc)
            SMap.empty pad_violations
        in
        if SMap.cardinal by_violation = 1 then
          let wv, _ = SMap.choose by_violation in
          Printf.printf "    %-40s worst_violation=%s\n" param wv
        else
          SMap.iter
            (fun wv pad_modes ->
              Printf.printf "    %-40s worst_violation=%-16s (pad=%s)\n" param wv
                (String.concat "," (List.sort_uniq compare pad_modes)))
            by_violation)
      params_in_order
  in
  Printf.printf "-- UNSOUND (worst_violation >= %.1f somewhere in the group -- a genuinely wrong invariant) --\n"
    unsound_threshold;
  if unsound = [] then Printf.printf "  (none)\n"
  else List.iter print_group (sort_by_max unsound);
  Printf.printf "\n-- IMPRECISE (all violations < %.1f -- likely a numerical/precision gap, not a logic error) --\n"
    unsound_threshold;
  if imprecise = [] then Printf.printf "  (none)\n"
  else List.iter print_group (sort_by_max imprecise);
  Printf.printf "\n"
