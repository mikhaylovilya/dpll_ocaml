open Base
open Stdio

let debug_mode = 0

(* type mystruct = int list list *)
type cnf_options = { vars_num : int; cls_num : int }
type formula = { cnf_options : cnf_options; clauses : int list list }
type cnf_result = Unsat | Sat of int list

let print_lst lst =
  Caml.Format.printf "%s\n"
  @@ List.fold_right lst
       ~f:(fun x acc -> String.concat ~sep:" " [ x; acc ])
       ~init:""

let log str = if debug_mode = 1 then Caml.Format.printf "%s\n" str
let log_lst lst = if debug_mode = 1 then print_lst lst
let insert ~cls ~acc = cls :: acc

let parse_cnf ~path =
  let ic = In_channel.create path in
  let parse_headers () =
    match In_channel.input_line ic with
    | None -> None
    | Some x -> (
        match String.split_on_chars ~on:[ ' ' ] x with
        | [ "p"; "cnf"; vars_num; cls_num ] ->
            (* let _ = log "header" in *)
            (* let _ = log_lst [ vars_num; cls_num ] in *)
            Some
              {
                vars_num = Int.of_string vars_num;
                cls_num = Int.of_string cls_num;
              }
        | _ -> None)
  in
  let rec parse_clauses acc =
    match In_channel.input_line ic with
    | None -> Some acc
    | Some x -> (
        match List.tl @@ List.rev @@ String.split_on_chars ~on:[ ' ' ] x with
        | None -> None
        | Some line ->
            (* let _ = log "clause" in *)
            (* let _ = log_lst line in *)
            parse_clauses
            @@ insert ~cls:(List.map line ~f:(fun s -> Int.of_string s)) ~acc)
  in
  try
    let hdr = parse_headers () in
    let cls = parse_clauses [] in
    let _ = In_channel.close ic in
    (hdr, cls)
  with (* | End_of_file -> None *)
  | Failure e ->
    let _ = log e in
    let _ = In_channel.close ic in
    (None, None)
(* Base.Exn.protect  *)

module CNFFormula = struct
  type t = formula

  let is_satisfiable f = match f.clauses with [] -> true | _ -> false
  (* List.length f.clauses = 0 *)

  let does_contain_empty_clause f =
    let rec helper = function
      | [] -> false
      | hd :: tl -> ( match hd with [] -> true | _ -> helper tl)
    in
    helper f.clauses

  let does_contain_unit_clause f =
    let rec helper clx acc =
      match clx with
      | [] -> ( match acc with [] -> None | lst -> Some lst)
      | hd :: tl -> (
          match hd with [ x ] -> helper tl (x :: acc) | _ -> helper tl acc)
    in
    helper f.clauses []

  let substitute_pure l f =
    let no_pure_occurence =
      List.filter f.clauses ~f:(fun cls ->
          match List.find cls ~f:(fun lit -> lit = l) with
          | None -> true
          | Some cls -> false)
    in
    (* let _ = log (String.concat ~sep:" " [ "Substitute"; Int.to_string l ]) in *)
    (* let _ =
         List.iter no_occurence ~f:(fun cls ->
             log_lst @@ List.map cls ~f:Int.to_string)
       in *)
    { cnf_options = f.cnf_options; clauses = no_pure_occurence }

  let substitute l f =
    let no_pure_occurence = substitute_pure l f in
    let no_occurence =
      List.map no_pure_occurence.clauses ~f:(fun cls ->
          List.filter cls ~f:(fun lit -> not (lit = -l)))
    in
    (* let _ = log (String.concat ~sep:" " [ "Substitute"; Int.to_string l ]) in *)
    (* let _ =
         List.iter no_occurence ~f:(fun cls ->
             log_lst @@ List.map cls ~f:Int.to_string)
       in *)
    { cnf_options = f.cnf_options; clauses = no_occurence }

  let rec unit_propagation unit_literals f =
    (* let no_unit_clx =
         List.filter f.clauses ~f:(fun cls ->
             (not (List.length cls = 1)) || not (List.hd_exn cls = l))
       in *)
    match List.hd unit_literals with
    | None -> f
    | Some l -> (
        match List.tl unit_literals with
        | None -> f
        | Some new_unit_literals ->
            unit_propagation new_unit_literals (substitute l f))

  let get_pure_literals f =
    let pure_lits = Hash_set.create ~size:f.cnf_options.vars_num (module Int) in
    let all_lits = Hash_set.create ~size:f.cnf_options.vars_num (module Int) in
    let _ =
      List.iter f.clauses ~f:(fun cls ->
          List.iter cls ~f:(fun lit ->
              let _ =
                match Hash_set.exists pure_lits ~f:(fun e -> e = -lit) with
                | true -> Hash_set.remove pure_lits (-lit)
                | false ->
                    if not (Hash_set.exists all_lits ~f:(fun e -> e = lit)) then
                      Hash_set.add pure_lits lit
              in
              Hash_set.add all_lits lit))
    in
    (* let _ = log "pure literals" in *)
    (* let _ = log_lst @@ List.map (Hash_set.to_list pure_lits) ~f:Int.to_string in *)
    pure_lits

  let min_elt hash =
    let exception Found of int in
    try
      Hash_set.iter hash ~f:(fun x -> raise (Found x));
      raise Caml.Not_found
    with Found x -> x

  let rec pure_literal_elimination pure_literals f =
    try
      let l = min_elt pure_literals in
      let _ = Hash_set.remove pure_literals l in
      pure_literal_elimination pure_literals (substitute_pure l f)
    with Caml.Not_found -> f
  (*ok?*)

  let choose f = List.hd_exn @@ List.hd_exn f.clauses
end

type stats = { mutable splits : int }

let stats = { splits = 0 }

let solve f =
  let rec loop fs : cnf_result =
    (* Stdio.printf "Targets: %d\n" (List.length fs); *)
    (* Stdio.printf "splits = %d\n" stats.splits; *)
    match fs with
    | [] -> Unsat
    | f :: fs -> (
        if CNFFormula.is_satisfiable f then Sat []
        else if CNFFormula.does_contain_empty_clause f then loop fs
        else
          match CNFFormula.does_contain_unit_clause f with
          | Some unit_literals ->
              loop (CNFFormula.unit_propagation unit_literals f :: fs)
              (* (List.append unit_literals acc) *)
          | None ->
              let pure_literals = CNFFormula.get_pure_literals f in
              (* let _ = List.filter f.clauses ~f:(fun cls -> ) *)
              if not (Hash_set.is_empty pure_literals) then
                (* let l = min_elt pure_literals in *)
                (* List.hd_exn @@ Hash_set.to_list pure_literals in *)
                (* let _ = Hash_set.remove pure_literals l in *)
                loop (CNFFormula.pure_literal_elimination pure_literals f :: fs)
                (* (List.append (Hash_set.to_list pure_literals) acc) *)
              else
                let l = CNFFormula.choose f in
                stats.splits <- stats.splits + 1;
                loop
                  (CNFFormula.substitute l f
                  :: CNFFormula.substitute (-l) f
                  :: fs))
  in
  loop [ f ]

let print_model = function
  | None -> print_endline "Error during parsing file"
  | Some cnf_res -> (
      match cnf_res with
      | Unsat -> print_endline "Unsat"
      | Sat res ->
          let _ = print_endline "Sat" in
          print_lst @@ List.map res ~f:Int.to_string)

let main ~path =
  match parse_cnf ~path with
  | Some hdr, Some clx ->
      let f = { cnf_options = hdr; clauses = clx } in
      Some (solve f)
  | _, _ -> None
