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

  let is_satisfiable : t -> bool = fun f -> List.length f.clauses = 0

  let does_contain_empty_clause f =
    let rec helper = function
      | [] -> false
      | hd :: tl -> (
          (* if List.length hd = 0 then true else helper tl *)
          match hd with [] -> true | _ -> helper tl)
    in
    helper f.clauses

  let does_contain_unit_clause f =
    let rec helper = function
      | [] -> None
      | hd :: tl -> (
          (* if List.length hd = 1 then List.hd hd else helper tl *)
          match hd with [ x ] -> Some x | _ -> helper tl)
    in
    helper f.clauses

  let substitute_pure l f =
    let no_pure_occurence =
      List.filter f.clauses ~f:(fun cls ->
          match List.find cls ~f:(fun lit -> lit = l) with
          | None -> true
          | Some cls -> false)
      (* List.length cls
         = List.length (List.filter cls ~f:(fun lit -> not (lit = l)))) *)
      (*todo: rewrite, length is O(n)*)
    in
    (* let _ = log (String.concat ~sep:" " [ "Substitute"; Int.to_string l ]) in *)
    (* let _ =
         List.iter no_occurence ~f:(fun cls ->
             log_lst @@ List.map cls ~f:Int.to_string)
       in *)
    { cnf_options = f.cnf_options; clauses = no_pure_occurence }

  let substitute l f =
    let no_pure_occurence =
      substitute_pure l f
      (* List.filter f.clauses ~f:(fun cls ->
          List.length cls
          = List.length (List.filter cls ~f:(fun lit -> not (lit = l)))) *)
      (*todo: rewrite, length is O(n)*)
    in
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

  let unit_propagation l f =
    let no_unit_clx =
      List.filter f.clauses ~f:(fun cls ->
          (not (List.length cls = 1)) || not (List.hd_exn cls = l))
    in
    substitute l { cnf_options = f.cnf_options; clauses = no_unit_clx }

  (* let does_contain_pure_literal : t -> int option = fun f -> None *)
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

  let pure_literal_elimination l f = substitute_pure l f (*ok?*)
  let choose f = List.hd_exn @@ List.hd_exn f.clauses
end

let solve f =
  let pure_literals = CNFFormula.get_pure_literals f in
  (* let _ =  *)
  let rec loop f pure_literals acc : cnf_result =
    if CNFFormula.is_satisfiable f then Sat acc
    else if CNFFormula.does_contain_empty_clause f then Unsat
    else
      match CNFFormula.does_contain_unit_clause f with
      | Some l -> loop (CNFFormula.unit_propagation l f) pure_literals (l :: acc)
      | None -> (
          if not (Hash_set.is_empty pure_literals) then
            let l = List.hd_exn @@ Hash_set.to_list pure_literals in
            let _ = Hash_set.remove pure_literals l in
            loop
              (CNFFormula.pure_literal_elimination l f)
              pure_literals (l :: acc)
          else
            let l = CNFFormula.choose f in
            match loop (CNFFormula.substitute l f) pure_literals (l :: acc) with
            | Unsat ->
                loop (CNFFormula.substitute (-l) f) pure_literals (-l :: acc)
            | Sat acc -> Sat acc)
  in
  loop f pure_literals []

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
