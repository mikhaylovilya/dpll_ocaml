open Base
open Stdio

let debug_mode = 1

(* type mystruct = int list list *)
type cnf_options =
  { vars_num : int
  ; cls_num : int
  }

type formula =
  { cnf_options : cnf_options
  ; clauses : int list list
  }

type cnf_result =
  | Unsat
  | Sat of int list

let print_lst lst =
  Caml.Format.printf "%s\n"
  @@ List.fold_right lst ~f:(fun x acc -> String.concat ~sep:" " [ x; acc ]) ~init:""
;;

let log_str str = if debug_mode = 1 then Caml.Format.printf "%s\n" str
let log_int intg = if debug_mode = 1 then Caml.Format.printf "%d\n" intg

let log_lst lst =
  if debug_mode = 1
  then
    log_str @@ String.concat @@ List.intersperse ~sep:" " @@ List.map lst ~f:Int.to_string
;;

let log_lst_lst lst_lst =
  if debug_mode = 1
  then
    (* log_str @@ String.concat ~sep:" | " @@ List.map (List.concat lst_lst) ~f:Int.to_string *)
    log_str
    @@ String.concat
    @@ List.concat
    @@ List.map lst_lst ~f:(fun cls ->
         ([ "(" ] @ List.intersperse ~sep:" " @@ List.map cls ~f:Int.to_string) @ [ ")" ])
;;

let log_set set = if debug_mode = 1 then log_lst @@ Hash_set.to_list set
let insert ~cls ~acc = cls :: acc

let parse_cnf ~path =
  let ic = In_channel.create path in
  let parse_headers () =
    match In_channel.input_line ic with
    | None -> None
    | Some x ->
      (match String.split_on_chars ~on:[ ' ' ] x with
       | [ "p"; "cnf"; vars_num; cls_num ] ->
         (* let _ = log "header" in *)
         (* let _ = log_lst [ vars_num; cls_num ] in *)
         Some { vars_num = Int.of_string vars_num; cls_num = Int.of_string cls_num }
       | _ -> None)
  in
  let rec parse_clauses acc =
    match In_channel.input_line ic with
    | None -> Some acc
    | Some x ->
      (match List.tl @@ List.rev @@ String.split_on_chars ~on:[ ' ' ] x with
       | None -> None
       | Some line ->
         (* let _ = log "clause" in *)
         (* let _ = log_lst line in *)
         parse_clauses @@ insert ~cls:(List.map line ~f:(fun s -> Int.of_string s)) ~acc)
  in
  try
    let hdr = parse_headers () in
    let cls = parse_clauses [] in
    let _ = In_channel.close ic in
    hdr, cls
  with
  (* | End_of_file -> None *)
  | Failure e ->
    let _ = log_str e in
    let _ = In_channel.close ic in
    None, None
;;

(* Base.Exn.protect  *)

module CNFFormula = struct
  type t = formula

  let is_satisfiable f =
    match f.clauses with
    | [] -> true
    | _ -> false
  ;;

  (* List.length f.clauses = 0 *)

  let does_contain_empty_clause f =
    let rec helper = function
      | [] -> false
      | hd :: tl ->
        (match hd with
         | [] -> true
         | _ -> helper tl)
    in
    helper f.clauses
  ;;

  let does_contain_unit_clause f =
    let rec helper clx acc =
      match clx with
      | [] ->
        (match acc with
         | [] -> None
         | lst -> Some lst)
      | hd :: tl ->
        (match hd with
         | [ x ] -> helper tl (x :: acc) (*serach for abs(x)*)
         | _ -> helper tl acc)
    in
    helper f.clauses []
  ;;

  let eliminate_pures predicate f =
    let no_pure_occurence = List.filter f.clauses ~f:predicate in
    log_str "no_pure_occurence literals";
    log_lst_lst no_pure_occurence;
    { cnf_options = f.cnf_options; clauses = no_pure_occurence }
  ;;

  (* let substitute_pure l f =
    let no_pure_occurence =
      List.filter f.clauses ~f:(fun cls ->
        match List.find cls ~f:(fun lit -> lit = l) with
        | None -> true
        | Some cls -> false)
    in
    { cnf_options = f.cnf_options; clauses = no_pure_occurence }
  ;; *)

  let substitute l f =
    log_str "Literal to substitute:";
    log_int l;
    let clause_intersects l cls =
      let exception Found_other in
      try
        List.iter cls ~f:(fun lit -> if lit = l then raise Found_other);
        true
      with
      | Found_other -> false
    in
    let no_pure_occurence = eliminate_pures (clause_intersects l) f in
    (* let no_pure_occurence = substitute_pure l f in *)
    (* log_str "no_pure_occurence literals: "; *)
    (* let _ = log_lst_lst no_pure_occurence.clauses in *)
    (* log_str "no_pure_occurence cls lengths: "; *)
    (* let _ = log_lst @@ List.map no_pure_occurence.clauses ~f:List.length in *)
    let no_occurence =
      List.map no_pure_occurence.clauses ~f:(fun cls ->
        List.filter cls ~f:(fun lit -> not (lit = -l)))
    in
    log_str "no_occurence literals: ";
    let _ = log_lst_lst no_occurence in
    (* log_str "no_occurence cls lengths: "; *)
    (* let _ = log_lst @@ List.map no_occurence ~f:List.length in *)
    { cnf_options = f.cnf_options; clauses = no_occurence }
  ;;

  let rec unit_propagation unit_literals f =
    match unit_literals with
    | [] -> f
    | hd :: tl -> unit_propagation tl (substitute hd f)
  ;;

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
              if not (Hash_set.exists all_lits ~f:(fun e -> e = lit))
              then Hash_set.add pure_lits lit
          in
          Hash_set.add all_lits lit))
    in
    pure_lits
  ;;

  let min_elt hash =
    let exception Found of int in
    try
      Hash_set.iter hash ~f:(fun x -> raise (Found x));
      raise Caml.Not_found
    with
    | Found x -> x
  ;;

  let pure_literal_elimination pure_literals f =
    (* try *)
    (* let l = min_elt pure_literals in *)
    let clause_intersects pure_literals cls =
      let exception Found in
      try
        List.iter cls ~f:(fun lit -> if Hash_set.mem pure_literals lit then raise Found);
        true
      with
      | Found -> false
    in
    (* let _ = Hash_set.remove pure_literals l in *)
    eliminate_pures (clause_intersects pure_literals) f
  ;;

  (* with Caml.Not_found -> f *)
  (*ok?*)

  let choose f = List.hd_exn @@ List.hd_exn f.clauses
end

let solve f =
  let rec loop f acc : cnf_result =
    log_str "Source formula:";
    log_lst_lst f.clauses;
    if CNFFormula.is_satisfiable f
    then Sat acc
    else if CNFFormula.does_contain_empty_clause f
    then (
      let _ = log_str "Unsat" in
      Unsat)
    else (
      let f1, acc1, opt =
        match CNFFormula.does_contain_unit_clause f with
        | Some unit_literals ->
          log_str "Unit literals:";
          log_lst unit_literals;
          CNFFormula.unit_propagation unit_literals f, List.append unit_literals acc, true
        | None -> f, acc, false
      in
      let pure_literals = CNFFormula.get_pure_literals f1 in
      log_str "Pure literals:";
      log_set pure_literals;
      if not (Hash_set.is_empty pure_literals)
      then
        loop
          (CNFFormula.pure_literal_elimination pure_literals f1)
          (List.append (Hash_set.to_list pure_literals) acc1)
      else if opt
      then loop f1 acc1
      else (
        let l = CNFFormula.choose f1 in
        log_str "Choose:";
        log_int l;
        match loop (CNFFormula.substitute l f1) (l :: acc1) with
        | Unsat -> loop (CNFFormula.substitute (-l) f1) (-l :: acc1)
        | Sat acc1 -> Sat acc1))
  in
  loop f []
;;

let print_model = function
  | None -> print_endline "Error during parsing file"
  | Some cnf_res ->
    (match cnf_res with
     | Unsat -> print_endline "Unsat"
     | Sat res ->
       let _ = print_endline "Sat" in
       print_lst @@ List.map res ~f:Int.to_string)
;;

let main ~path =
  match parse_cnf ~path with
  | Some hdr, Some clx ->
    let f = { cnf_options = hdr; clauses = clx } in
    Some (solve f)
  | _, _ -> None
;;
