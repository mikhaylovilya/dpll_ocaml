open Base
open Stdio

<<<<<<< Updated upstream
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
=======
type formula = int list list

type cnf_result =
  | Unsat
  | Sat of int list

let parse_cnf ~path =
  let ic = In_channel.create path in
  let _ = In_channel.input_line ic in
  let rec parse_clauses acc =
    match In_channel.input_line ic with
    | None -> Some acc
    | Some x ->
      (match List.tl @@ List.rev @@ String.split_on_chars ~on:[ ' ' ] x with
       | None -> None
       | Some line -> parse_clauses @@ (List.map line ~f:(fun s -> Int.of_string s) :: acc))
>>>>>>> Stashed changes
  in
  try
    let cls = parse_clauses [] in
<<<<<<< Updated upstream
    let _ = In_channel.close ic in
    (hdr, cls)
  with (* | End_of_file -> None *)
  | Failure e ->
    let _ = log e in
    let _ = In_channel.close ic in
    (None, None)
(* Base.Exn.protect  *)
=======
    In_channel.close ic;
    cls
  with
  | Failure e ->
    In_channel.close ic;
    None
;;
>>>>>>> Stashed changes

module CNFFormula = struct
  type t = formula

<<<<<<< Updated upstream
  let is_satisfiable f = match f.clauses with [] -> true | _ -> false
  (* List.length f.clauses = 0 *)

  let does_contain_empty_clause f =
=======
  let is_satisfiable f =
    match f with
    | [] -> true
    | _ -> false
  ;;

  let contains_empty_clause f =
>>>>>>> Stashed changes
    let rec helper = function
      | [] -> false
      | hd :: tl -> ( match hd with [] -> true | _ -> helper tl)
    in
<<<<<<< Updated upstream
    helper f.clauses

  let does_contain_unit_clause f =
    let rec helper clx acc =
      match clx with
      | [] -> ( match acc with [] -> None | lst -> Some lst)
      | hd :: tl -> (
          match hd with [ x ] -> helper tl (x :: acc) | _ -> helper tl acc)
    in
    helper f.clauses []

  let eliminate_pures predicate f =
    let no_pure_occurence = List.filter f.clauses ~f:predicate in
    { cnf_options = f.cnf_options; clauses = no_pure_occurence }

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
=======
    helper f
  ;;

  let find_units_pures f =
    let pures = Hash_set.create (module Int) in
    let all = Hash_set.create (module Int) in
    let units = Hash_set.create (module Int) in
    let () =
      List.iter f ~f:(fun cl ->
        let () =
          List.iter cl ~f:(fun l ->
            let () =
              match Hash_set.mem pures (-l) with
              | true -> Hash_set.remove pures (-l)
              | false when not (Hash_set.mem all l) -> Hash_set.add pures l
              | _ -> ()
            in
            Hash_set.add all l)
        in
        match cl with
        | [ l ] when (not (Hash_set.mem units l)) && not (Hash_set.mem units (-l)) ->
          Hash_set.add units l
        | _ -> ())
    in
    units, pures
  ;;

  let%test "pures" =
    let f = [ [ 2 ]; [ 3; 5; -2 ]; [ 4 ] ] in
    let _, pures = find_units_pures f in
    let expected = Hash_set.of_list (module Int) [ 3; 5; 4 ] in
    Hash_set.equal expected pures
  ;;

  let eliminate_pures f pures =
    List.filter f ~f:(fun cl -> not (List.exists cl ~f:(fun l -> Hash_set.mem pures l)))
  ;;

  let%test "eliminate pures" =
    let f = [ [ 2 ]; [ 3; 5; -2 ]; [ 4; -2 ] ] in
    let _, pures = find_units_pures f in
    let expected = [ [ 2 ] ] in
    let actual = eliminate_pures f pures in
    Stdlib.(actual = expected)
  ;;

  let substitute f lit =
    List.filter_map f ~f:(fun cl ->
      let exception Found of int in
      try
        List.iter cl ~f:(fun l -> if l = lit || l = -lit then raise (Found l));
        Some cl
      with
      | Found l ->
        if l = lit then None else Some (List.filter cl ~f:(fun l1 -> not (l1 = l))))
  ;;

  let%test "subs" =
    let f = [ [ 2; -5 ]; [ 3; 5; -2 ]; [ 4; -2 ] ] in
    let actual = substitute f 2 in
    let expected = [ [ 3; 5 ]; [ 4 ] ] in
    Stdlib.(actual = expected)
  ;;

  let unit_propagation f units =
    List.rev_filter_map f ~f:(fun cl ->
      let exception Found of int in
      try
        Some
          (List.rev_filter cl ~f:(fun l ->
             if Hash_set.mem units l
             then raise (Found l)
             else not (Hash_set.mem units (-l))))
      with
      | Found l -> None)
  ;;

  (* let unit_propagation f units =
    List.filter_map f ~f:(fun cl ->
      let exception Same of int in
      let exception Reverse of int in
      try
        List.iter cl ~f:(fun l ->
          if Hash_set.exists units ~f:(fun ul -> ul = l)
          then raise (Same l)
          else if Hash_set.exists units ~f:(fun ul -> ul = -l)
          then raise (Reverse l));
        Some cl
      with
      | Same l -> None
      | Reverse rl -> Some (List.filter cl ~f:(fun l1 -> not (l1 = rl))))
  ;; *)

  let hash_set_list () =
    let rec range a b acc = if a > b then acc else range (a + 1) b (a :: acc) in
    let a = 1 in
    let b = 10000000 in
    let lst = range a b [] in
    let set = Hash_set.of_list (module Int) lst in
    let elt = 56708 in
    let start_time_list = Stdlib.Sys.time () in
    (* let _  *)
    let _ = List.exists ~f:(fun e -> e = elt) lst in
    let finish_time_list = Stdlib.Sys.time () in
    let _ = printf "List.exists: %f\n" (finish_time_list -. start_time_list) in
    let start_time_set = Stdlib.Sys.time () in
    let fl = Hash_set.mem set elt in
    let finish_time_set = Stdlib.Sys.time () in
    printf "Hash_set.mem: %f\n, %b" (finish_time_set -. start_time_set) fl
  ;;

  let%test "unit propagation1" =
    let f = [ [ 2 ]; [ 3 ]; [ 3; 5; -2 ]; [ 4; -2 ]; [ 5; 4; -3 ] ] in
    let units, _ = find_units_pures f in
    let actual = unit_propagation f units in
    let expected = [ [ 4; 5 ]; [ 4 ] ] in
    (* let _ = List.iter ~f:(fun cls -> List.iter ~f:(fun l -> printf "%d " l) cls) actual in *)
    Stdlib.(actual = expected)
  ;;

  let%test "unit propagation2" =
    let f = [ [ 1 ]; [ -1 ] ] in
    let units, _ = find_units_pures f in
    (* Hash_set.iter units ~f:(fun x -> Caml.print_int x); *)
    let actual = unit_propagation f units in
    let expected = [ [] ] in
    Stdlib.(actual = expected)
  ;;

  let%test "unit propagation3" =
    let f = [ [ 2 ]; [ -1 ]; [ -2; 1 ] ] in
    let units, _ = find_units_pures f in
    (* Hash_set.iter units ~f:(fun x -> Caml.print_int x); *)
    let actual = unit_propagation f units in
    let expected = [ [] ] in
    Stdlib.(actual = expected)
  ;;
>>>>>>> Stashed changes

  (* let min_elt hash =
    let exception Found of int in
    try
      Hash_set.iter hash ~f:(fun x -> raise (Found x));
      raise Caml.Not_found
<<<<<<< Updated upstream
    with Found x -> x

  let pure_literal_elimination pure_literals f =
    (* try *)
    (* let l = min_elt pure_literals in *)
    let clause_intersects pure_literals cls =
      let exception Found in
      try
        List.iter cls ~f:(fun lit ->
            if Hash_set.mem pure_literals lit then raise Found);
        false
      with Found -> true
    in
    (* let _ = Hash_set.remove pure_literals l in *)
    eliminate_pures (clause_intersects pure_literals) f
  (* with Caml.Not_found -> f *)
  (*ok?*)
=======
    with
    | Found x -> x
  ;; *)
>>>>>>> Stashed changes

  let choose f = List.hd_exn @@ List.hd_exn f
end

let solve f =
  (* let pure_literals = CNFFormula.get_pure_literals f in *)
  (* let _ =  *)
  let rec loop f acc : cnf_result =
<<<<<<< Updated upstream
    if CNFFormula.is_satisfiable f then Sat acc
    else if CNFFormula.does_contain_empty_clause f then Unsat
    else
      match CNFFormula.does_contain_unit_clause f with
      | Some unit_literals ->
          loop
            (CNFFormula.unit_propagation unit_literals f)
            (List.append unit_literals acc)
      | None -> (
          let pure_literals = CNFFormula.get_pure_literals f in
          (* let _ = List.filter f.clauses ~f:(fun cls -> ) *)
          if not (Hash_set.is_empty pure_literals) then
            (* let l = min_elt pure_literals in *)
            (* List.hd_exn @@ Hash_set.to_list pure_literals in *)
            (* let _ = Hash_set.remove pure_literals l in *)
            loop
              (CNFFormula.pure_literal_elimination pure_literals f)
              (List.append (Hash_set.to_list pure_literals) acc)
          else
            let l = CNFFormula.choose f in
            match loop (CNFFormula.substitute l f) (l :: acc) with
            | Unsat -> loop (CNFFormula.substitute (-l) f) (-l :: acc)
            | Sat acc -> Sat acc)
=======
    (* log_lst_lst f; *)
    let units, pures = CNFFormula.find_units_pures f in
    let f = CNFFormula.unit_propagation f units in
    if CNFFormula.is_satisfiable f
    then Sat (List.append (Hash_set.to_list units) acc)
    else if CNFFormula.contains_empty_clause f
    then Unsat
    else (
      let f = CNFFormula.eliminate_pures f pures in
      if CNFFormula.is_satisfiable f
      then
        Sat
          (List.append
             (List.append (Hash_set.to_list units) acc)
             (Hash_set.to_list pures))
      else if CNFFormula.contains_empty_clause f
      then Unsat
      else (
        let l = CNFFormula.choose f in
        match loop (CNFFormula.substitute f l) (l :: acc) with
        | Unsat -> loop (CNFFormula.substitute f (-l)) (-l :: acc)
        | Sat acc -> Sat acc))
>>>>>>> Stashed changes
  in
  loop f []

let print_model = function
  | None -> print_endline "Error during parsing file"
<<<<<<< Updated upstream
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
=======
  | Some cnf_res ->
    (match cnf_res with
     | Unsat -> print_endline "Unsat"
     | Sat res ->
       let _ = print_endline "Sat" in
       List.iter ~f:(fun model_lit -> printf "%d " model_lit) res)
;;

let main ~path =
  match parse_cnf ~path with
  | Some clx -> Some (solve clx)
  | _ -> None
;;

(* let%test "UNSAT" =
  match main ~path:"/home/cy/Desktop/ocaml-rep/dpll_ocaml/TestFiles/unsat_1_2.txt" with
  | Some ans ->
    (match ans with
     | Sat _ -> false
     | Unsat -> true)
  | None -> true
;; *)
>>>>>>> Stashed changes
