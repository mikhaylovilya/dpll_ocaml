open Base
open Stdio

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

let parse_cnf ~path =
  let ic = In_channel.create path in
  let parse_headers () =
    match In_channel.input_line ic with
    | None -> None
    | Some x ->
      (match String.split_on_chars ~on:[ ' ' ] x with
       | [ "p"; "cnf"; vars_num; cls_num ] ->
         Some { vars_num = Int.of_string vars_num; cls_num = Int.of_string cls_num }
       | _ -> None)
  in
  let rec parse_clauses acc =
    match In_channel.input_line ic with
    | None -> Some acc
    | Some x ->
      (match List.tl @@ List.rev @@ String.split_on_chars ~on:[ ' ' ] x with
       | None -> None
       | Some line -> parse_clauses @@ (List.map line ~f:(fun s -> Int.of_string s) :: acc))
  in
  try
    let opts = parse_headers () in
    let cls = parse_clauses [] in
    let _ = In_channel.close ic in
    opts, cls
  with
  | Failure e ->
    In_channel.close ic;
    None, None
;;

module CNFFormula = struct
  type t = formula

  let is_empty f =
    match f.clauses with
    | [] -> true
    | _ -> false
  ;;

  let contains_empty_clause f =
    let rec helper = function
      | [] -> false
      | hd :: tl ->
        (match hd with
         | [] -> true
         | _ -> helper tl)
    in
    helper f.clauses
  ;;

  (* let rec find_units_pures1 f units pures all =
     (* let rec helper f acc = *)
     match f.clauses with
     | [] -> (units, pures)
     | cls :: clx -> (
         match cls with
         | [ l ] ->
             find_units_pures1 { f with clauses = clx } (l :: units) pures
               (l :: all)
         | cls ->
             let new_pures =
               List.rev_filter_map cls ~f:(fun lit ->
                   if List.exists pures ~f:(fun elt -> elt = -lit) then None
                   else )
             in
             find_units_pures1 { f with clauses = clx } units pures (l :: all)) *)

  let find_units_pures f =
    let pures = Hash_set.create ~size:f.cnf_options.vars_num (module Int) in
    let all = Hash_set.create ~size:f.cnf_options.vars_num (module Int) in
    let units = Hash_set.create ~size:f.cnf_options.cls_num (module Int) in
    let () =
      List.iter f.clauses ~f:(fun cl ->
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
          Hash_set.strict_add_exn units l
        | _ -> ())
    in
    units, pures
  ;;

  (* let%test "pures" =
     let f = [ [ 2 ]; [ 3; 5; -2 ]; [ 4 ] ] in
     let _, pures = find_units_pures f in
     let expected = Hash_set.of_list (module Int) [ 3; 5; 4 ] in
     Hash_set.equal expected pures *)

  let eliminate_pures f pures =
    { f with
      clauses =
        List.rev_filter f.clauses ~f:(fun cl ->
          not (List.exists cl ~f:(fun l -> Hash_set.mem pures l)))
    }
  ;;

  (* let%test "eliminate pures" =
     let f = [ [ 2 ]; [ 3; 5; -2 ]; [ 4; -2 ] ] in
     let _, pures = find_units_pures f in
     let expected = [ [ 2 ] ] in
     let actual = eliminate_pures f pures in
     Stdlib.(actual = expected) *)

  let substitute f lit =
    { f with
      clauses =
        List.rev_filter_map f.clauses ~f:(fun cl ->
          let exception Found of int in
          try
            Some
              (List.rev_filter cl ~f:(fun l ->
                 if l = lit then raise (Found l) else not (l = -lit)))
          with
          | Found l -> None)
    }
  ;;

  (* let%test "subs" =
     let f = [ [ 2; -5 ]; [ 3; 5; -2 ]; [ 4; -2 ] ] in
     let actual = substitute f 2 in
     let expected = [ [ 3; 5 ]; [ 4 ] ] in
     Stdlib.(actual = expected) *)

  let unit_propagation f units =
    { f with
      clauses =
        List.rev_filter_map f.clauses ~f:(fun cl ->
          let exception Found of int in
          try
            Some
              (List.rev_filter cl ~f:(fun l ->
                 if Hash_set.mem units l
                 then raise (Found l)
                 else not (Hash_set.mem units (-l))))
          with
          | Found l -> None)
    }
  ;;

  (* let hash_set_list () =
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
     printf "Hash_set.mem: %f\n, %b" (finish_time_set -. start_time_set) fl *)

  (* let%test "unit propagation1" =
     let f = [ [ 2 ]; [ 3 ]; [ 3; 5; -2 ]; [ 4; -2 ]; [ 5; 4; -3 ] ] in
     let units, _ = find_units_pures f in
     let actual = unit_propagation f units in
     let expected = [ [ 4; 5 ]; [ 4 ] ] in
     (* let _ = List.iter ~f:(fun cls -> List.iter ~f:(fun l -> printf "%d " l) cls) actual in *)
     Stdlib.(actual = expected) *)

  (* let%test "unit propagation2" =
     let f = [ [ 1 ]; [ -1 ] ] in
     let units, _ = find_units_pures f in
     (* Hash_set.iter units ~f:(fun x -> Caml.print_int x); *)
     let actual = unit_propagation f units in
     let expected = [ [] ] in
     Stdlib.(actual = expected) *)

  (* let%test "unit propagation3" =
     let f = [ [ 2 ]; [ -1 ]; [ -2; 1 ] ] in
     let units, _ = find_units_pures f in
     (* Hash_set.iter units ~f:(fun x -> Caml.print_int x); *)
     let actual = unit_propagation f units in
     let expected = [ [] ] in
     Stdlib.(actual = expected) *)

  (* let min_elt hash =
       let exception Found of int in
       try
         Hash_set.iter hash ~f:(fun x -> raise (Found x));
         raise Caml.Not_found
       with
       | Found x -> x
     ;; *)

  (* let choose1 f =
       let occurences = Hashtbl.create (module Int) in
       List.iter f.clauses ~f:(fun cls ->
           List.iter cls ~f:(fun lit ->
               match Hashtbl.find occurences (abs lit) with
               | Some v -> Hashtbl.set occurences ~key:(abs lit) ~data:(v + 1)
               | None -> Hashtbl.add_exn occurences ~key:(abs lit) ~data:1));
       let elt = List.max_elt (Hashtbl.data occurences) ~compare:Int.compare in
       match elt with Some x -> x | None -> raise (Failure "")

     let%test "choose1 1" =
       let f =
         {
           cnf_options = { vars_num = 0; cls_num = 0 };
           clauses = [ [ 3; -2; 1; -4 ]; [ -1 ]; [ -2; 1; -4 ]; [ 3 ] ];
         }
       in
       let actual = choose1 f in
       (* Hash_set.iter units ~f:(fun x -> Caml.print_int x); *)
       let expected = 1 in
       Stdlib.(actual = expected) *)

  let choose f = List.hd_exn @@ List.hd_exn f.clauses
end

let solve f =
  let exception Sat_exn of int list in
  let exception Unsat_exn in
  let rec loop f acc : cnf_result =
    let rec simplify f acc =
      if CNFFormula.is_empty f
      then raise (Sat_exn acc)
      else if CNFFormula.contains_empty_clause f
      then raise Unsat_exn
      else (
        let units, pures = CNFFormula.find_units_pures f in
        match Hash_set.is_empty units, Hash_set.is_empty pures with
        | false, false ->
          let f = CNFFormula.unit_propagation f units in
          simplify
            (CNFFormula.eliminate_pures f pures)
            (Hash_set.to_list units @ Hash_set.to_list pures @ acc)
        | false, true ->
          simplify (CNFFormula.unit_propagation f units) (Hash_set.to_list units @ acc)
        | true, false ->
          simplify (CNFFormula.eliminate_pures f pures) (Hash_set.to_list pures @ acc)
        | true, true -> f, acc)
    in
    match simplify f acc with
    | exception Sat_exn res -> Sat res
    | exception Unsat_exn -> Unsat
    | f, acc ->
      if CNFFormula.is_empty f
      then Sat acc
      else if CNFFormula.contains_empty_clause f
      then Unsat
      else (
        let l = CNFFormula.choose f in
        match loop (CNFFormula.substitute f l) (l :: acc) with
        | Unsat -> loop (CNFFormula.substitute f (-l)) (-l :: acc)
        | Sat acc -> Sat acc)
  in
  loop f []
;;

let print_model = function
  | None -> print_endline "Error during parsing file"
  | Some cnf_res ->
    (match cnf_res with
     | Unsat -> print_endline "\nUnsat"
     | Sat res ->
       let _ = print_endline "\nSat" in
       List.iter
         ~f:(fun model_lit -> printf "%d " model_lit)
         (List.sort res ~compare:(fun greater lesser ->
            if greater = lesser
            then 0
            else if Int.abs greater > Int.abs lesser
            then 1
            else -1));
       print_endline "")
;;

let main ~path =
  match parse_cnf ~path with
  | Some opts, Some clx -> Some (solve { cnf_options = opts; clauses = clx })
  | _ -> None
;;

let _ = print_model @@ main ~path:(Sys.get_argv ()).(1)

(* let%test "UNSAT" =
     match main ~path:"/home/cy/Desktop/ocaml-rep/dpll_ocaml/TestFiles/unsat_1_2.txt" with
     | Some ans ->
       (match ans with
        | Sat _ -> false
        | Unsat -> true)
     | None -> true
   ;; *)
