open Base
open Stdio

type formula = int list list
type cnf_result = Unsat | Sat of int list

let parse_cnf ~path =
  let ic = In_channel.create path in
  let _ = In_channel.input_line ic in
  let rec parse_clauses acc =
    match In_channel.input_line ic with
    | None -> Some acc
    | Some x -> (
        match List.tl @@ List.rev @@ String.split_on_chars ~on:[ ' ' ] x with
        | None -> None
        | Some line ->
            parse_clauses @@ (List.map line ~f:(fun s -> Int.of_string s) :: acc)
        )
  in
  try
    let cls = parse_clauses [] in
    In_channel.close ic;
    cls
  with Failure e ->
    In_channel.close ic;
    None

module CNFFormula = struct
  type t = formula

  let is_satisfiable f = match f with [] -> true | _ -> false

  let contains_empty_clause f =
    let rec helper = function
      | [] -> false
      | hd :: tl -> ( match hd with [] -> true | _ -> helper tl)
    in
    helper f

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
          | [ l ]
            when (not (Hash_set.mem units l)) && not (Hash_set.mem units (-l))
            ->
              Hash_set.add units l
          | _ -> ())
    in
    (units, pures)

  let%test "pures" =
    let f = [ [ 2 ]; [ 3; 5; -2 ]; [ 4 ] ] in
    let _, pures = find_units_pures f in
    let expected = Hash_set.of_list (module Int) [ 3; 5; 4 ] in
    Hash_set.equal expected pures

  let eliminate_pures f pures =
    List.filter f ~f:(fun cl ->
        not (List.exists cl ~f:(fun l -> Hash_set.mem pures l)))

  let%test "eliminate pures" =
    let f = [ [ 2 ]; [ 3; 5; -2 ]; [ 4; -2 ] ] in
    let _, pures = find_units_pures f in
    let expected = [ [ 2 ] ] in
    let actual = eliminate_pures f pures in
    Stdlib.(actual = expected)

  let substitute f lit =
    List.filter_map f ~f:(fun cl ->
        let exception Found of int in
        try
          List.iter cl ~f:(fun l -> if l = lit || l = -lit then raise (Found l));
          Some cl
        with Found l ->
          if l = lit then None
          else Some (List.filter cl ~f:(fun l1 -> not (l1 = l))))

  let%test "subs" =
    let f = [ [ 2; -5 ]; [ 3; 5; -2 ]; [ 4; -2 ] ] in
    let actual = substitute f 2 in
    let expected = [ [ 3; 5 ]; [ 4 ] ] in
    Stdlib.(actual = expected)

  let unit_propagation f units =
    List.rev_filter_map f ~f:(fun cl ->
        let exception Found of int in
        try
          Some
            (List.rev_filter cl ~f:(fun l ->
                 if Hash_set.mem units l then raise (Found l)
                 else not (Hash_set.mem units (-l))))
        with Found l -> None)

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

  let%test "unit propagation1" =
    let f = [ [ 2 ]; [ 3 ]; [ 3; 5; -2 ]; [ 4; -2 ]; [ 5; 4; -3 ] ] in
    let units, _ = find_units_pures f in
    let actual = unit_propagation f units in
    let expected = [ [ 4; 5 ]; [ 4 ] ] in
    (* let _ = List.iter ~f:(fun cls -> List.iter ~f:(fun l -> printf "%d " l) cls) actual in *)
    Stdlib.(actual = expected)

  let%test "unit propagation2" =
    let f = [ [ 1 ]; [ -1 ] ] in
    let units, _ = find_units_pures f in
    (* Hash_set.iter units ~f:(fun x -> Caml.print_int x); *)
    let actual = unit_propagation f units in
    let expected = [ [] ] in
    Stdlib.(actual = expected)

  let%test "unit propagation3" =
    let f = [ [ 2 ]; [ -1 ]; [ -2; 1 ] ] in
    let units, _ = find_units_pures f in
    (* Hash_set.iter units ~f:(fun x -> Caml.print_int x); *)
    let actual = unit_propagation f units in
    let expected = [ [] ] in
    Stdlib.(actual = expected)

  (* let min_elt hash =
       let exception Found of int in
       try
         Hash_set.iter hash ~f:(fun x -> raise (Found x));
         raise Caml.Not_found
       with
       | Found x -> x
     ;; *)

  let choose f = List.hd_exn @@ List.hd_exn f
end

let solve f =
  (* let pure_literals = CNFFormula.get_pure_literals f in *)
  (* let _ =  *)
  let rec loop f acc : cnf_result =
    (* log_lst_lst f; *)
    let units, pures = CNFFormula.find_units_pures f in
    let f = CNFFormula.unit_propagation f units in
    if CNFFormula.is_satisfiable f then
      Sat (List.append (Hash_set.to_list units) acc)
    else if CNFFormula.contains_empty_clause f then Unsat
    else
      let f = CNFFormula.eliminate_pures f pures in
      if CNFFormula.is_satisfiable f then
        Sat
          (List.append
             (List.append (Hash_set.to_list units) acc)
             (Hash_set.to_list pures))
      else if CNFFormula.contains_empty_clause f then Unsat
      else
        let l = CNFFormula.choose f in
        match loop (CNFFormula.substitute f l) (l :: acc) with
        | Unsat -> loop (CNFFormula.substitute f (-l)) (-l :: acc)
        | Sat acc -> Sat acc
  in
  loop f []

let print_model = function
  | None -> print_endline "Error during parsing file"
  | Some cnf_res -> (
      match cnf_res with
      | Unsat -> print_endline "Unsat"
      | Sat res ->
          let _ = print_endline "Sat" in
          List.iter ~f:(fun model_lit -> printf "%d " model_lit) res)

let main ~path =
  match parse_cnf ~path with Some clx -> Some (solve clx) | _ -> None

(* let%test "UNSAT" =
     match main ~path:"/home/cy/Desktop/ocaml-rep/dpll_ocaml/TestFiles/unsat_1_2.txt" with
     | Some ans ->
       (match ans with
        | Sat _ -> false
        | Unsat -> true)
     | None -> true
   ;; *)
