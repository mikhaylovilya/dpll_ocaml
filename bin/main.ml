open Base
open Stdio

let debug_mode = 1

(* exception Myexn *)

(* type mystruct = int list list *)
type cnf_options = { vars_num : int; cls_num : int }
(* type cnf_result = Sat | Unsat Sat of ... *)

module CNFFormula = struct
  type t = { cnf_options : cnf_options; clauses : int list list }

  let is_satisfiable : t -> bool = fun f -> List.length f.clauses = 0

  let does_contain_empty_clause f =
    let rec helper = function
      | [] -> false
      | hd :: tl -> if List.length hd = 0 then true else helper tl
    in
    helper f.clauses

  let does_contain_unit_clause f =
    let rec helper = function
      | [] -> None
      | hd :: tl -> if List.length hd = 1 then List.hd hd else helper tl
    in
    helper f.clauses

  let substitute l f =
    let no_pure_appearence =
      List.filter f.clauses ~f:(fun cls ->
          phys_equal cls (List.filter cls ~f:(fun lit -> not (lit = l))))
    in
    let no_appearence =
      List.map no_pure_appearence ~f:(fun cls ->
          List.filter cls ~f:(fun lit -> not (lit = -l)))
    in
    { cnf_options = f.cnf_options; clauses = no_appearence }

  let unit_propagation l f =
    let no_unit_clx =
      List.filter f.clauses ~f:(fun cls ->
          (not (List.length cls = 1)) || not (List.hd_exn cls = l))
    in
    substitute l { cnf_options = f.cnf_options; clauses = no_unit_clx }

  (* let does_contain_pure_literal : t -> int option = fun f -> None *)
  let does_contain_pure_literal l f = None
end

let log str = if debug_mode = 1 then Caml.Format.printf "%s\n" str

let log_lst lst =
  if debug_mode = 1 then
    Caml.Format.printf "%s\n"
    @@ List.fold_right lst
         ~f:(fun x acc -> String.concat ~sep:" " [ x; acc ])
         ~init:""

let insert ~cls ~acc = cls :: acc

let parse_cnf ~path =
  let ic = In_channel.create path in
  let parse_headers () =
    match In_channel.input_line ic with
    | None -> None
    | Some x -> (
        match String.split_on_chars ~on:[ ' ' ] x with
        | [ "p"; "cnf"; vars_num; cls_num ] ->
            let _ = log_lst [ vars_num; cls_num ] in
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
            let _ = log_lst line in
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

let main ~path =
  let hdr, clx = parse_cnf ~path in
  (hdr, clx)
