open Main

let path = "../TestFiles/"

(* let list_txt =
     Sys.readdir path |> Array.to_list
     |> List.filter_map (fun x ->
            match Filename.extension x = ".txt" with
            | true -> Some (path ^ x)
            | false -> None)

   (* let _ = List.iter list_txt ~f: *)
   let _ = List.iter (fun x -> print_model @@ main ~path:x) list_txt *)
let _ = print_model @@ main ~path:(path ^ "sat_20_91.txt")
let _ = print_model @@ main ~path:(path ^ "sat_50_80.txt")
let _ = print_model @@ main ~path:(path ^ "sat_50_170.txt")
let _ = print_model @@ main ~path:(path ^ "sat_50_80_2.txt")
let _ = print_model @@ main ~path:(path ^ "sat_100_449.txt")
let _ = print_model @@ main ~path:(path ^ "sat_100_499.txt")

(*  *)
let _ = print_model @@ main ~path:(path ^ "unsat_1_2.txt")
let _ = print_model @@ main ~path:(path ^ "unsat_2_3.txt")
let _ = print_model @@ main ~path:(path ^ "unsat_50_100.txt")
let _ = print_model @@ main ~path:(path ^ "unsat_100_200.txt")
