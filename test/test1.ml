(* let _ = does_contain_pure_literal main () *)
open Main

let _ = main ~path:"../TestFiles/example.txt"
let _ = main ~path:"../TestFiles/examplePureLiteral.txt"
let _ = main ~path:"../TestFiles/exampleUnitLiteral.txt"
