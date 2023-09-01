open Main

let () = print_model @@ main ~path:"../TestFiles/example.txt"
let () = print_model @@ main ~path:"../TestFiles/examplePureLiteral.txt"
let () = print_model @@ main ~path:"../TestFiles/exampleUnitLiteral.txt"
