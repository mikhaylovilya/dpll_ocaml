  $ dune exec ./main.exe ds ./testfiles/sat_20_91.txt
  $ picosat -f dpll_ocaml_dimacs_sat_20_91.txt | grep SATISFIABLE
  s SATISFIABLE
  $ dune exec ./main.exe ds ./testfiles/sat_50_80.txt
  $ picosat -f dpll_ocaml_dimacs_sat_50_80.txt | grep SATISFIABLE
  s SATISFIABLE
  $ dune exec ./main.exe ds ./testfiles/sat_50_80_2.txt
  $ picosat -f dpll_ocaml_dimacs_sat_50_80_2.txt | grep SATISFIABLE
  s SATISFIABLE
  $ dune exec ./main.exe ds ./testfiles/sat_50_170.txt
  $ picosat -f dpll_ocaml_dimacs_sat_50_170.txt | grep SATISFIABLE
  s SATISFIABLE
  $ dune exec ./main.exe ds ./testfiles/sat_100_449.txt
  $ picosat -f dpll_ocaml_dimacs_sat_100_449.txt | grep SATISFIABLE
  s SATISFIABLE
  $ dune exec ./main.exe ds ./testfiles/sat_100_499.txt
  $ picosat -f dpll_ocaml_dimacs_sat_100_499.txt | grep SATISFIABLE
  s SATISFIABLE

  $ dune exec ./main.exe ds ./testfiles/unsat_1_2.txt
  Unsat
  $ picosat ./testfiles/unsat_1_2.txt
  s UNSATISFIABLE
  [20]
  $ dune exec ./main.exe ds ./testfiles/unsat_2_3.txt
  Unsat
  $ picosat ./testfiles/unsat_2_3.txt
  s UNSATISFIABLE
  [20]
  $ dune exec ./main.exe ds ./testfiles/unsat_50_100.txt
  Unsat
  $ picosat ./testfiles/unsat_50_100.txt
  s UNSATISFIABLE
  [20]
  $ dune exec ./main.exe ds ./testfiles/unsat_100_200.txt
  Unsat
  $ picosat ./testfiles/unsat_100_200.txt
  s UNSATISFIABLE
  [20]
