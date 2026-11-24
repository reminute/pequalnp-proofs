import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi

namespace G11Certificate

def edgeRows : List (Fin 11 × Fin 11) := [
  (0, 9),
  (0, 10),
  (1, 4),
  (1, 8),
  (2, 5),
  (2, 10),
  (3, 6),
  (3, 7),
  (4, 8),
  (4, 10),
  (5, 8),
  (5, 9),
  (6, 7),
  (6, 10),
  (7, 9),
  (8, 9)]

def negativeRows : List (Finset (Fin 11)) := [
  {0, 1, 2, 3},
  {0, 2, 3, 4},
  {0, 1, 3, 5},
  {0, 3, 4, 5},
  {0, 1, 2, 6},
  {0, 2, 4, 6},
  {0, 1, 5, 6},
  {0, 4, 5, 6},
  {0, 1, 2, 7},
  {0, 2, 4, 7},
  {0, 1, 5, 7},
  {0, 4, 5, 7},
  {0, 2, 3, 8},
  {0, 2, 6, 8},
  {0, 2, 7, 8},
  {1, 2, 3, 9},
  {2, 3, 4, 9},
  {1, 2, 6, 9},
  {2, 4, 6, 9},
  {1, 3, 5, 10},
  {1, 5, 7, 10},
  {3, 8, 10},
  {7, 8, 10},
  {1, 3, 9, 10}]

def patternRows : List (Finset (Fin 16)) := [
  {0, 2, 4},
  {1, 3, 6},
  {5, 7, 8},
  {9, 10, 12},
  {2, 11, 13},
  {4, 13, 14},
  {1, 7, 15},
  {5, 6, 15},
  {0, 3, 12},
  {3, 9, 11},
  {2, 10, 14},
  {0, 6, 8},
  {4, 8, 12},
  {0, 10, 13},
  {5, 11, 12},
  {6, 9, 14},
  {2, 13, 15},
  {1, 3, 14},
  {4, 7, 9},
  {1, 8, 9, 11},
  {3, 7, 11},
  {0, 5, 8, 15},
  {1, 6, 10},
  {0, 2, 12},
  {1, 3, 4},
  {8, 13, 14},
  {0, 4, 6},
  {2, 4, 6},
  {1, 10, 14}]

def witnessRows : List (List (Fin 24)) := [
  [0, 1, 2, 3, 15],
  [0, 4, 12, 13, 19],
  [0, 9, 14, 19, 20],
  [6, 9, 13, 20, 22],
  [1, 6, 17, 19, 23],
  [6, 8, 17, 20, 23],
  [0, 8, 20, 21, 23],
  [0, 13, 17, 21, 23],
  [4, 8, 13, 14, 15],
  [3, 16, 19, 21, 23],
  [10, 11, 14, 15, 16],
  [0, 5, 13, 15, 17],
  [1, 6, 10, 13, 14],
  [6, 13, 17, 19, 21],
  [6, 8, 17, 20, 23],
  [9, 16, 17, 20, 23],
  [13, 16, 17, 21, 23],
  [0, 12, 20, 21, 23],
  [0, 2, 8, 11, 20],
  [3, 12, 16, 19, 23],
  [2, 8, 12, 14, 15],
  [1, 12, 15, 21, 23],
  [0, 6, 13, 19, 21],
  [0, 5, 9, 15, 16],
  [0, 2, 12, 19, 21],
  [9, 13, 18, 22, 23],
  [0, 2, 4, 6, 15],
  [0, 1, 2, 3, 4],
  [2, 12, 20, 22, 23]]

def edgeAt (e : Fin 16) : Fin 11 × Fin 11 := edgeRows.getD e.val (0,0)
def edge (e : Fin 16) : Finset (Fin 11) := {(edgeAt e).1,(edgeAt e).2}
def negative (i : Fin 24) : Finset (Fin 11) := negativeRows.getD i.val ∅
def needed (k : Fin 29) : Finset (Fin 16) := patternRows.getD k.val ∅
def witness (k : Fin 29) (i : Fin 5) : Fin 24 := (witnessRows.getD k.val []).getD i.val 0

inductive Certificate where
  | small
  | found (k : Fin 29)
  | split (e : Fin 16) (yes no : Certificate)

open Certificate

def part0 : Certificate := (split 12 (found 12) small)

def part1 : Certificate := (split 14 (found 5) small)

def part2 : Certificate := (split 9 (found 18) (split 15 (found 6) (split 8 (split 5 (found 2) part0) (split 13 part1 small))))

def part3 : Certificate := (split 12 (split 8 (found 12) small) small)

def part4 : Certificate := (split 11 (found 14) small)

def part5 : Certificate := (split 14 (split 13 (found 5) (split 9 (found 15) (split 5 part3 small))) (split 5 (split 12 (split 8 (found 12) part4) (split 15 (found 7) small)) (split 8 (split 12 (found 12) small) small)))

def part6 : Certificate := (split 3 (found 1) (split 10 (found 22) (split 2 (found 27) (split 7 part2 part5))))

def part7 : Certificate := (split 10 (found 3) small)

def part8 : Certificate := (split 15 (found 7) small)

def part9 : Certificate := (split 12 (split 5 (split 11 (found 14) (split 8 (found 12) part7)) (split 8 (found 12) (split 10 (found 3) small))) (split 3 (split 11 (found 9) (split 5 part8 small)) (split 5 (split 15 (found 7) small) small)))

def part10 : Certificate := (split 15 (found 7) small)

def part11 : Certificate := (split 12 (found 12) (split 7 (found 2) (split 13 (split 14 (found 5) part10) (split 15 (found 7) small))))

def part12 : Certificate := (split 7 (found 20) small)

def part13 : Certificate := (split 15 (found 7) (split 11 (split 12 (found 14) (split 3 part12 small)) (split 13 (split 14 (found 5) small) small)))

def part14 : Certificate := (split 7 (split 11 (found 20) small) small)

def part15 : Certificate := (split 11 (found 20) small)

def part16 : Certificate := (split 12 (found 12) (split 13 (split 14 (found 5) (split 3 part14 small)) (split 3 (split 7 part15 small) small)))

def part17 : Certificate := (split 11 (found 20) small)

def part18 : Certificate := (split 13 (split 14 (found 5) (split 3 (split 7 part17 small) small)) (split 3 (split 7 (split 11 (found 20) small) small) small))

def part19 : Certificate := (split 2 (found 27) (split 9 (split 14 (found 15) (split 7 (found 18) part9)) (split 5 (split 8 part11 part13) (split 8 part16 part18))))

def part20 : Certificate := (split 12 (found 12) small)

def part21 : Certificate := (split 3 (found 24) small)

def part22 : Certificate := (split 3 (found 24) small)

def part23 : Certificate := (split 7 (split 9 (found 18) (split 8 (split 5 (found 2) part20) (split 1 part21 small))) (split 12 (split 8 (found 12) (split 1 part22 small)) (split 1 (split 3 (found 24) small) small)))

def part24 : Certificate := (split 14 (found 10) (split 12 (found 12) small))

def part25 : Certificate := (split 12 (found 12) small)

def part26 : Certificate := (split 15 (found 6) small)

def part27 : Certificate := (split 9 (found 18) (split 8 (split 5 (found 2) (split 10 part24 part25)) (split 10 (split 14 (found 10) part26) (split 15 (found 6) small))))

def part28 : Certificate := (split 9 (found 3) small)

def part29 : Certificate := (split 9 (split 11 (found 19) small) small)

def part30 : Certificate := (split 11 (found 19) small)

def part31 : Certificate := (split 12 (found 14) small)

def part32 : Certificate := (split 10 (split 14 (found 10) (split 12 (split 8 (found 12) part28) (split 8 part29 small))) (split 8 (split 12 (found 12) (split 9 part30 small)) (split 5 (split 11 part31 small) small)))

def part33 : Certificate := (split 11 (found 20) small)

def part34 : Certificate := (split 12 (found 14) small)

def part35 : Certificate := (split 8 (split 5 (found 2) (split 12 (found 12) (split 3 part33 small))) (split 11 (split 3 (found 20) (split 5 part34 small)) (split 10 (split 14 (found 10) small) small)))

def part36 : Certificate := (split 8 (found 12) (split 10 (split 9 (found 3) (split 14 (found 10) small)) (split 11 (split 5 (found 14) small) small)))

def part37 : Certificate := (split 11 (found 9) small)

def part38 : Certificate := (split 10 (split 14 (found 10) (split 3 (split 9 part37 small) small)) (split 3 (split 9 (split 11 (found 9) small) small) small))

def part39 : Certificate := (split 13 (split 14 (found 5) (split 11 (found 4) (split 15 (found 16) part23))) (split 1 (split 3 (found 24) (split 7 part27 part32)) (split 7 (split 9 (found 18) part35) (split 12 part36 part38))))

def part40 : Certificate := (split 11 (found 9) (split 0 (found 8) (split 7 (found 18) (split 10 (found 3) small))))

def part41 : Certificate := (split 0 (found 8) (split 11 (split 5 (found 14) (split 7 (found 20) small)) (split 13 (split 14 (found 5) small) small)))

def part42 : Certificate := (split 10 (found 13) small)

def part43 : Certificate := (split 11 (found 20) (split 13 (split 14 (found 5) (split 0 part42 small)) (split 5 (split 8 (found 2) small) small)))

def part44 : Certificate := (split 11 (found 9) small)

def part45 : Certificate := (split 14 (found 5) (split 0 (split 10 (found 13) (split 9 part44 small)) (split 9 (split 11 (found 9) small) small)))

def part46 : Certificate := (split 8 (split 15 (found 21) small) small)

def part47 : Certificate := (split 15 (found 21) small)

def part48 : Certificate := (split 9 (split 11 (found 9) (split 0 (split 5 part46 small) small)) (split 0 (split 5 (split 8 part47 small) small) small))

def part49 : Certificate := (split 1 (found 24) (split 12 (split 8 (found 12) (split 9 part40 part41)) (split 7 (split 9 (found 18) part43) (split 13 part45 part48))))

def part50 : Certificate := (split 10 (found 13) small)

def part51 : Certificate := (split 13 (split 14 (found 5) (split 12 (found 12) (split 0 part50 small))) (split 12 (found 12) (split 1 (split 15 (found 6) small) small)))

def part52 : Certificate := (split 13 (found 13) small)

def part53 : Certificate := (split 14 (split 10 (found 28) (split 13 (found 5) (split 15 (found 6) small))) (split 15 (found 6) (split 0 (split 10 part52 small) small)))

def part54 : Certificate := (split 13 (split 14 (found 5) (split 0 (split 10 (found 13) small) small)) (split 5 (split 11 (split 12 (found 14) small) small) small))

def part55 : Certificate := (split 9 (found 3) (split 13 (split 14 (found 5) (split 0 (found 13) small)) (split 1 (split 14 (found 28) small) small)))

def part56 : Certificate := (split 5 (split 11 (found 14) (split 13 (split 14 (found 5) small) small)) (split 13 (split 14 (found 5) small) small))

def part57 : Certificate := (split 15 (found 21) small)

def part58 : Certificate := (split 11 (found 19) small)

def part59 : Certificate := (split 0 (split 10 (found 13) (split 5 (split 8 part57 small) small)) (split 1 (split 8 (split 9 part58 small) small) small))

def part60 : Certificate := (split 11 (found 19) small)

def part61 : Certificate := (split 10 (split 14 (found 28) (split 8 (split 9 part60 small) small)) (split 8 (split 9 (split 11 (found 19) small) small) small))

def part62 : Certificate := (split 0 (split 5 (split 8 (split 15 (found 21) small) small) small) small)

def part63 : Certificate := (split 7 (split 8 (split 5 (found 2) (split 9 (found 18) part51)) (split 9 (found 18) (split 1 part53 part54))) (split 12 (split 8 (found 12) (split 10 part55 part56)) (split 13 (split 14 (found 5) part59) (split 1 part61 part62))))

def part64 : Certificate := (split 13 (found 4) small)

def part65 : Certificate := (split 10 (found 13) small)

def part66 : Certificate := (split 8 (split 15 (found 21) small) small)

def part67 : Certificate := (split 12 (split 0 (found 8) (split 5 (found 14) (split 2 part64 small))) (split 13 (split 2 (found 4) (split 0 part65 small)) (split 0 (split 5 part66 small) small)))

def part68 : Certificate := (split 10 (found 13) small)

def part69 : Certificate := (split 8 (found 21) small)

def part70 : Certificate := (split 7 (split 8 (found 2) small) small)

def part71 : Certificate := (split 8 (found 2) small)

def part72 : Certificate := (split 15 (split 7 (found 6) (split 13 (split 2 (found 16) part68) (split 5 part69 small))) (split 10 (split 13 (found 13) (split 5 part70 small)) (split 5 (split 7 part71 small) small)))

def part73 : Certificate := (split 10 (split 12 (found 3) small) small)

def part74 : Certificate := (split 12 (found 3) small)

def part75 : Certificate := (split 15 (found 6) (split 5 (split 8 (found 2) (split 9 part73 small)) (split 9 (split 10 part74 small) small)))

def part76 : Certificate := (split 10 (split 12 (found 3) small) small)

def part77 : Certificate := (split 12 (found 3) small)

def part78 : Certificate := (split 2 (split 13 (split 15 (found 16) (split 9 part76 small)) (split 9 (split 10 part77 small) small)) (split 9 (split 10 (split 12 (found 3) small) small) small))

def part79 : Certificate := (split 14 (found 17) (split 11 (split 7 (found 20) (split 9 (found 9) part67)) (split 0 (split 12 (found 8) part72) (split 7 part75 part78))))

def part80 : Certificate := (split 8 (found 2) (split 11 (found 14) small))

def part81 : Certificate := (split 11 (found 14) small)

def part82 : Certificate := (split 15 (found 6) small)

def part83 : Certificate := (split 0 (split 2 (found 23) (split 5 (split 7 part80 part81) (split 13 (found 13) small))) (split 5 (split 11 (found 14) (split 7 part82 small)) (split 15 (split 7 (found 6) small) small)))

def part84 : Certificate := (split 0 (found 13) (split 2 (split 15 (found 16) (split 11 (found 4) small)) (split 7 (split 15 (found 6) small) small)))

def part85 : Certificate := (split 7 (split 15 (found 6) (split 8 (split 5 (found 2) small) small)) (split 8 (split 9 (split 11 (found 19) small) small) small))

def part86 : Certificate := (split 14 (found 28) (split 6 (found 22) (split 12 (split 9 (found 3) part83) (split 13 part84 part85))))

def part87 : Certificate := (split 2 (found 4) (split 9 (found 19) small))

def part88 : Certificate := (split 9 (found 19) small)

def part89 : Certificate := (split 2 (found 16) small)

def part90 : Certificate := (split 0 (found 21) (split 6 (found 7) (split 11 (split 13 part87 part88) (split 13 part89 small))))

def part91 : Certificate := (split 2 (found 4) small)

def part92 : Certificate := (split 9 (found 19) (split 12 (found 14) (split 7 (found 2) (split 13 part91 small))))

def part93 : Certificate := (split 12 (found 23) small)

def part94 : Certificate := (split 7 (found 2) (split 0 (split 6 (found 11) (split 2 part93 small)) (split 14 (split 13 (found 25) small) small)))

def part95 : Certificate := (split 6 (found 11) small)

def part96 : Certificate := (split 11 (found 4) (split 15 (found 16) (split 14 (found 25) (split 0 part95 small))))

def part97 : Certificate := (split 15 (found 6) small)

def part98 : Certificate := (split 14 (found 25) (split 0 (split 6 (found 11) (split 7 part97 small)) (split 7 (split 15 (found 6) small) small)))

def part99 : Certificate := (split 15 (found 6) small)

def part100 : Certificate := (split 6 (found 11) (split 2 (split 12 (found 23) (split 7 part99 small)) (split 7 (split 15 (found 6) small) small)))

def part101 : Certificate := (split 9 (split 11 (found 19) (split 6 (split 14 (found 15) small) small)) (split 7 (split 15 (found 6) small) small))

def part102 : Certificate := (split 0 (found 23) small)

def part103 : Certificate := (split 7 (found 6) (split 5 (split 6 (found 7) (split 12 part102 small)) (split 0 (split 12 (found 23) small) small)))

def part104 : Certificate := (split 5 (split 6 (found 7) (split 11 (split 12 (found 14) small) small)) (split 6 (split 9 (split 14 (found 15) small) small) small))

def part105 : Certificate := (split 14 (found 15) small)

def part106 : Certificate := (split 12 (split 0 (found 23) (split 5 (found 14) (split 13 (found 4) small))) (split 13 (found 4) (split 6 (split 9 part105 small) small)))

def part107 : Certificate := (split 14 (found 15) small)

def part108 : Certificate := (split 0 (split 12 (found 23) (split 6 (split 9 part107 small) small)) (split 6 (split 9 (split 14 (found 15) small) small) small))

def part109 : Certificate := (split 14 (found 15) small)

def part110 : Certificate := (split 11 (split 12 (found 14) (split 6 (split 9 part109 small) small)) (split 6 (split 9 (split 14 (found 15) small) small) small))

def part111 : Certificate := (split 6 (split 9 (split 14 (found 15) small) small) small)

def part112 : Certificate := (split 8 (split 5 (split 15 (split 7 (found 2) part90) (split 11 part92 part94)) (split 13 (split 2 part96 part98) (split 0 part100 part101))) (split 15 (split 2 (split 13 (found 16) part103) (split 7 (found 6) part104)) (split 2 (split 11 part106 part108) (split 5 part110 part111))))

def part113 : Certificate := (split 9 (found 3) small)

def part114 : Certificate := (split 6 (found 11) (split 7 (found 2) (split 10 (split 13 (found 13) part113) (split 11 (found 14) small))))

def part115 : Certificate := (split 10 (split 9 (found 3) (split 11 (found 14) (split 13 (found 13) small))) (split 11 (found 14) (split 6 (split 15 (found 7) small) small)))

def part116 : Certificate := (split 9 (found 3) (split 13 (found 13) (split 6 (split 8 (found 11) small) small)))

def part117 : Certificate := (split 6 (split 8 (found 11) (split 9 (split 14 (found 15) small) small)) (split 8 (split 13 (split 14 (found 25) small) small) small))

def part118 : Certificate := (split 2 (found 23) (split 3 (found 8) (split 5 (split 8 part114 part115) (split 10 part116 part117))))

def part119 : Certificate := (split 10 (found 13) (split 11 (found 4) (split 15 (found 16) (split 14 (found 25) small))))

def part120 : Certificate := (split 5 (split 7 (found 2) (split 10 (found 13) (split 14 (found 25) small))) (split 10 (found 13) (split 14 (found 25) small)))

def part121 : Certificate := (split 14 (found 10) small)

def part122 : Certificate := (split 7 (found 2) (split 15 (found 21) (split 2 (split 10 part121 small) small)))

def part123 : Certificate := (split 14 (found 10) small)

def part124 : Certificate := (split 3 (split 11 (split 7 (found 20) (split 9 (found 9) small)) (split 2 (split 10 part123 small) small)) (split 2 (split 10 (split 14 (found 10) small) small) small))

def part125 : Certificate := (split 14 (found 15) small)

def part126 : Certificate := (split 11 (found 4) (split 15 (found 16) (split 6 (split 9 part125 small) small)))

def part127 : Certificate := (split 15 (found 7) small)

def part128 : Certificate := (split 3 (split 11 (split 9 (found 9) (split 7 (found 20) small)) (split 6 (split 5 part127 small) small)) (split 6 (split 5 (split 15 (found 7) small) small) small))

def part129 : Certificate := (split 14 (found 10) small)

def part130 : Certificate := (split 9 (found 9) (split 7 (found 20) (split 2 (split 10 part129 small) small)))

def part131 : Certificate := (split 10 (found 10) small)

def part132 : Certificate := (split 6 (split 14 (split 9 (found 15) (split 2 part131 small)) (split 5 (split 15 (found 7) small) small)) (split 2 (split 10 (split 14 (found 10) small) small) small))

def part133 : Certificate := (split 14 (split 9 (found 15) (split 2 (split 10 (found 10) small) small)) (split 5 (split 15 (found 7) small) small))

def part134 : Certificate := (split 2 (split 10 (split 14 (found 10) small) small) small)

def part135 : Certificate := (split 8 (split 6 (found 11) (split 13 (split 2 part119 part120) (split 5 part122 part124))) (split 13 (split 2 (split 10 (found 13) part126) (split 10 (found 13) part128)) (split 3 (split 11 part130 part132) (split 6 part133 part134))))

def part136 : Certificate := (split 15 (found 7) small)

def part137 : Certificate := (split 7 (found 20) (split 5 (split 12 (found 14) (split 6 part136 small)) (split 10 (split 14 (found 10) small) small)))

def part138 : Certificate := (split 10 (found 10) small)

def part139 : Certificate := (split 12 (found 14) (split 6 (split 14 (split 9 (found 15) part138) (split 15 (found 7) small)) (split 7 (split 8 (found 2) small) small)))

def part140 : Certificate := (split 10 (split 14 (found 10) (split 9 (split 12 (found 3) small) small)) (split 6 (split 9 (split 14 (found 15) small) small) small))

def part141 : Certificate := (split 5 (split 12 (found 14) (split 6 (split 15 (found 7) small) small)) (split 8 (split 13 (split 14 (found 25) small) small) small))

def part142 : Certificate := (split 6 (split 15 (found 7) (split 8 (split 7 (found 2) small) small)) (split 8 (split 7 (found 2) small) small))

def part143 : Certificate := (split 14 (split 6 (found 15) (split 8 (split 13 (found 25) small) small)) (split 10 (split 12 (found 3) small) small))

def part144 : Certificate := (split 8 (split 13 (split 14 (found 25) small) small) small)

def part145 : Certificate := (split 2 (split 13 (found 4) (split 3 (split 9 (found 9) part137) (split 5 part139 part140))) (split 3 (split 9 (found 9) (split 7 (found 20) part141)) (split 5 (split 12 (found 14) part142) (split 9 part143 part144))))

def part146 : Certificate := (split 8 (found 25) (split 15 (found 16) (split 6 (split 9 (found 15) small) small)))

def part147 : Certificate := (split 6 (split 9 (found 15) (split 5 (split 15 (found 7) small) small)) (split 5 (split 7 (split 8 (found 2) small) small) small))

def part148 : Certificate := (split 5 (split 8 (split 7 (found 2) (split 13 (found 25) small)) (split 15 (found 7) small)) (split 8 (split 13 (found 25) small) small))

def part149 : Certificate := (split 13 (found 25) (split 5 (split 7 (found 2) small) small))

def part150 : Certificate := (split 9 (split 10 (split 12 (found 3) small) small) small)

def part151 : Certificate := (split 2 (split 13 (found 16) (split 7 (split 8 (found 2) small) small)) (split 7 (split 8 (found 2) small) small))

def part152 : Certificate := (split 8 (found 2) (split 9 (split 10 (split 12 (found 3) small) small) small))

def part153 : Certificate := (split 9 (split 10 (split 12 (found 3) small) small) small)

def part154 : Certificate := (split 15 (found 16) (split 9 (split 10 (split 12 (found 3) small) small) small))

def part155 : Certificate := (split 9 (split 10 (split 12 (found 3) small) small) small)

def part156 : Certificate := (split 10 (split 12 (found 3) small) small)

def part157 : Certificate := (split 14 (split 2 (split 10 (found 10) (split 13 part146 part147)) (split 6 (split 9 (found 15) part148) (split 8 part149 part150))) (split 5 (split 15 (split 6 (found 7) part151) (split 7 part152 part153)) (split 2 (split 13 part154 part155) (split 9 part156 small))))

def certificate : Certificate := (split 4 (split 6 (split 0 (found 26) (split 1 part6 part19)) (split 2 (split 0 (found 0) part39) (split 3 part49 part63))) (split 1 (split 3 (split 6 (found 1) part79) (split 10 part86 part112)) (split 0 (split 12 part118 part135) (split 11 part145 part157))))

end G11Certificate
