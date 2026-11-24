import G11NineEdges

namespace G11Protected

def upperRows : List (Finset (Fin 16)) := [{3, 11, 13}, {8, 11, 13}, {0, 12, 13}, {11, 12, 13}, {9, 10, 13, 14}, {1, 10, 15}, {2, 11, 15}, {9, 11, 15}, {5, 12, 15}, {7, 13, 15}, {10, 13, 15}, {12, 13, 15}, {4, 14, 15}, {6, 14, 15}]
def upperSet (k : Fin 14) : Finset (Fin 16) := upperRows.getD k.val ∅

inductive Tree where
  | cover (k : Fin 14)
  | row (z : Fin 24)
  | step (e : Fin 16) (yes no : Tree)

open Tree

def certificate : Tree := (step 0 (step 1 (row 0) (step 11 (row 15) (step 2 (row 16) (step 6 (row 17) (step 14 (row 15) (step 4 (row 2) (step 15 (row 15) (step 3 (row 12) (step 8 (row 12) (step 5 (row 0) (step 7 (row 0) (step 9 (row 1) (step 10 (row 0) (cover 2)))))))))))))) (step 2 (step 3 (row 0) (step 9 (row 1) (step 4 (row 3) (step 6 (row 1) (step 8 (row 1) (step 1 (row 0) (step 5 (row 0) (step 7 (row 0) (step 12 (row 1) (step 10 (row 0) (step 13 (row 0) (step 14 (row 15) (cover 6))))))))))))) (step 4 (step 5 (row 0) (step 10 (row 2) (step 6 (row 0) (step 11 (row 2) (step 1 (row 0) (step 3 (row 2) (step 7 (row 2) (step 12 (row 6) (step 8 (row 3) (step 9 (row 1) (step 13 (row 0) (cover 12)))))))))))) (step 6 (step 7 (row 0) (step 13 (row 4) (step 12 (row 4) (step 1 (row 0) (step 3 (row 0) (step 8 (row 1) (step 5 (row 0) (step 9 (row 0) (step 10 (row 0) (step 11 (row 15) (cover 13))))))))))) (step 1 (step 5 (row 19) (step 9 (row 19) (step 3 (row 21) (step 13 (row 19) (step 7 (row 20) (step 8 (row 0) (step 11 (row 2) (step 12 (row 0) (step 14 (row 8) (cover 5)))))))))) (step 14 (step 15 (row 15) (step 7 (row 8) (step 12 (row 8) (step 11 (row 15) (step 3 (row 12) (step 5 (row 23) (step 8 (row 12) (cover 4)))))))) (step 3 (step 8 (row 12) (step 10 (row 12) (step 15 (row 12) (step 5 (row 21) (step 7 (row 8) (step 12 (row 8) (step 9 (row 0) (cover 0)))))))) (step 8 (step 9 (row 1) (step 10 (row 12) (step 15 (row 12) (step 5 (row 0) (step 7 (row 8) (step 12 (row 9) (cover 1))))))) (step 5 (step 9 (row 19) (step 13 (row 19) (step 7 (row 19) (step 10 (row 12) (step 11 (row 15) (cover 8)))))) (step 7 (step 12 (row 8) (step 9 (row 19) (step 10 (row 8) (step 11 (row 0) (cover 9))))) (step 9 (step 13 (row 19) (step 10 (row 3) (step 12 (row 0) (cover 7)))) (step 10 (step 11 (row 2) (step 12 (row 8) (cover 10))) (step 11 (step 15 (row 15) (cover 3)) (cover 11))))))))))))))

end G11Protected
