import ProtectedObstruction

namespace G11TwoRounds

structure Hint where
  edges : Finset (Fin 16)
  z : Fin 24
  rows : Finset (Fin 24)

def hints : List Hint := [
  ⟨{1, 2}, 1, {1, 23}⟩,
  ⟨{0, 1, 2}, 0, {0, 23}⟩,
  ⟨{0, 3}, 12, {12, 23}⟩,
  ⟨{0, 4}, 2, {2, 18}⟩,
  ⟨{1, 4}, 0, {0, 20}⟩,
  ⟨{3, 4}, 2, {2, 14}⟩,
  ⟨{2, 3, 4}, 1, {1, 20}⟩,
  ⟨{0, 5}, 0, {0, 23}⟩,
  ⟨{2, 5}, 1, {1, 23}⟩,
  ⟨{1, 6}, 4, {4, 23}⟩,
  ⟨{0, 1, 6}, 0, {0, 23}⟩,
  ⟨{2, 6}, 1, {1, 17}⟩,
  ⟨{0, 2, 6}, 0, {0, 18}⟩,
  ⟨{3, 6}, 13, {13, 23}⟩,
  ⟨{4, 6}, 0, {0, 7}⟩,
  ⟨{5, 6}, 4, {4, 23}⟩,
  ⟨{0, 7}, 8, {8, 23}⟩,
  ⟨{2, 7}, 9, {9, 23}⟩,
  ⟨{3, 7}, 8, {8, 21}⟩,
  ⟨{1, 3, 7}, 0, {0, 22}⟩,
  ⟨{4, 7}, 2, {2, 14}⟩,
  ⟨{0, 8}, 12, {12, 18}⟩,
  ⟨{1, 8}, 1, {1, 22}⟩,
  ⟨{2, 3, 8}, 0, {0, 18, 22}⟩,
  ⟨{4, 8}, 3, {3, 14}⟩,
  ⟨{2, 4, 8}, 0, {0, 11}⟩,
  ⟨{5, 8}, 1, {1, 22}⟩,
  ⟨{6, 8}, 1, {1, 13}⟩,
  ⟨{7, 8}, 9, {9, 21}⟩,
  ⟨{0, 9}, 1, {1, 23}⟩,
  ⟨{3, 9}, 0, {0, 18, 22}⟩,
  ⟨{1, 3, 9}, 0, {0, 22}⟩,
  ⟨{2, 3, 9}, 1, {1, 23}⟩,
  ⟨{4, 9}, 1, {1, 20}⟩,
  ⟨{2, 4, 9}, 1, {1, 20}⟩,
  ⟨{6, 9}, 5, {5, 23}⟩,
  ⟨{0, 10}, 2, {2, 22, 23}⟩,
  ⟨{2, 10}, 1, {1, 20, 22}⟩,
  ⟨{5, 10}, 12, {12, 20}⟩,
  ⟨{1, 3, 5, 10}, 12, {12, 20}⟩,
  ⟨{6, 10}, 2, {2, 18, 22}⟩,
  ⟨{1, 7, 10}, 2, {2, 22}⟩,
  ⟨{1, 11}, 2, {2, 23}⟩,
  ⟨{0, 1, 11}, 0, {0, 23}⟩,
  ⟨{3, 11}, 2, {2, 22, 23}⟩,
  ⟨{5, 11}, 15, {15, 20}⟩,
  ⟨{7, 11}, 10, {10, 23}⟩,
  ⟨{6, 7, 11}, 6, {6, 23}⟩,
  ⟨{8, 11}, 2, {2, 18, 22}⟩,
  ⟨{2, 8, 11}, 2, {2, 18}⟩,
  ⟨{0, 12}, 8, {8, 18}⟩,
  ⟨{1, 12}, 4, {4, 22}⟩,
  ⟨{2, 12}, 4, {4, 11}⟩,
  ⟨{3, 12}, 8, {8, 13}⟩,
  ⟨{4, 12}, 6, {6, 14}⟩,
  ⟨{5, 12}, 4, {4, 22}⟩,
  ⟨{6, 7, 12}, 0, {0, 18, 22}⟩,
  ⟨{8, 12}, 9, {9, 13}⟩,
  ⟨{9, 12}, 5, {5, 22}⟩,
  ⟨{0, 13}, 4, {4, 23}⟩,
  ⟨{2, 13}, 5, {5, 23}⟩,
  ⟨{4, 13}, 4, {4, 20}⟩,
  ⟨{7, 13}, 0, {0, 18, 22}⟩,
  ⟨{1, 7, 13}, 0, {0, 22}⟩,
  ⟨{8, 13}, 5, {5, 22}⟩,
  ⟨{6, 11, 13}, 4, {4, 23}⟩,
  ⟨{1, 14}, 8, {8, 23}⟩,
  ⟨{3, 14}, 14, {14, 23}⟩,
  ⟨{4, 14}, 10, {10, 18}⟩,
  ⟨{6, 14}, 0, {0, 18, 22}⟩,
  ⟨{0, 6, 14}, 0, {0, 18}⟩,
  ⟨{5, 7, 14}, 8, {8, 23}⟩,
  ⟨{8, 14}, 14, {14, 18}⟩,
  ⟨{10, 14}, 2, {2, 22, 23}⟩,
  ⟨{7, 11, 14}, 8, {8, 23}⟩,
  ⟨{5, 12, 14}, 4, {4, 22}⟩,
  ⟨{13, 14}, 17, {17, 22}⟩,
  ⟨{1, 15}, 12, {12, 23}⟩,
  ⟨{2, 15}, 0, {0, 18, 22}⟩,
  ⟨{0, 2, 15}, 0, {0, 18}⟩,
  ⟨{4, 15}, 2, {2, 18, 22}⟩,
  ⟨{3, 5, 8, 15}, 0, {0, 22}⟩,
  ⟨{3, 5, 10, 15}, 12, {12, 23}⟩]

def hint (i : Fin 83) : Hint := hints.getD i.val ⟨∅,0,∅⟩

def caps : List (Finset (Fin 16)) := [{1, 5, 7, 9}, {4, 5, 10, 11}, {1, 3, 5, 13}, {1, 3, 10, 13}, {3, 5, 8, 10, 13}, {1, 5, 9, 10, 13}, {2, 8, 9, 14}, {0, 2, 11, 14}, {2, 3, 11, 14}, {2, 4, 11, 14}, {2, 9, 11, 14}, {8, 9, 10, 15}, {0, 6, 11, 15}, {7, 9, 10, 12, 15}, {6, 11, 12, 15}, {3, 5, 13, 15}, {6, 7, 13, 15}, {5, 7, 9, 13, 15}, {3, 8, 10, 13, 15}, {9, 10, 11, 13, 15}, {6, 12, 13, 15}, {10, 11, 12, 13, 15}, {0, 1, 14, 15}, {0, 11, 14, 15}, {5, 9, 11, 14, 15}, {7, 9, 12, 14, 15}, {9, 11, 12, 14, 15}]
def bound (i : Fin 27) : Finset (Fin 16) := caps.getD i.val ∅

inductive Tree where
  | cap (i : Fin 27)
  | forced (i : Fin 83)
  | step (e : Fin 16) (yes no : Tree)

open Tree

def certificate : Tree := (step 0 (step 7 (forced 16) (step 10 (forced 36) (step 5 (forced 7) (step 12 (forced 50) (step 9 (forced 29) (step 3 (forced 2) (step 4 (forced 3) (step 13 (forced 59) (step 8 (forced 21) (step 2 (step 6 (forced 12) (step 1 (forced 1) (step 15 (forced 79) (cap 7)))) (step 1 (step 6 (forced 10) (step 11 (forced 43) (cap 22))) (step 6 (step 14 (forced 70) (cap 12)) (cap 23))))))))))))) (step 2 (step 5 (forced 8) (step 7 (forced 17) (step 10 (forced 37) (step 1 (forced 0) (step 13 (forced 60) (step 15 (forced 78) (step 6 (forced 11) (step 12 (forced 52) (step 3 (step 4 (forced 6) (step 8 (forced 23) (step 9 (forced 32) (cap 8)))) (step 8 (step 11 (forced 49) (step 4 (forced 25) (cap 6))) (step 9 (step 4 (forced 34) (cap 10)) (cap 9)))))))))))) (step 4 (step 13 (forced 61) (step 7 (forced 20) (step 15 (forced 80) (step 1 (forced 4) (step 6 (forced 14) (step 12 (forced 54) (step 3 (forced 5) (step 9 (forced 33) (step 14 (forced 68) (step 8 (forced 24) (cap 1))))))))))) (step 6 (step 1 (forced 9) (step 14 (forced 69) (step 3 (forced 13) (step 8 (forced 27) (step 5 (forced 15) (step 9 (forced 35) (step 10 (forced 40) (step 7 (step 11 (forced 47) (step 12 (forced 56) (cap 16))) (step 13 (step 11 (forced 65) (cap 20)) (cap 14)))))))))) (step 1 (step 8 (forced 22) (step 12 (forced 51) (step 11 (forced 42) (step 14 (forced 66) (step 15 (forced 77) (step 3 (step 7 (forced 19) (step 9 (forced 31) (step 5 (step 10 (forced 39) (cap 2)) (cap 3)))) (step 7 (step 13 (forced 63) (step 10 (forced 41) (cap 0))) (cap 5)))))))) (step 14 (step 10 (forced 73) (step 3 (forced 67) (step 8 (forced 72) (step 13 (forced 76) (step 7 (step 11 (forced 74) (step 5 (forced 71) (cap 25))) (step 12 (step 5 (forced 75) (cap 26)) (cap 24))))))) (step 3 (step 9 (forced 30) (step 11 (forced 44) (step 7 (forced 18) (step 12 (forced 53) (step 15 (step 5 (step 8 (forced 81) (step 10 (forced 82) (cap 15))) (cap 18)) (cap 4)))))) (step 8 (step 11 (forced 48) (step 13 (forced 64) (step 5 (forced 26) (step 7 (forced 28) (step 12 (forced 57) (cap 11)))))) (step 5 (step 12 (forced 55) (step 11 (forced 45) (step 10 (forced 38) (cap 17)))) (step 7 (step 11 (forced 46) (step 13 (forced 62) (cap 13))) (step 9 (step 12 (forced 58) (cap 19)) (cap 21))))))))))))

end G11TwoRounds
