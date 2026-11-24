import ProtectedData

namespace G11Protected

open G11Certificate

def covers (U : Finset (Fin 16)) (K : Finset (Fin 11)) : Prop :=
  ∀ e : Fin 16, e ∈ U ∨ (edgeAt e).1 ∈ K ∨ (edgeAt e).2 ∈ K

def weight (K : Finset (Fin 11)) (i : Fin 11) : ℕ := if i ∈ K then 1 else 0

theorem endpoint_charge {U : Finset (Fin 16)} {K : Finset (Fin 11)} (s : covers U K)
    (e : Fin 16) (notDeleted : e ∉ U) : 1 ≤ weight K (edgeAt e).1 + weight K (edgeAt e).2 := by
  rcases (s e).resolve_left notDeleted with h | h <;> simp [weight,h]

theorem total_weight (K : Finset (Fin 11)) :
    weight K 0 + (weight K 1 + (weight K 2 + (weight K 3 + (weight K 4 + (weight K 5 + (weight K 6 + (weight K 7 + (weight K 8 + (weight K 9 + (weight K 10)))))))))) = K.card := by
  have eq : ∑ i, weight K i = K.card := by simp [weight]
  simpa [Fin.sum_univ_succ] using eq

theorem bound_0 (K : Finset (Fin 11)) (s : covers (upperSet 0) K) :
    (upperSet 0).card + 2 < K.card := by
  change 5 < K.card
  have sum := total_weight K
  have h15 : 1 ≤ weight K 8 + weight K 9 := endpoint_charge s 15 (by decide)
  have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge s 7 (by decide)
  have h12 : 1 ≤ weight K 6 + weight K 7 := endpoint_charge s 12 (by decide)
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h1 : 1 ≤ weight K 0 + weight K 10 := endpoint_charge s 1 (by decide)
  omega

theorem bound_1 (K : Finset (Fin 11)) (s : covers (upperSet 1) K) :
    (upperSet 1).card + 2 < K.card := by
  change 5 < K.card
  have sum := total_weight K
  have h15 : 1 ≤ weight K 8 + weight K 9 := endpoint_charge s 15 (by decide)
  have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge s 7 (by decide)
  have h12 : 1 ≤ weight K 6 + weight K 7 := endpoint_charge s 12 (by decide)
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h1 : 1 ≤ weight K 0 + weight K 10 := endpoint_charge s 1 (by decide)
  omega

theorem bound_2 (K : Finset (Fin 11)) (s : covers (upperSet 2) K) :
    (upperSet 2).card + 2 < K.card := by
  change 5 < K.card
  have sum := total_weight K
  have h14 : 1 ≤ weight K 7 + weight K 9 := endpoint_charge s 14 (by decide)
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h1 : 1 ≤ weight K 0 + weight K 10 := endpoint_charge s 1 (by decide)
  omega

theorem bound_3 (K : Finset (Fin 11)) (s : covers (upperSet 3) K) :
    (upperSet 3).card + 2 < K.card := by
  change 5 < K.card
  have sum := total_weight K
  have h14 : 1 ≤ weight K 7 + weight K 9 := endpoint_charge s 14 (by decide)
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h1 : 1 ≤ weight K 0 + weight K 10 := endpoint_charge s 1 (by decide)
  omega

theorem bound_4 (K : Finset (Fin 11)) (s : covers (upperSet 4) K) :
    (upperSet 4).card + 2 < K.card := by
  change 6 < K.card
  have sum := total_weight K
  have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge s 7 (by decide)
  have h12 : 1 ≤ weight K 6 + weight K 7 := endpoint_charge s 12 (by decide)
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h1 : 1 ≤ weight K 0 + weight K 10 := endpoint_charge s 1 (by decide)
  have h5 : 1 ≤ weight K 2 + weight K 10 := endpoint_charge s 5 (by decide)
  have h0 : 1 ≤ weight K 0 + weight K 9 := endpoint_charge s 0 (by decide)
  have h11 : 1 ≤ weight K 5 + weight K 9 := endpoint_charge s 11 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  omega

theorem bound_5 (K : Finset (Fin 11)) (s : covers (upperSet 5) K) :
    (upperSet 5).card + 2 < K.card := by
  change 5 < K.card
  have sum := total_weight K
  have h13 : 1 ≤ weight K 6 + weight K 10 := endpoint_charge s 13 (by decide)
  have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge s 7 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h0 : 1 ≤ weight K 0 + weight K 9 := endpoint_charge s 0 (by decide)
  omega

theorem bound_6 (K : Finset (Fin 11)) (s : covers (upperSet 6) K) :
    (upperSet 6).card + 2 < K.card := by
  change 5 < K.card
  have sum := total_weight K
  have h9 : 1 ≤ weight K 4 + weight K 10 := endpoint_charge s 9 (by decide)
  have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge s 7 (by decide)
  have h12 : 1 ≤ weight K 6 + weight K 7 := endpoint_charge s 12 (by decide)
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h0 : 1 ≤ weight K 0 + weight K 9 := endpoint_charge s 0 (by decide)
  omega

theorem bound_7 (K : Finset (Fin 11)) (s : covers (upperSet 7) K) :
    (upperSet 7).card + 2 < K.card := by
  change 5 < K.card
  have sum := total_weight K
  have h14 : 1 ≤ weight K 7 + weight K 9 := endpoint_charge s 14 (by decide)
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h1 : 1 ≤ weight K 0 + weight K 10 := endpoint_charge s 1 (by decide)
  omega

theorem bound_8 (K : Finset (Fin 11)) (s : covers (upperSet 8) K) :
    (upperSet 8).card + 2 < K.card := by
  change 5 < K.card
  have sum := total_weight K
  have h14 : 1 ≤ weight K 7 + weight K 9 := endpoint_charge s 14 (by decide)
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h1 : 1 ≤ weight K 0 + weight K 10 := endpoint_charge s 1 (by decide)
  omega

theorem bound_9 (K : Finset (Fin 11)) (s : covers (upperSet 9) K) :
    (upperSet 9).card + 2 < K.card := by
  change 5 < K.card
  have sum := total_weight K
  have h14 : 1 ≤ weight K 7 + weight K 9 := endpoint_charge s 14 (by decide)
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h1 : 1 ≤ weight K 0 + weight K 10 := endpoint_charge s 1 (by decide)
  omega

theorem bound_10 (K : Finset (Fin 11)) (s : covers (upperSet 10) K) :
    (upperSet 10).card + 2 < K.card := by
  change 5 < K.card
  have sum := total_weight K
  have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge s 7 (by decide)
  have h12 : 1 ≤ weight K 6 + weight K 7 := endpoint_charge s 12 (by decide)
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h1 : 1 ≤ weight K 0 + weight K 10 := endpoint_charge s 1 (by decide)
  have h5 : 1 ≤ weight K 2 + weight K 10 := endpoint_charge s 5 (by decide)
  have h0 : 1 ≤ weight K 0 + weight K 9 := endpoint_charge s 0 (by decide)
  have h11 : 1 ≤ weight K 5 + weight K 9 := endpoint_charge s 11 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  omega

theorem bound_11 (K : Finset (Fin 11)) (s : covers (upperSet 11) K) :
    (upperSet 11).card + 2 < K.card := by
  change 5 < K.card
  have sum := total_weight K
  have h14 : 1 ≤ weight K 7 + weight K 9 := endpoint_charge s 14 (by decide)
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h1 : 1 ≤ weight K 0 + weight K 10 := endpoint_charge s 1 (by decide)
  omega

theorem bound_12 (K : Finset (Fin 11)) (s : covers (upperSet 12) K) :
    (upperSet 12).card + 2 < K.card := by
  change 5 < K.card
  have sum := total_weight K
  have h11 : 1 ≤ weight K 5 + weight K 9 := endpoint_charge s 11 (by decide)
  have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge s 7 (by decide)
  have h12 : 1 ≤ weight K 6 + weight K 7 := endpoint_charge s 12 (by decide)
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h5 : 1 ≤ weight K 2 + weight K 10 := endpoint_charge s 5 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  omega

theorem bound_13 (K : Finset (Fin 11)) (s : covers (upperSet 13) K) :
    (upperSet 13).card + 2 < K.card := by
  change 5 < K.card
  have sum := total_weight K
  have h13 : 1 ≤ weight K 6 + weight K 10 := endpoint_charge s 13 (by decide)
  have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge s 7 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h0 : 1 ≤ weight K 0 + weight K 9 := endpoint_charge s 0 (by decide)
  omega

theorem upper_bound (k : Fin 14) (K : Finset (Fin 11)) (s : covers (upperSet k) K) :
    (upperSet k).card + 2 < K.card := by
  fin_cases k
  · exact bound_0 K s
  · exact bound_1 K s
  · exact bound_2 K s
  · exact bound_3 K s
  · exact bound_4 K s
  · exact bound_5 K s
  · exact bound_6 K s
  · exact bound_7 K s
  · exact bound_8 K s
  · exact bound_9 K s
  · exact bound_10 K s
  · exact bound_11 K s
  · exact bound_12 K s
  · exact bound_13 K s

end G11Protected
