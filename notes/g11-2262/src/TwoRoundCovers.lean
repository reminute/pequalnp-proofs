import TwoRoundData

namespace G11TwoRounds

open G11Protected G11Certificate

theorem cap_0 (K : Finset (Fin 11)) (s : covers (bound 0) K) : (bound 0).card < K.card := by
  change 4 < K.card
  have sum := total_weight K
  have h14 : 1 ≤ weight K 7 + weight K 9 := endpoint_charge s 14 (by decide)
  have h13 : 1 ≤ weight K 6 + weight K 10 := endpoint_charge s 13 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  omega

theorem cap_1 (K : Finset (Fin 11)) (s : covers (bound 1) K) : (bound 1).card < K.card := by
  change 4 < K.card
  have sum := total_weight K
  have h15 : 1 ≤ weight K 8 + weight K 9 := endpoint_charge s 15 (by decide)
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge s 7 (by decide)
  have h12 : 1 ≤ weight K 6 + weight K 7 := endpoint_charge s 12 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h1 : 1 ≤ weight K 0 + weight K 10 := endpoint_charge s 1 (by decide)
  omega

theorem cap_2 (K : Finset (Fin 11)) (s : covers (bound 2) K) : (bound 2).card < K.card := by
  change 4 < K.card
  have sum := total_weight K
  have h15 : 1 ≤ weight K 8 + weight K 9 := endpoint_charge s 15 (by decide)
  have h9 : 1 ≤ weight K 4 + weight K 10 := endpoint_charge s 9 (by decide)
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge s 7 (by decide)
  have h12 : 1 ≤ weight K 6 + weight K 7 := endpoint_charge s 12 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  omega

theorem cap_3 (K : Finset (Fin 11)) (s : covers (bound 3) K) : (bound 3).card < K.card := by
  change 4 < K.card
  have sum := total_weight K
  have h15 : 1 ≤ weight K 8 + weight K 9 := endpoint_charge s 15 (by decide)
  have h9 : 1 ≤ weight K 4 + weight K 10 := endpoint_charge s 9 (by decide)
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge s 7 (by decide)
  have h12 : 1 ≤ weight K 6 + weight K 7 := endpoint_charge s 12 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  omega

theorem cap_4 (K : Finset (Fin 11)) (s : covers (bound 4) K) : (bound 4).card < K.card := by
  change 5 < K.card
  have sum := total_weight K
  have h15 : 1 ≤ weight K 8 + weight K 9 := endpoint_charge s 15 (by decide)
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge s 7 (by decide)
  have h12 : 1 ≤ weight K 6 + weight K 7 := endpoint_charge s 12 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h1 : 1 ≤ weight K 0 + weight K 10 := endpoint_charge s 1 (by decide)
  omega

theorem cap_5 (K : Finset (Fin 11)) (s : covers (bound 5) K) : (bound 5).card < K.card := by
  change 5 < K.card
  have sum := total_weight K
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge s 7 (by decide)
  have h12 : 1 ≤ weight K 6 + weight K 7 := endpoint_charge s 12 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  have h0 : 1 ≤ weight K 0 + weight K 9 := endpoint_charge s 0 (by decide)
  omega

theorem cap_6 (K : Finset (Fin 11)) (s : covers (bound 6) K) : (bound 6).card < K.card := by
  change 4 < K.card
  have sum := total_weight K
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge s 7 (by decide)
  have h12 : 1 ≤ weight K 6 + weight K 7 := endpoint_charge s 12 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h0 : 1 ≤ weight K 0 + weight K 9 := endpoint_charge s 0 (by decide)
  have h1 : 1 ≤ weight K 0 + weight K 10 := endpoint_charge s 1 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h5 : 1 ≤ weight K 2 + weight K 10 := endpoint_charge s 5 (by decide)
  have h11 : 1 ≤ weight K 5 + weight K 9 := endpoint_charge s 11 (by decide)
  omega

theorem cap_7 (K : Finset (Fin 11)) (s : covers (bound 7) K) : (bound 7).card < K.card := by
  change 4 < K.card
  have sum := total_weight K
  have h15 : 1 ≤ weight K 8 + weight K 9 := endpoint_charge s 15 (by decide)
  have h9 : 1 ≤ weight K 4 + weight K 10 := endpoint_charge s 9 (by decide)
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge s 7 (by decide)
  have h12 : 1 ≤ weight K 6 + weight K 7 := endpoint_charge s 12 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  omega

theorem cap_8 (K : Finset (Fin 11)) (s : covers (bound 8) K) : (bound 8).card < K.card := by
  change 4 < K.card
  have sum := total_weight K
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge s 7 (by decide)
  have h12 : 1 ≤ weight K 6 + weight K 7 := endpoint_charge s 12 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h5 : 1 ≤ weight K 2 + weight K 10 := endpoint_charge s 5 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  have h9 : 1 ≤ weight K 4 + weight K 10 := endpoint_charge s 9 (by decide)
  have h10 : 1 ≤ weight K 5 + weight K 8 := endpoint_charge s 10 (by decide)
  have h0 : 1 ≤ weight K 0 + weight K 9 := endpoint_charge s 0 (by decide)
  omega

theorem cap_9 (K : Finset (Fin 11)) (s : covers (bound 9) K) : (bound 9).card < K.card := by
  change 4 < K.card
  have sum := total_weight K
  have h10 : 1 ≤ weight K 5 + weight K 8 := endpoint_charge s 10 (by decide)
  have h9 : 1 ≤ weight K 4 + weight K 10 := endpoint_charge s 9 (by decide)
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge s 7 (by decide)
  have h12 : 1 ≤ weight K 6 + weight K 7 := endpoint_charge s 12 (by decide)
  have h0 : 1 ≤ weight K 0 + weight K 9 := endpoint_charge s 0 (by decide)
  omega

theorem cap_10 (K : Finset (Fin 11)) (s : covers (bound 10) K) : (bound 10).card < K.card := by
  change 4 < K.card
  have sum := total_weight K
  have h15 : 1 ≤ weight K 8 + weight K 9 := endpoint_charge s 15 (by decide)
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge s 7 (by decide)
  have h12 : 1 ≤ weight K 6 + weight K 7 := endpoint_charge s 12 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h1 : 1 ≤ weight K 0 + weight K 10 := endpoint_charge s 1 (by decide)
  omega

theorem cap_11 (K : Finset (Fin 11)) (s : covers (bound 11) K) : (bound 11).card < K.card := by
  change 4 < K.card
  have sum := total_weight K
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge s 7 (by decide)
  have h12 : 1 ≤ weight K 6 + weight K 7 := endpoint_charge s 12 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h0 : 1 ≤ weight K 0 + weight K 9 := endpoint_charge s 0 (by decide)
  have h1 : 1 ≤ weight K 0 + weight K 10 := endpoint_charge s 1 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h5 : 1 ≤ weight K 2 + weight K 10 := endpoint_charge s 5 (by decide)
  have h11 : 1 ≤ weight K 5 + weight K 9 := endpoint_charge s 11 (by decide)
  omega

theorem cap_12 (K : Finset (Fin 11)) (s : covers (bound 12) K) : (bound 12).card < K.card := by
  change 4 < K.card
  have sum := total_weight K
  have h14 : 1 ≤ weight K 7 + weight K 9 := endpoint_charge s 14 (by decide)
  have h13 : 1 ≤ weight K 6 + weight K 10 := endpoint_charge s 13 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  omega

theorem cap_13 (K : Finset (Fin 11)) (s : covers (bound 13) K) : (bound 13).card < K.card := by
  change 5 < K.card
  have sum := total_weight K
  have h14 : 1 ≤ weight K 7 + weight K 9 := endpoint_charge s 14 (by decide)
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  have h1 : 1 ≤ weight K 0 + weight K 10 := endpoint_charge s 1 (by decide)
  omega

theorem cap_14 (K : Finset (Fin 11)) (s : covers (bound 14) K) : (bound 14).card < K.card := by
  change 4 < K.card
  have sum := total_weight K
  have h13 : 1 ≤ weight K 6 + weight K 10 := endpoint_charge s 13 (by decide)
  have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge s 7 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  have h0 : 1 ≤ weight K 0 + weight K 9 := endpoint_charge s 0 (by decide)
  omega

theorem cap_15 (K : Finset (Fin 11)) (s : covers (bound 15) K) : (bound 15).card < K.card := by
  change 4 < K.card
  have sum := total_weight K
  have h14 : 1 ≤ weight K 7 + weight K 9 := endpoint_charge s 14 (by decide)
  have h10 : 1 ≤ weight K 5 + weight K 8 := endpoint_charge s 10 (by decide)
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h1 : 1 ≤ weight K 0 + weight K 10 := endpoint_charge s 1 (by decide)
  omega

theorem cap_16 (K : Finset (Fin 11)) (s : covers (bound 16) K) : (bound 16).card < K.card := by
  change 4 < K.card
  have sum := total_weight K
  have h12 : 1 ≤ weight K 6 + weight K 7 := endpoint_charge s 12 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  have h0 : 1 ≤ weight K 0 + weight K 9 := endpoint_charge s 0 (by decide)
  have h1 : 1 ≤ weight K 0 + weight K 10 := endpoint_charge s 1 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h5 : 1 ≤ weight K 2 + weight K 10 := endpoint_charge s 5 (by decide)
  have h11 : 1 ≤ weight K 5 + weight K 9 := endpoint_charge s 11 (by decide)
  omega

theorem cap_17 (K : Finset (Fin 11)) (s : covers (bound 17) K) : (bound 17).card < K.card := by
  change 5 < K.card
  have sum := total_weight K
  have h14 : 1 ≤ weight K 7 + weight K 9 := endpoint_charge s 14 (by decide)
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  have h1 : 1 ≤ weight K 0 + weight K 10 := endpoint_charge s 1 (by decide)
  omega

theorem cap_18 (K : Finset (Fin 11)) (s : covers (bound 18) K) : (bound 18).card < K.card := by
  change 5 < K.card
  have sum := total_weight K
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge s 7 (by decide)
  have h12 : 1 ≤ weight K 6 + weight K 7 := endpoint_charge s 12 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h0 : 1 ≤ weight K 0 + weight K 9 := endpoint_charge s 0 (by decide)
  have h1 : 1 ≤ weight K 0 + weight K 10 := endpoint_charge s 1 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h5 : 1 ≤ weight K 2 + weight K 10 := endpoint_charge s 5 (by decide)
  have h11 : 1 ≤ weight K 5 + weight K 9 := endpoint_charge s 11 (by decide)
  omega

theorem cap_19 (K : Finset (Fin 11)) (s : covers (bound 19) K) : (bound 19).card < K.card := by
  change 5 < K.card
  have sum := total_weight K
  have h14 : 1 ≤ weight K 7 + weight K 9 := endpoint_charge s 14 (by decide)
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  have h1 : 1 ≤ weight K 0 + weight K 10 := endpoint_charge s 1 (by decide)
  omega

theorem cap_20 (K : Finset (Fin 11)) (s : covers (bound 20) K) : (bound 20).card < K.card := by
  change 4 < K.card
  have sum := total_weight K
  have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge s 7 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  have h0 : 1 ≤ weight K 0 + weight K 9 := endpoint_charge s 0 (by decide)
  have h1 : 1 ≤ weight K 0 + weight K 10 := endpoint_charge s 1 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h5 : 1 ≤ weight K 2 + weight K 10 := endpoint_charge s 5 (by decide)
  have h11 : 1 ≤ weight K 5 + weight K 9 := endpoint_charge s 11 (by decide)
  omega

theorem cap_21 (K : Finset (Fin 11)) (s : covers (bound 21) K) : (bound 21).card < K.card := by
  change 5 < K.card
  have sum := total_weight K
  have h14 : 1 ≤ weight K 7 + weight K 9 := endpoint_charge s 14 (by decide)
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  have h1 : 1 ≤ weight K 0 + weight K 10 := endpoint_charge s 1 (by decide)
  omega

theorem cap_22 (K : Finset (Fin 11)) (s : covers (bound 22) K) : (bound 22).card < K.card := by
  change 4 < K.card
  have sum := total_weight K
  have h11 : 1 ≤ weight K 5 + weight K 9 := endpoint_charge s 11 (by decide)
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge s 7 (by decide)
  have h12 : 1 ≤ weight K 6 + weight K 7 := endpoint_charge s 12 (by decide)
  have h5 : 1 ≤ weight K 2 + weight K 10 := endpoint_charge s 5 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  omega

theorem cap_23 (K : Finset (Fin 11)) (s : covers (bound 23) K) : (bound 23).card < K.card := by
  change 4 < K.card
  have sum := total_weight K
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge s 7 (by decide)
  have h12 : 1 ≤ weight K 6 + weight K 7 := endpoint_charge s 12 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  have h1 : 1 ≤ weight K 0 + weight K 10 := endpoint_charge s 1 (by decide)
  omega

theorem cap_24 (K : Finset (Fin 11)) (s : covers (bound 24) K) : (bound 24).card < K.card := by
  change 5 < K.card
  have sum := total_weight K
  have h13 : 1 ≤ weight K 6 + weight K 10 := endpoint_charge s 13 (by decide)
  have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge s 7 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  have h0 : 1 ≤ weight K 0 + weight K 9 := endpoint_charge s 0 (by decide)
  omega

theorem cap_25 (K : Finset (Fin 11)) (s : covers (bound 25) K) : (bound 25).card < K.card := by
  change 5 < K.card
  have sum := total_weight K
  have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge s 6 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  have h0 : 1 ≤ weight K 0 + weight K 9 := endpoint_charge s 0 (by decide)
  have h1 : 1 ≤ weight K 0 + weight K 10 := endpoint_charge s 1 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h5 : 1 ≤ weight K 2 + weight K 10 := endpoint_charge s 5 (by decide)
  have h11 : 1 ≤ weight K 5 + weight K 9 := endpoint_charge s 11 (by decide)
  omega

theorem cap_26 (K : Finset (Fin 11)) (s : covers (bound 26) K) : (bound 26).card < K.card := by
  change 5 < K.card
  have sum := total_weight K
  have h13 : 1 ≤ weight K 6 + weight K 10 := endpoint_charge s 13 (by decide)
  have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge s 7 (by decide)
  have h4 : 1 ≤ weight K 2 + weight K 5 := endpoint_charge s 4 (by decide)
  have h2 : 1 ≤ weight K 1 + weight K 4 := endpoint_charge s 2 (by decide)
  have h3 : 1 ≤ weight K 1 + weight K 8 := endpoint_charge s 3 (by decide)
  have h8 : 1 ≤ weight K 4 + weight K 8 := endpoint_charge s 8 (by decide)
  have h0 : 1 ≤ weight K 0 + weight K 9 := endpoint_charge s 0 (by decide)
  omega

theorem cap_bound (k : Fin 27) (K : Finset (Fin 11)) (s : covers (bound k) K) :
    (bound k).card < K.card := by
  fin_cases k
  · exact cap_0 K s
  · exact cap_1 K s
  · exact cap_2 K s
  · exact cap_3 K s
  · exact cap_4 K s
  · exact cap_5 K s
  · exact cap_6 K s
  · exact cap_7 K s
  · exact cap_8 K s
  · exact cap_9 K s
  · exact cap_10 K s
  · exact cap_11 K s
  · exact cap_12 K s
  · exact cap_13 K s
  · exact cap_14 K s
  · exact cap_15 K s
  · exact cap_16 K s
  · exact cap_17 K s
  · exact cap_18 K s
  · exact cap_19 K s
  · exact cap_20 K s
  · exact cap_21 K s
  · exact cap_22 K s
  · exact cap_23 K s
  · exact cap_24 K s
  · exact cap_25 K s
  · exact cap_26 K s

end G11TwoRounds
