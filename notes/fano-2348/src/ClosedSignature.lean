import Multiplicity

namespace FanoSignature

open FanoDeskNormal

private theorem compact_square (x : Sig) :
    conj x x = fun i => x i && (decide (i.val < 60) || x (i-2)) := by
  funext i
  by_cases a : i = 60
  · subst i
    change (x 58 && x 60 || x 60 && x 58) = (x 60 && (false || x 58))
    simp [Bool.and_comm]
  by_cases b : i = 61
  · subst i
    change (x 59 && x 61 || x 61 && x 59) = (x 61 && (false || x 59))
    simp [Bool.and_comm]
  have low : i.val < 60 := by
    have p : i.val ≠ 60 := fun h => a (Fin.ext h)
    have q : i.val ≠ 61 := fun h => b (Fin.ext h)
    omega
  simp [conj, a, b, low]

theorem closed : have x1 : List (Fin (62 : ℕ) → Bool) := List.map (fun (x1 : ℕ) (x2 : Fin (62 : ℕ)) => x1.testBit ↑x2) [(2594090156585648135 : ℕ), (15270196031782968 : ℕ), (58150373818816 : ℕ), (94946423956573696 : ℕ), (54820275478360064 : ℕ), (3870282840506368 : ℕ), (133412159488 : ℕ), (1911954591369396745 : ℕ), (218716039641305168 : ℕ), (189725234880873600 : ℕ), (156548607028504576 : ℕ), (229736628137050114 : ℕ), (270286071509155872 : ℕ), (288160007408582916 : ℕ)]; have x2 : List (Fin (62 : ℕ) → Bool) → Prop := fun (x2 : List (Fin (62 : ℕ) → Bool)) =>   (fun (x3 : Fin (62 : ℕ)) => Decidable.decide (↑x3 < (21 : ℕ))) ∈ x2 ∧     ∀ x3 < x2.length,       ∃ (x5 : ℕ) (x6 : ℕ),         x5 ≠ x6 ∧           x5 < (14 : ℕ) + x3 ∧             x6 < (14 : ℕ) + x3 ∧               have x7 : Fin (62 : ℕ) → Bool := (x1 ++ x2).getD x5 fun (x7 : Fin (62 : ℕ)) => Bool.false;               have x8 : Fin (62 : ℕ) → Bool := (x1 ++ x2).getD x6 fun (x8 : Fin (62 : ℕ)) => Bool.false;               ((x2.getD x3 fun (x9 : Fin (62 : ℕ)) => Bool.false) = fun (x9 : Fin (62 : ℕ)) => x7 x9 || x8 x9) ∨ (0 : ℕ) < x3 ∧ (x2.getD x3 fun (x9 : Fin (62 : ℕ)) => Bool.false) = fun (x9 : Fin (62 : ℕ)) => if x9 = (60 : Fin (62 : ℕ)) then x7 (58 : Fin (62 : ℕ)) && x8 (60 : Fin (62 : ℕ)) || x7 (60 : Fin (62 : ℕ)) && x8 (58 : Fin (62 : ℕ)) else if x9 = (61 : Fin (62 : ℕ)) then x7 (59 : Fin (62 : ℕ)) && x8 (61 : Fin (62 : ℕ)) || x7 (61 : Fin (62 : ℕ)) && x8 (59 : Fin (62 : ℕ)) else x7 x9 && x8 x9; ∀ (x3 : List (Fin (62 : ℕ) → Bool)),   x2 x3 →     ∃ (x5 : List (Fin (62 : ℕ) → Bool)),       x5.length ≤ x3.length ∧         x2 x5 ∧           ∀ (x6 : Fin (62 : ℕ) → Bool),             have x7 : ℕ := List.count x6 (x1 ++ x5);             x7 ≤ (2 : ℕ) ∧ ((1 : ℕ) < x7 → ∃ x9 ∈ x5, x9 ≠ x6 ∧ x9 = fun (x10 : Fin (62 : ℕ)) => x6 x10 && (Decidable.decide (↑x10 < (60 : ℕ)) || x6 (x10 - (2 : Fin (62 : ℕ))))) := by
  intro raw good s yes
  change posted s at yes
  cases s with
  | nil => exact (List.not_mem_nil yes.1).elim
  | cons first tail =>
    obtain ⟨t,le,ok,mult⟩ := normalize_multiplicity first tail yes
    refine ⟨first::t, by simpa using le, ok, ?_⟩
    intro x
    obtain ⟨cap,need⟩ := mult x
    refine ⟨cap, fun twice => ?_⟩
    obtain ⟨y,mem,ne,eq⟩ := need twice
    exact ⟨y, List.mem_cons_of_mem _ mem, ne, eq.trans (compact_square x)⟩

end FanoSignature

#print axioms FanoSignature.closed
