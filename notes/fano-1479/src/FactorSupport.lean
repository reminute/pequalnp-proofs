import FactorWitness

namespace FanoFactor

def support (f : Input → Bool) : Finset (Fin 14) :=
  Finset.univ.filter fun i => f (unitAt i) = true

private theorem pair_incidence (i j : Fin 14) :
    incidence (pairAt i j) = decide (∃ p l : Fin 7,
      (p=l ∨ p=l+1 ∨ p=l+3) ∧
      ((i=Fin.castAdd 7 p ∧ j=Fin.natAdd 7 l) ∨
       (j=Fin.castAdd 7 p ∧ i=Fin.natAdd 7 l))) := by
  revert i j
  decide +kernel

private theorem support_pair (a b : Fin 14) {A B : Input → Bool}
    (ma : Increasing A) (mb : Increasing B)
    (sound : ∀ x, A x = true → B x = true → incidence x = true)
    (ha : a ∈ support A) (hb : b ∈ support B) : incidence (pairAt a b) = true := by
  have leftOn : A (unitAt a) = true := (Finset.mem_filter.mp ha).2
  have rightOn : B (unitAt b) = true := (Finset.mem_filter.mp hb).2
  apply sound
  · exact ma _ _ (by simp [unitAt,pairAt]) leftOn
  · exact mb _ _ (by simp [unitAt,pairAt]) rightOn

-- In the undirected incidence graph, two distinct raw inputs have at most
-- one common neighbor. Compute the seven-bit geometry once per pair.
def neighbors (a : Fin 14) := Finset.univ.filter fun b =>
  decide (∃ p l : Fin 7, (p=l ∨ p=l+1 ∨ p=l+3) ∧
    ((a=Fin.castAdd 7 p ∧ b=Fin.natAdd 7 l) ∨
     (b=Fin.castAdd 7 p ∧ a=Fin.natAdd 7 l)))

theorem supported_neighbor {a b : Fin 14} {A B : Input → Bool}
    (ma : Increasing A) (mb : Increasing B)
    (sound : ∀ x, A x = true → B x = true → incidence x = true)
    (ha : a ∈ support A) (hb : b ∈ support B) : b ∈ neighbors a := by
  simpa [neighbors,pair_incidence] using support_pair a b ma mb sound ha hb

set_option maxHeartbeats 1200000 in
private theorem common_neighbors : ∀ a b : Fin 14, a ≠ b →
    ((neighbors a) ∩ (neighbors b)).card ≤ 1 := by decide +kernel

/-- A correct AND decomposition cannot have two different singleton witnesses
    in each operand. This also applies to arbitrary monotone Boolean factors. -/
theorem narrow_support {A B : Input → Bool} (ma : Increasing A) (mb : Increasing B)
    (sound : ∀ x, A x = true → B x = true → incidence x = true) :
    (support A).card ≤ 1 ∨ (support B).card ≤ 1 := by
  by_cases small : (support A).card ≤ 1
  · exact Or.inl small
  · rw [Finset.card_le_one] at small
    push Not at small
    obtain ⟨p,hp,q,hq,ne⟩ := small
    right
    apply Nat.le_trans _ (common_neighbors p q ne)
    apply Finset.card_le_card
    intro l hl
    have neighbor (i : Fin 14) (hi : i ∈ support A) : l ∈ neighbors i :=
      supported_neighbor ma mb sound hi hl
    exact Finset.mem_inter.mpr ⟨neighbor p hp,neighbor q hq⟩

end FanoFactor

#print axioms FanoFactor.narrow_support
