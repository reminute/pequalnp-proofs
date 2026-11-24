import Mathlib.Tactic

namespace FanoResidual

def remaining : Finset ℕ := Finset.Icc 1 6

/-- Covering just the six diagonal edges and six backward edges of the
    point-deleted Fano graph already forces its unique minimum vertex cover. -/
theorem unique_cover (points lines : Finset ℕ) (valid : points ⊆ remaining)
    (diag : ∀ p ∈ remaining, p ∈ points ∨ p ∈ lines)
    (back : ∀ p ∈ remaining, p ∈ points ∨ p-1 ∈ lines)
    (budget : points.card + lines.card ≤ 6) :
    points = remaining ∧ lines = ∅ := by
  let missing := remaining \ points
  have count : missing.card = 6 - points.card := by
    have six : remaining.card = 6 := by decide
    simpa [missing,six] using Finset.card_sdiff_of_subset valid
  have sub : missing ⊆ lines := by
    intro p hp
    obtain ⟨hin,habs⟩ := Finset.mem_sdiff.mp hp
    exact (diag p hin).resolve_left habs
  have empty : missing = ∅ := by
    by_contra h
    have nonempty := Finset.nonempty_iff_ne_empty.mpr h
    let m := missing.min' nonempty
    have hm : m ∈ missing := Finset.min'_mem _ _
    obtain ⟨hin,habs⟩ := Finset.mem_sdiff.mp hm
    have pos : 1 ≤ m := (Finset.mem_Icc.mp hin).1
    have prior : m-1 ∉ missing := by
      intro hp
      have le : m ≤ m-1 := Finset.min'_le missing _ hp
      omega
    have strict : missing ⊂ lines := Finset.ssubset_iff_subset_ne.mpr ⟨sub,by
      intro eq
      exact prior (eq ▸ (back m hin).resolve_left habs)⟩
    have lt := Finset.card_lt_card strict
    omega
  have eq : points = remaining := Finset.Subset.antisymm valid (by
    intro p hp
    by_contra h
    have mem : p ∈ missing := Finset.mem_sdiff.mpr ⟨hp,h⟩
    simp [empty] at mem)
  have six : points.card = 6 := eq ▸ (by decide : remaining.card = 6)
  exact ⟨eq,Finset.card_eq_zero.mp (by omega)⟩

def incident (p l : Fin 7) := p=l ∨ p=l+1 ∨ p=l+3
instance (p l : Fin 7) : Decidable (incident p l) := by unfold incident; infer_instance

/-- Among covers of the residual Fano incidence graph by at most six star
    centers, the centers are exactly the six remaining points. -/
theorem unique_residual_cover (points lines : Finset ℕ) (valid : points ⊆ remaining)
    (cover : ∀ p ∈ remaining, ∀ (l : ℕ), l < 7 → incident (Fin.ofNat 7 p) (Fin.ofNat 7 l) →
      p ∈ points ∨ l ∈ lines) (budget : points.card + lines.card ≤ 6) :
    points = remaining ∧ lines = ∅ := by
  apply unique_cover points lines valid _ _ budget
  · intro p hp
    have h := Finset.mem_Icc.mp hp
    exact cover p hp p (by omega) (Or.inl rfl)
  · intro p hp
    obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp hp
    apply cover p hp (p-1) (by omega)
    interval_cases p <;> decide

/-- Every rectangle of Fano incidences is a star.  In particular the
    line pencils of any two distinct points share no pair of distinct lines. -/
theorem no_rectangle : ∀ p q a b : Fin 7,
    incident p a → incident p b → incident q a → incident q b → p=q ∨ a=b := by
  decide +kernel

theorem rectangle_is_star (points lines : Finset (Fin 7))
    (rectangle : ∀ p ∈ points, ∀ l ∈ lines, incident p l) :
    points.card ≤ 1 ∨ lines.card ≤ 1 := by
  by_cases small : points.card ≤ 1
  · exact Or.inl small
  · rw [Finset.card_le_one] at small
    push Not at small
    obtain ⟨p,hp,q,hq,ne⟩ := small
    right
    rw [Finset.card_le_one]
    intro a ha b hb
    exact (no_rectangle p q a b (rectangle p hp a ha) (rectangle p hp b hb)
      (rectangle q hq a ha) (rectangle q hq b hb)).resolve_left ne

theorem no_shared_pair {p q a b : Fin 7} (different : p ≠ q) (pair : a ≠ b)
    (a₁ : incident p a) (b₁ : incident p b) : ¬ (incident q a ∧ incident q b) := by
  rintro ⟨a₂,b₂⟩
  exact (no_rectangle p q a b a₁ b₁ a₂ b₂).elim different pair

end FanoResidual

#print axioms FanoResidual.unique_residual_cover
#print axioms FanoResidual.rectangle_is_star
#print axioms FanoResidual.no_shared_pair
