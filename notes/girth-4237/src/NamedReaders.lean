import SampleWitness

namespace GirthRepresent

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

variable {n : ℕ}

theorem distinct_readers {C : Circuit} {j : Fin C.gates.length} (h : 1 < (readers n C j).card) :
    ∃ a b : Fin C.gates.length, a ≠ b ∧ j < a ∧ n+j.val ∈ (gateAt C a.val).inputs ∧
      j < b ∧ n+j.val ∈ (gateAt C b.val).inputs := by
  obtain ⟨a,b,am,bm,diff⟩ := Finset.one_lt_card_iff.mp h
  have first := (Finset.mem_filter.mp am).2
  have second := (Finset.mem_filter.mp bm).2
  exact ⟨a,b,diff,first.1,first.2,second⟩

theorem tested_by_values (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {x : Fin n → Bool}
    (h : tested G x) :
    ∃ U : Finset (Fin n), U.card ≤ 2 ∧ G.IsClique (U : Set (Fin n)) ∧
      ((∀ v, x v = true ↔ v ∈ U) ∨ (∀ v, x v = true ↔ v ∉ U ∧ ∃ w ∈ U, G.Adj v w)) := by
  obtain ⟨U,few,clique,inside | outside⟩ := h
  · exact ⟨U,few,clique,Or.inl (fun v => by simp [inside])⟩
  · refine ⟨U,few,clique,Or.inr ?_⟩
    intro v
    rw [outside]
    exact decide_eq_true_iff

end GirthRepresent
