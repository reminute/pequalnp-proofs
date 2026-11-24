import NamedReaders

namespace GirthRepresent

theorem checked_child : ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 → PEqualNP.MetaComplexity.circuitFun x2 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x3 ∅ → (¬∃ (x9 : Finset (Fin x6.gates.length)), x9.card = x1 + (1 : ℕ) ∧ (∀ x10 ∈ x9, ∃ (x12 : Fin x6.gates.length) (x13 : Fin x6.gates.length), x12 ≠ x13 ∧ x10 < x12 ∧ x2 + ↑x10 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x6 ↑x12).inputs ∧ x10 < x13 ∧ x2 + ↑x10 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x6 ↑x13).inputs) ∧ ∀ x10 ∈ x9, ∀ x12 ∈ x9, x10 < x12 → ∃ (x15 : Fin x2 → Bool), (∃ (x16 : Finset (Fin x2)), x16.card ≤ (2 : ℕ) ∧ x3.IsClique ↑x16 ∧ ((∀ (x17 : Fin x2), x15 x17 = Bool.true ↔ x17 ∈ x16) ∨ ∀ (x17 : Fin x2), x15 x17 = Bool.true ↔ x17 ∉ x16 ∧ ∃ x18 ∈ x16, x3.Adj x17 x18)) ∧ PEqualNP.EdgeOwnership.gateVal x2 x6 (↑x12) x15 = PEqualNP.MetaComplexity.circuitFun x2 x6 x15 ∧ PEqualNP.EdgeOwnership.gateVal x2 x6 (↑x10) x15 ≠ PEqualNP.MetaComplexity.circuitFun x2 x6 x15) → x3.edgeFinset.card ≤ ((2 : ℕ) ^ (x1 + (1 : ℕ)) - (1 : ℕ)) * (x6.size + (1 : ℕ)) := by
  intro k n G inst girth C mono computes missing
  apply tested_easy k n G girth C mono computes
  rintro ⟨Q,card,shared,sep⟩
  apply missing
  refine ⟨Q,card,fun j hj => distinct_readers (shared j hj),?_⟩
  intro t ht i hi lt
  obtain ⟨x,check,yes,no⟩ := sep t ht i hi lt
  exact ⟨x,tested_by_values G check,yes,no⟩

end GirthRepresent

#print axioms GirthRepresent.checked_child
