import Posted4237
import GraphCoreBounds

namespace GirthFiveCore

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

/-- The posted dense-residual bound is equivalent to a uniform linear bound on
    all edges of the graph class, for the original circuit model. -/
theorem posted_iff_all_edges : (∃ (x1 : ℕ) (x2 : ℕ), ∀ (x3 : ℕ) (x4 : SimpleGraph (Fin x3)) [x5 : DecidableRel x4.Adj], (∀ (x6 : Fin x3), x4.degree x6 = (0 : ℕ) ∨ (3 : ℕ) ≤ x4.degree x6) → (∀ (x7 : Fin x3) (x8 : x4.Walk x7 x7), x8.IsCycle → (5 : ℕ) ≤ x8.length) → ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 → PEqualNP.MetaComplexity.circuitFun x3 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x4 ∅ → ∀ x11 ⊆ {x12 ∈ x4.edgeFinset | ¬∃ (x13 : Fin x3) (x14 : Fin x3), x12 = s(x13, x14) ∧ ∃ (x15 : Fin x8.gates.length), PEqualNP.EdgeOwnership.Owns x3 x8 (↑x15) x13 x14 ∧ ∀ (x16 x17 : Fin x3), PEqualNP.EdgeOwnership.gateVal x3 x8 (↑x15) (PEqualNP.EdgeOwnership.pairInput x16 x17) = Bool.true → x4.Adj x16 x17}, (∀ (x13 : Fin x3), {x14 ∈ x11 | x13 ∈ x14}.card = (0 : ℕ) ∨ x1 < {x14 ∈ x11 | x13 ∈ x14}.card) → x11.card ≤ x2 * (x8.size + (1 : ℕ))) ↔
    ∃ K : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ v : Fin n, ∀ w : G.Walk v v, w.IsCycle → 5 ≤ w.length) →
      ∀ C : Circuit, Monotone2 C → circuitFun n C = graphFun G ∅ →
        G.edgeFinset.card ≤ K * (C.size + 1) := by
  rw [GirthAnchor.posted_iff]
  constructor
  · rintro ⟨D,K,h⟩
    refine ⟨K+D,?_⟩
    intro n G inst degrees cycles C mono computes
    exact all_edges_of_core C mono computes D K (h n G degrees cycles C mono computes)
  · rintro ⟨K,h⟩
    refine ⟨0,K,?_⟩
    intro n G inst degrees cycles C mono computes S sub _
    exact (Finset.card_le_card sub).trans (h n G degrees cycles C mono computes)

end GirthFiveCore

#print axioms GirthFiveCore.posted_iff_all_edges
