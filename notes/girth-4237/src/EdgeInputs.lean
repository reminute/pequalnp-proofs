import PinnedSupport
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace GirthFiveCore

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

/-- Apply the project's joint wire-support count to the essential variables of
    the edge function. This allows isolated vertices and invalid wire indices. -/
theorem edge_inputs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (fan : FanInTwo C) (computes : circuitFun n C = graphFun G ∅) :
    G.support.toFinset.card ≤ C.size + 1 := by
  classical
  let S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅
  have contains : G.support.toFinset ⊆ S := by
    intro v hv
    obtain ⟨w,adj⟩ := Set.mem_toFinset.mp hv
    by_contra absent
    let one (i : Fin n) := decide (i = w)
    have ag := (agree_wiresFrom (pairInput v w) one C.gates _ _ _ (agree_inputs _ _)).2.2
      C.output (by
        intro k hk
        have off : k ≠ v := fun h => absent (h ▸ hk)
        simp [pairInput, one, off])
    change circuitFun n C (pairInput v w) = circuitFun n C one at ag
    rw [computes] at ag
    have yes : graphFun G ∅ (pairInput v w) = true := by
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq]
      exact ⟨v,w,adj,by simp [pairInput],by simp [pairInput]⟩
    have no : graphFun G ∅ one = false := by
      simp [graphFun, one]
    rw [yes,no] at ag
    contradiction
  have count := cnt_suppsFrom C.gates 0 (inputSupps n) fan cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion,Finset.card_singleton,zero_add] at count
  exact (Finset.card_le_card contains).trans count

theorem mono_fan {C : Circuit} (mono : Monotone2 C) : FanInTwo C := by
  intro g hg
  obtain ⟨op,len⟩ := mono g hg
  exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using
             (show g.op = .and ∨ g.op = .or ∨ g.op = .not from
               ((show g.op = .and ∨ g.op = .or from op).imp_right Or.inl)),len⟩

end GirthFiveCore
