import WeightedPin
import HighDegreeReduction

namespace Edge606.ReaderCore

open SimpleGraph GirthFiveCore
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open GraphDensity (edgeFunction)

/-- Each nonisolated vertex has more incident edges than k times its direct gate reads. -/
def sparseReads {n : ℕ} (k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : Prop :=
  ∀ v, 0 < G.degree v → k * WeightedPin.readers C v < G.degree v

theorem high_degree {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (comp : circuitFun n C = edgeFunction G) (sparse : sparseReads k G C)
    (v : Fin n) (active : 0 < G.degree v) : k < G.degree v := by
  obtain ⟨j, hj⟩ := PEqualNP.Outside.L_meta_1708_aux.reads_vertex G v active C comp
  have pos : 1 ≤ WeightedPin.readers C v :=
    Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  have cost : k ≤ k * WeightedPin.readers C v := by
    simpa using Nat.mul_le_mul_left k pos
  exact cost.trans_lt (sparse v active)

/-- For a fixed coefficient k, it suffices to consider circuits with few
    direct reads at every nonisolated vertex, without any loss in k. -/
theorem fixed_coefficient (k : ℕ) : HighDegree.OnAll k ↔
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      LongCycles G → ∀ C : Circuit, Monotone2 C → circuitFun n C = edgeFunction G →
        sparseReads k G C → G.edgeFinset.card ≤ k * (C.size + 1) := by
  constructor
  · intro h n G inst girth C mono comp _
    exact h n G girth C mono comp
  · intro hard
    let P (m : ℕ) := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.edgeFinset.card = m → LongCycles G → ∀ C : Circuit, Monotone2 C →
        circuitFun n C = edgeFunction G → G.edgeFinset.card ≤ k * (C.size + 1)
    have every (m : ℕ) : P m := by
      induction m using Nat.strong_induction_on with
      | ind m ih =>
        intro n G inst card girth C mono comp
        by_cases sparse : sparseReads k G C
        · exact hard n G girth C mono comp sparse
        · classical
          simp only [sparseReads, not_forall, not_lt] at sparse
          obtain ⟨v, hv, budget⟩ := sparse
          obtain ⟨D, dm, saving, deval⟩ := WeightedPin.peel G v C mono comp
          let H := G.deleteIncidenceSet v
          have safe : LongCycles H := by
            intro u w hw
            have sub : H ≤ G := G.deleteIncidenceSet_le v
            simpa using girth u (w.mapLe sub) (hw.mapLe sub)
          have leEdges : G.degree v ≤ G.edgeFinset.card := by
            rw [← G.card_incidenceFinset_eq_degree v]
            exact Finset.card_le_card (G.incidenceFinset_subset v)
          have edgeCard : H.edgeFinset.card = G.edgeFinset.card - G.degree v :=
            G.card_edgeFinset_deleteIncidenceSet v
          have fewer : H.edgeFinset.card < m := by omega
          have inner := ih _ fewer n H rfl safe D dm deval
          have room := Nat.mul_le_mul_left k (Nat.succ_le_succ saving)
          have expand : k * (D.size + WeightedPin.readers C v + 1) =
              k * (D.size + 1) + k * WeightedPin.readers C v := by ring
          change k * (D.size + WeightedPin.readers C v + 1) ≤ k * (C.size + 1) at room
          rw [expand] at room
          omega
    intro n G inst girth C mono comp
    exact every _ n G rfl girth C mono comp

end Edge606.ReaderCore

#print axioms Edge606.ReaderCore.fixed_coefficient
#print axioms Edge606.ReaderCore.high_degree
