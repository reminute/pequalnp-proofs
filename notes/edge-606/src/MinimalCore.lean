import ReaderCore

namespace Edge606.ReaderCore

open SimpleGraph GirthFiveCore
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open GraphDensity (edgeFunction)

/-- Every monotone circuit has a least-size monotone representative of its function. -/
theorem choose_minimal {n : ℕ} (C : Circuit) (mono : Monotone2 C) :
    ∃ D : Circuit, IsMinimalMonoCircuit n D ∧ circuitFun n D = circuitFun n C ∧
      D.size ≤ C.size := by
  classical
  let P (s : ℕ) := ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = circuitFun n C ∧ D.size = s
  have witness : ∃ s, P s := ⟨C.size, C, mono, rfl, rfl⟩
  obtain ⟨D, dm, equal, size⟩ := Nat.find_spec witness
  refine ⟨D, ⟨dm, ?_⟩, equal, ?_⟩
  · intro F fm computes
    rw [size]
    exact Nat.find_min' witness (show P F.size from ⟨F, fm, computes.trans equal, rfl⟩)
  · rw [size]
    exact Nat.find_min' witness (show P C.size from ⟨C, mono, rfl, rfl⟩)

/-- The same coefficient suffices when the hypothesis is restricted to circuits
    that are simultaneously minimal and sparse at all nonisolated vertices. -/
theorem fixed_coefficient_minimal (k : ℕ) : HighDegree.OnAll k ↔
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      LongCycles G → ∀ D : Circuit, IsMinimalMonoCircuit n D →
        circuitFun n D = edgeFunction G → sparseReads k G D →
        G.edgeFinset.card ≤ k * (D.size + 1) := by
  constructor
  · intro all n G inst girth D minimal computes _
    exact all n G girth D minimal.1 computes
  · intro hard
    let P (m : ℕ) := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.edgeFinset.card = m → LongCycles G → ∀ C : Circuit, Monotone2 C →
        circuitFun n C = edgeFunction G → G.edgeFinset.card ≤ k * (C.size + 1)
    have every (m : ℕ) : P m := by
      induction m using Nat.strong_induction_on with
      | ind m ih =>
        intro n G inst card girth C mono comp
        obtain ⟨D, minimal, eq, small⟩ := choose_minimal (n := n) C mono
        have computes := eq.trans comp
        apply Nat.le_trans _ (Nat.mul_le_mul_left k (Nat.succ_le_succ small))
        change G.edgeFinset.card ≤ k * (D.size + 1)
        by_cases sparse : sparseReads k G D
        · exact hard n G girth D minimal computes sparse
        · classical
          simp only [sparseReads, not_forall, not_lt] at sparse
          obtain ⟨v, hv, budget⟩ := sparse
          obtain ⟨F, fm, saving, feval⟩ := WeightedPin.peel G v D minimal.1 computes
          let H := G.deleteIncidenceSet v
          have safe : LongCycles H := by
            intro u w hw
            have sub : H ≤ G := G.deleteIncidenceSet_le v
            simpa using girth u (w.mapLe sub) (hw.mapLe sub)
          have available : G.degree v ≤ G.edgeFinset.card := by
            rw [← G.card_incidenceFinset_eq_degree v]
            exact Finset.card_le_card (G.incidenceFinset_subset v)
          have edgeCard : H.edgeFinset.card = G.edgeFinset.card - G.degree v :=
            G.card_edgeFinset_deleteIncidenceSet v
          have fewer : H.edgeFinset.card < m := by omega
          have inner := ih _ fewer n H rfl safe F fm feval
          have room := Nat.mul_le_mul_left k (Nat.succ_le_succ saving)
          have expand : k * (F.size + WeightedPin.readers D v + 1) =
              k * (F.size + 1) + k * WeightedPin.readers D v := by ring
          change k * (F.size + WeightedPin.readers D v + 1) ≤ k * (D.size + 1) at room
          rw [expand] at room
          omega
    intro n G inst girth C mono comp
    exact every _ n G rfl girth C mono comp

end Edge606.ReaderCore
