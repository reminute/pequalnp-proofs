import PartnerWidth

namespace Cubic1971

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem closedWidth : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Fin x1) (x7 x8 : List PEqualNP.CircuitLowerBounds.Gate) (x9 : PEqualNP.CircuitLowerBounds.Gate) (x10 : ℕ), (∀ (x11 x12 : Fin x1), x2.Adj x11 x12 → x11 ∉ x4) → (∀ (x12 : Fin x1) (x13 : x2.Walk x12 x12), x13.IsCycle → (5 : ℕ) ≤ x13.length) → (x2.neighborSet x6).ncard = (3 : ℕ) → x6 ∉ x4 → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 → (∀ (x17 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.circuitFun x1 x5) x17 → x5.size ≤ x17) → (List.filter (fun (x18 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x18.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x18.inputs).contains ↑x6) x5.gates).length ≤ (1 : ℕ) → x5.gates = x7 ++ x9 :: x8 → x9.op = PEqualNP.CircuitLowerBounds.GateOp.and → x9.inputs = [↑x6, x10] ∨ x9.inputs = [x10, ↑x6] → (∀ x22 ∈ x8, x22.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → x10 ≠ ↑x6 → x5.output ≠ ↑x6 → ∀ (x25 : Finset (Fin x1)), x25.card ≤ (2 : ℕ) → x6 ∉ x25 → ∃ (x28 : Fin x1 → Bool) (x29 : Fin x1 → Bool), (∀ x30 ∈ x25, x28 x30 = x29 x30) ∧ PEqualNP.MetaComplexity.circuitFun x1 { gates := x7, output := x10 : PEqualNP.CircuitLowerBounds.Circuit } x28 ≠ PEqualNP.MetaComplexity.circuitFun x1 { gates := x7, output := x10 : PEqualNP.CircuitLowerBounds.Circuit } x29 := by
  intro n G inst A C v pre post g k ordinary girth degree hv legal correct least one layout op args pos other out K small away
  have read : StarReader.effective v.val g := by
    rcases args with h | h <;> simp [StarReader.effective, op, h, GateOp.eval]
  have sole := StarReader.sole_of_count layout read one
  exact PartnerWidth.no_pair G A v (fun {_ _} h => ordinary _ _ h) girth degree hv C pre post g k
    layout legal sole op args other out correct least pos K small away

end Cubic1971

#print axioms Cubic1971.closedWidth
