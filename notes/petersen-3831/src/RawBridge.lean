import RawPartner

namespace Petersen3831.RawBridge

/-- Literal receipt with the additional earlier-gate (rather than raw input) bound. -/
def Restricted : Prop := ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.inputs.contains (0 : ℕ)) x1.gates).length = (1 : ℕ) → x2 < x1.gates.length → (0 : ℕ) < x3 → (9 : ℕ) ≤ x3 → x3 < (9 : ℕ) + x2 → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.or → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).inputs = [(0 : ℕ), x3] → ∃ (x12 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x13 : Fin (9 : ℕ)) => if x13 = (0 : Fin (9 : ℕ)) then !x12 (0 : Fin (9 : ℕ)) else x12 x13) ≠ (x12 (0 : Fin (9 : ℕ)) && x12 (1 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (3 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (4 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)) && x12 (0 : Fin (9 : ℕ)) || x12 (0 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (6 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (5 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (6 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (8 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)))

/-- Verbatim L-meta-3831 receipt. -/
def Posted : Prop := ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.inputs.contains (0 : ℕ)) x1.gates).length = (1 : ℕ) → x2 < x1.gates.length → (0 : ℕ) < x3 → x3 < (9 : ℕ) + x2 → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.or → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).inputs = [(0 : ℕ), x3] → ∃ (x12 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x13 : Fin (9 : ℕ)) => if x13 = (0 : Fin (9 : ℕ)) then !x12 (0 : Fin (9 : ℕ)) else x12 x13) ≠ (x12 (0 : Fin (9 : ℕ)) && x12 (1 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (3 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (4 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)) && x12 (0 : Fin (9 : ℕ)) || x12 (0 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (6 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (5 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (6 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (8 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)))

theorem of_restricted (restricted : Restricted) : Posted := by
  intro C k a fan size once valid positive earlier op args
  by_cases raw : a<9
  · exact RawPartner.raw_partner C k a once valid positive raw op args
  · exact restricted C k a fan size once valid positive (by omega) earlier op args

theorem equivalent : Posted ↔ Restricted :=
  ⟨fun full C k a fan size once valid positive _ earlier op args =>
    full C k a fan size once valid positive earlier op args,of_restricted⟩

end Petersen3831.RawBridge

#print axioms Petersen3831.RawBridge.of_restricted
