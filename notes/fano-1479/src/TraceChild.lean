import FanoPadding

open PEqualNP.CircuitLowerBounds FanoPadding

namespace FanoTraceChild

theorem checked : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) → ∀ (x3 x4 : Fin (14 : ℕ) → Bool) (x5 x6 x7 : ℕ), x1.gates[x5]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x6, x7] : PEqualNP.CircuitLowerBounds.Gate } → (x1.wires (List.ofFn x3)).getD x6 Bool.false = Bool.false → (x1.wires (List.ofFn x3)).getD x7 Bool.false = Bool.false → ∃ (x11 : ℕ → Bool), (∀ (x12 : Fin (14 : ℕ)), x11 ↑x12 = x4 x12) ∧ (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate) (x14 x15 : ℕ), x1.gates[x12]? = Option.some x13 → x13.inputs = [x14, x15] → (x13.op = PEqualNP.CircuitLowerBounds.GateOp.and → x11 ((14 : ℕ) + x12) = ((x1.wires (List.ofFn x3)).getD x14 Bool.false && x11 x15 || x11 x14 && (x1.wires (List.ofFn x3)).getD x15 Bool.false)) ∧ (x13.op = PEqualNP.CircuitLowerBounds.GateOp.or → x11 ((14 : ℕ) + x12) = (x11 x14 || x11 x15))) ∧ x11 ((14 : ℕ) + x5) = Bool.false := by
  intro C normal x seed k a b gate da db
  let base := C.wires (List.ofFn x)
  let start (i : Nat) : Bool := if inRange : i<14 then seed ⟨i,inRange⟩ else false
  let v := derivative C base start
  have rules : Rules C base v := derivative_rules C normal base start
  have last := (rules k _ a b gate rfl).1 rfl
  change v (14+k)=((base.getD a false && v b) || (v a && base.getD b false)) at last
  change base.getD a false=false at da
  change base.getD b false=false at db
  rw [da,db] at last
  refine ⟨v,?_,rules,by simpa only [Bool.false_and,Bool.and_false,Bool.or_self] using last⟩
  intro i
  change derivative C base start i.val=seed i
  rw [derivative_raw C base start i.isLt]
  simp [start,i.isLt]

end FanoTraceChild

#print axioms FanoTraceChild.checked
