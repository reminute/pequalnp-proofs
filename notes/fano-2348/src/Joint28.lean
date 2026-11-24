import Joint25
import JointFactor

namespace FanoJoint28

open PEqualNP.CircuitLowerBounds FanoPadding FanoFactor

def circuit : Circuit := FanoJoint.extend FanoJoint25.circuit 36 38

theorem exact_circuit : circuit.size=28 ∧ Normal circuit ∧ Spec circuit ∧
    Trace circuit point line ∧ Trace circuit line point := by
  refine ⟨rfl,FanoJoint.gadget_traces FanoJoint25.circuit FanoJoint25.normalized
    (h := 36) (n := 38) (by decide) (by decide) ?_ ?_⟩
  · intro x
    change (FanoJoint25.circuit.wires (List.ofFn x)).getD 36 false=_
    rw [(FanoJoint25.outputs x).1,Bool.eq_iff_iff]
    simpa only [FanoJoint.H,decide_eq_true_eq] using FanoJoint25.remainder_spec x
  · intro x
    change (FanoJoint25.circuit.wires (List.ofFn x)).getD 38 false=_
    rw [(FanoJoint25.outputs x).2,Bool.eq_iff_iff]
    simpa only [FanoJoint.N,decide_eq_true_eq] using FanoJoint25.pencil_spec x 0

theorem checked : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 28 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧ ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (14 + ky) = (((C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 14 => decide (ey = Fin.castAdd 7 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 7, w mx.val = decide (mx = p) ∧ w (7 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + kx) = (((C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 14 => decide (ex = Fin.natAdd 7 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + kx) = (w cx || w dx))) ∧ w C.output = false) := by
  obtain ⟨size,normal,spec,⟨v,vin,vr,vout⟩,w,win,wr,wout⟩ := exact_circuit
  let p : Fin 7 := 1
  let l : Fin 7 := 1
  change (∀ i : Fin 14, v i.val=decide (i=Fin.natAdd 7 l)) at vin
  change (∀ i : Fin 14, w i.val=decide (i=Fin.castAdd 7 p)) at win
  refine ⟨circuit,size.le,normal,spec,p,l,Or.inl rfl,⟨v,?_,vr,vout⟩,w,?_,wr,wout⟩
  · intro m
    constructor
    · simpa [Fin.ext_iff,show m.val ≠ l.val+7 by omega] using vin (Fin.castAdd 7 m)
    · simpa [Fin.ext_iff,Nat.add_comm 7] using vin (Fin.natAdd 7 m)
  · intro m
    constructor
    · simpa [Fin.ext_iff] using win (Fin.castAdd 7 m)
    · simpa [Fin.ext_iff,Nat.add_comm 7,show m.val+7 ≠ p.val by omega] using win (Fin.natAdd 7 m)

end FanoJoint28

#print axioms FanoJoint28.checked
