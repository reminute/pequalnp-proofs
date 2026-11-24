import RankCircuitBound
import Mathlib.Data.List.Dedup

namespace GirthFiveCore

open GirthWires PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_1490

/-- Each earlier input wire appears at most once per consuming gate. -/
def dependencies (n : ℕ) (C : Circuit) (j : Fin C.gates.length) : List ℕ :=
  (gateAt C j.val).inputs.dedup.filter (fun w => decide (w < n+j.val))

theorem dedup_gate (op : GateOp) (kind : op = .and ∨ op = .or) (ws : List ℕ)
    (value : ℕ → Bool) : op.eval (ws.map value) = op.eval (ws.dedup.map value) := by
  apply Bool.eq_iff_iff.mpr
  rcases kind with rfl | rfl <;> simp [GateOp.eval]

theorem dependent_gate {n : ℕ} {ρ : Signal n → ℕ} (sums : Sums ρ)
    {C : Circuit} (mono : Monotone2 C) (j : Fin C.gates.length) :
    ρ (signal n C (n+j.val)) ≤ ((dependencies n C j).map (fun w => ρ (signal n C w))).sum := by
  let g := gateAt C j.val
  have kind := (mono g (gateAt_mem j.isLt)).1
  have same : gateVal n C j.val = fun x =>
      g.op.eval ((g.inputs.dedup.map (readSignal n C j.val)).map (fun f => f x)) := by
    rw [evaluated_gate C j.isLt]
    funext x
    simp only [List.map_map]
    exact dedup_gate g.op kind g.inputs _
  rw [gate_signal, same]
  apply (list_bound sums g.op kind _).trans_eq
  simp only [List.map_map, dependencies]
  change (g.inputs.dedup.map _).sum = ((g.inputs.dedup.filter _).map _).sum
  generalize g.inputs.dedup = ws
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    by_cases h : w < n+j.val <;> simp [h, readSignal, sums.const, ih]

/-- The wires whose values determine the output by tracing gates backwards. -/
inductive ReachesOutput (n : ℕ) (C : Circuit) : ℕ → Prop where
  | output : ReachesOutput n C C.output
  | input {j : Fin C.gates.length} {w : ℕ} (parent : ReachesOutput n C (n+j.val))
      (used : w ∈ dependencies n C j) : ReachesOutput n C w

noncomputable def liveInputs (n : ℕ) (C : Circuit) (j : Fin C.gates.length) : List ℕ := by
  classical
  exact if ReachesOutput n C (n+j.val) then dependencies n C j else []

noncomputable def liveReads (n : ℕ) (C : Circuit) (j : Fin C.gates.length) : ℕ :=
  readCount (liveInputs n C) C.output (n+j.val)

/-- Only distinct downstream consumers on a path to the output incur a cost.
    Forward references are constant false at evaluation time. -/
theorem live_sharing_bound {n : ℕ} (ρ : Signal n → ℕ) (B : ℕ) (sums : Sums ρ)
    (raw : ∀ v : Fin n, ρ (fun x => x v) ≤ B) (C : Circuit) (mono : Monotone2 C) :
    ρ (circuitFun n C) ≤ B*(C.size+1) + ∑ j : Fin C.gates.length,
      (liveReads n C j-1) * (ρ (gateVal n C j.val)-B) := by
  classical
  let wt (w : ℕ) := if ReachesOutput n C w then ρ (signal n C w) else 0
  have arity (j : Fin C.gates.length) : (liveInputs n C j).length ≤ 2 := by
    unfold liveInputs
    split
    · exact (List.length_filter_le ..).trans ((List.dedup_sublist _).length_le.trans
        ((mono _ (gateAt_mem j.isLt)).2))
    · decide
  have outside (w : ℕ) (hw : w < n ∨ n+C.gates.length ≤ w) : wt w ≤ B := by
    dsimp [wt]
    split
    · rcases hw with h | h
      · exact (input_signal C ⟨w,h⟩ ▸ raw ⟨w,h⟩ : ρ (signal n C w) ≤ B)
      · simp [invalid_signal C h,sums.const]
    · exact Nat.zero_le _
  have gate (j : Fin C.gates.length) : wt (n+j.val) ≤ ((liveInputs n C j).map wt).sum := by
    by_cases h : ReachesOutput n C (n+j.val)
    · have eq : (dependencies n C j).map wt =
          (dependencies n C j).map (fun w => ρ (signal n C w)) :=
        List.map_congr_left fun _ used => ite_eq_left (ReachesOutput.input h used)
      simpa only [wt, liveInputs, ite_eq_left h] using (dependent_gate sums mono j).trans_eq
        (congrArg List.sum eq.symm)
    · simp [wt, h]
  have bound := rank_with_extra_reads n C.gates.length B C.output _ wt arity outside gate
  have out : wt C.output = ρ (circuitFun n C) := ite_eq_left ReachesOutput.output
  rw [out] at bound
  apply bound.trans
  apply Nat.add_le_add_left
  apply Finset.sum_le_sum
  intro j _
  apply Nat.mul_le_mul_left
  apply Nat.sub_le_sub_right
  dsimp [wt]
  split <;> simp [gate_signal]

end GirthFiveCore
