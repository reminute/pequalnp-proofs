import RankTelescope
import RankWires

namespace GirthFiveCore

open GirthWires PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1490

def gateReads {n : ℕ} (C : Circuit) (j : Fin C.gates.length) : ℕ :=
  readCount (fun i : Fin C.gates.length => (gateAt C i).inputs) C.output (n+j.val)

/-- The output measure is bounded by the input allowance and an explicit
    sum over the repeated reads of each gate. -/
theorem signal_with_extra_reads {n : ℕ} (ρ : Signal n → ℕ) (B : ℕ) (sums : Sums ρ)
    (input : ∀ v : Fin n, ρ (fun x => x v) ≤ B) (C : Circuit) (mono : Monotone2 C) :
    ρ (circuitFun n C) ≤ B*(C.size+1) + ∑ j : Fin C.gates.length,
      (gateReads (n := n) C j - 1) * (ρ (signal n C (n+j.val)) - B) := by
  rw [output_signal C]
  apply rank_with_extra_reads n C.gates.length B C.output (fun i => (gateAt C i).inputs)
    (fun w => ρ (signal n C w))
  · intro i
    exact (mono _ (gateAt_mem i.isLt)).2
  · intro w bad
    rcases bad with raw | off
    · let v : Fin n := ⟨w,raw⟩
      exact (input_signal C v ▸ input v : ρ (signal n C v.val) ≤ B)
    · rw [invalid_signal C off,sums.const]
      exact Nat.zero_le _
  · exact gate_bound_total sums mono

/-- A signal measure subadditive under both gates extends a bound on shared
    signals to the output of the actual circuit. -/
theorem signal_bound {n : ℕ} (ρ : Signal n → ℕ) (B : ℕ) (sums : Sums ρ)
    (input : ∀ v : Fin n, ρ (fun x => x v) ≤ B) (C : Circuit) (mono : Monotone2 C)
    (shared : ∀ j : Fin C.gates.length, 1 < gateReads (n := n) C j →
      ρ (signal n C (n+j.val)) ≤ B) :
    ρ (circuitFun n C) ≤ B*(C.size+1) := by
  have zero (j : Fin C.gates.length) :
      (gateReads (n := n) C j - 1) * (ρ (signal n C (n+j.val)) - B) = 0 := by
    by_cases many : 1 < gateReads (n := n) C j
    · simp [Nat.sub_eq_zero_of_le (shared j many)]
    · simp [Nat.sub_eq_zero_of_le (Nat.le_of_not_gt many)]
  simpa only [zero, Finset.sum_const_zero, Nat.add_zero] using
    signal_with_extra_reads ρ B sums input C mono

/-- Any violation of the linear output bound demands an explicitly shared,
    high-weight gate in the original circuit. -/
theorem large_shared {n : ℕ} (ρ : Signal n → ℕ) (B : ℕ) (sums : Sums ρ)
    (input : ∀ v : Fin n, ρ (fun x => x v) ≤ B) (C : Circuit) (mono : Monotone2 C)
    (large : B*(C.size+1) < ρ (circuitFun n C)) :
    ∃ j : Fin C.gates.length, 1 < gateReads (n := n) C j ∧ B < ρ (signal n C (n+j.val)) := by
  by_contra! h
  exact (Nat.not_lt_of_ge (signal_bound ρ B sums input C mono h)) large

end GirthFiveCore
