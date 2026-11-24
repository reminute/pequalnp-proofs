import PinSignal
import GatePrefixRank

namespace GirthFiveCore

open GirthPin GirthWires Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

/-- Pinning a gate erases its arguments while preserving every other gate's
    inputs and the output selector, so it cannot create new readers. -/
theorem force_reads_le (n : ℕ) (C : Circuit) (j : ℕ) (b : Bool)
    (k : Fin (force n C j b).gates.length) :
    gateReads (n := n) (force n C j b) k ≤
      gateReads (n := n) C ⟨k.val,by simpa using k.isLt⟩ := by
  let w := n + k.val
  change (if (force n C j b).output = w then 1 else 0) +
      (∑ i : Fin (force n C j b).gates.length, (gateAt (force n C j b) i.val).inputs.count w) ≤
    (if C.output = w then 1 else 0) +
      (∑ i : Fin C.gates.length, (gateAt C i.val).inputs.count w)
  rw [force_output]
  apply Nat.add_le_add_left
  have sumCmp {a d : ℕ} (same : a = d) (f g : ℕ → ℕ) (each : ∀ i < d, f i ≤ g i) :
      (∑ i : Fin a, f i.val) ≤ (∑ i : Fin d, g i.val) := by
    subst a
    exact sum_le_sum (fun i _ => each i.val i.isLt)
  apply sumCmp (force_length n C j b) (fun i => (gateAt (force n C j b) i).inputs.count w)
    (fun i => (gateAt C i).inputs.count w)
  intro i valid
  rw [force_inputs n C j b i valid]
  by_cases eq : i = j <;> simp [eq]

/-- If the only shared gate is pinned, each remaining shared signal is
    constant, even when the distinguished gate has arbitrarily many readers. -/
theorem force_signal_bound {n : ℕ} (ρ : Signal n → ℕ) (B : ℕ) (sums : Sums ρ)
    (input : ∀ v : Fin n, ρ (fun x => x v) ≤ B) (C : Circuit) (mono : Monotone2 C)
    (j : Fin C.gates.length) (b : Bool)
    (unique : ∀ i : Fin C.gates.length, 1 < gateReads (n := n) C i → i = j) :
    ρ (circuitFun n (force n C j.val b)) ≤ B*(C.size+1) := by
  rw [← force_size n C j.val b]
  apply signal_bound ρ B sums input _ (force_mono n C j.val b mono)
  intro k many
  have eq := unique _ (many.trans_le (force_reads_le n C j.val b k))
  have same : k.val = j.val := congrArg Fin.val eq
  rw [same,pinned_signal n C j.val b j.isLt,sums.const]
  exact Nat.zero_le _

/-- A single shared gate, of arbitrary fanout, costs at most three times
    the formula allowance: two forced outputs and the selected gate. -/
theorem one_shared_signal_bound {n : ℕ} (ρ : Signal n → ℕ) (B : ℕ) (sums : Sums ρ)
    (input : ∀ v : Fin n, ρ (fun x => x v) ≤ B) (C : Circuit) (mono : Monotone2 C)
    (j : Fin C.gates.length)
    (unique : ∀ i : Fin C.gates.length, 1 < gateReads (n := n) C i → i = j) :
    ρ (circuitFun n C) ≤ 3*(B*(C.size+1)) := by
  have gate : ρ (gateVal n C j.val) ≤ B*(C.size+1) :=
    gate_signal_bound ρ B sums input C mono j (by
      intro i earlier many
      have eq := unique i many
      exact (Nat.ne_of_lt earlier (congrArg Fin.val eq)).elim)
  have low := force_signal_bound ρ B sums input C mono j false unique
  have high := force_signal_bound ρ B sums input C mono j true unique
  have prod := sums.conj (gateVal n C j.val) (circuitFun n (force n C j.val true))
  have plus := sums.disj (circuitFun n (force n C j.val false))
    (fun x => gateVal n C j.val x && circuitFun n (force n C j.val true) x)
  rw [shannon_fun C mono j.val]
  omega

end GirthFiveCore
