import RankCircuitBound

namespace GirthFiveCore

open GirthWires Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1490 PEqualNP.MetaComplexity.NestedCover

/-- When a gate is chosen as output, its own signal requires one output read.
    Only earlier wires can contribute to it. In particular the change of
    output introduces no new shared gate, even with malformed forward reads. -/
theorem gate_signal_bound {n : ℕ} (ρ : Signal n → ℕ) (B : ℕ) (sums : Sums ρ)
    (input : ∀ v : Fin n, ρ (fun x => x v) ≤ B) (C : Circuit) (mono : Monotone2 C)
    (j : Fin C.gates.length)
    (shared : ∀ i : Fin C.gates.length, i.val < j.val → 1 < gateReads (n := n) C i →
      ρ (signal n C (n+i.val)) ≤ B) :
    ρ (signal n C (n+j.val)) ≤ B*(C.size+1) := by
  let cut := n+j.val
  let W (w : ℕ) := if w ≤ cut then ρ (signal n C w) else 0
  let I (i : Fin C.gates.length) := (gateAt C i.val).inputs.filter (· < cut)
  have prefixSum (i : Fin C.gates.length) (early : n+i.val ≤ cut) (ws : List ℕ) :
      (ws.map (charge n ρ C i.val)).sum ≤ ((ws.filter (· < cut)).map W).sum := by
    induction ws with
    | nil => simp
    | cons w ws ih =>
      by_cases kept : w < cut
      · simp only [List.filter_cons, decide_eq_true kept, ite_true, List.map_cons, List.sum_cons]
        apply Nat.add_le_add _ ih
        by_cases available : w < n+i.val <;> simp [W, charge, Nat.le_of_lt kept, available]
      · have past : ¬w < n+i.val := fun h => kept (h.trans_le early)
        simpa [kept, charge, past] using ih
  have out : W cut ≤ B*(C.gates.length+1) := by
    apply rank_telescope n C.gates.length B cut I W
    · intro i
      exact (List.length_filter_le _ _).trans (mono _ (gateAt_mem i.isLt)).2
    · intro w bad
      by_cases le : w ≤ cut
      · rw [show W w = ρ (signal n C w) by simp [W,le]]
        rcases bad with raw | off
        · let v : Fin n := ⟨w,raw⟩
          exact (input_signal C v ▸ input v : ρ (signal n C v.val) ≤ B)
        · rw [invalid_signal C off,sums.const]
          exact Nat.zero_le _
      · simp [W,le]
    · intro i
      by_cases le : n+i.val ≤ cut
      · rw [show W (n+i.val) = ρ (signal n C (n+i.val)) by simp [W,le]]
        exact (gate_bound sums mono i).trans (prefixSum i le _)
      · simp [W,le]
    · intro i many
      by_cases eq : i = j
      · subst i
        have zero (k : Fin C.gates.length) : (I k).count (n+j.val) = 0 := by
          apply List.count_eq_zero_of_not_mem
          intro mem
          have impossible := (List.mem_filter.mp mem).2
          simp [cut] at impossible
        simp [readCount, cut, zero] at many
      · have different : cut ≠ n+i.val := fun h => eq (Fin.ext (by dsimp [cut] at h; omega))
        have leReads : readCount I cut (n+i.val) ≤ gateReads (n := n) C i := by
          unfold readCount gateReads
          simp only [different,ite_false,zero_add]
          apply le_trans _ (Nat.le_add_left ..)
          exact sum_le_sum fun k _ => (List.filter_sublist).count_le _
        by_cases le : n+i.val ≤ cut
        · have earlier : i.val < j.val := by
            have ne : i.val ≠ j.val := fun h => eq (Fin.ext h)
            dsimp [cut] at le
            omega
          simpa [W,le] using shared i earlier (many.trans_le leReads)
        · simp [W,le]
  simpa [W,cut, Circuit.size] using out

end GirthFiveCore
