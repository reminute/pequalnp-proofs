import EffectiveReads

namespace GirthFiveCore

open GirthWires Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_1490

theorem live_input_properties {n : ℕ} {C : Circuit} {k : Fin C.gates.length} {w : ℕ}
    (mem : w ∈ liveInputs n C k) : ReachesOutput n C w ∧ w < n+k.val := by
  classical
  unfold liveInputs at mem
  split at mem
  · rename_i parent
    exact ⟨ReachesOutput.input parent mem,of_decide_eq_true (List.mem_filter.mp mem).2⟩
  · simp at mem

/-- Even a single live read witnesses a dependency path to the output. -/
theorem reaches_of_live_reads {n : ℕ} {C : Circuit} {j : Fin C.gates.length}
    (positive : 0 < liveReads n C j) : ReachesOutput n C (n+j.val) := by
  classical
  by_contra dead
  have notOutput : C.output ≠ n+j.val := fun h => dead (h ▸ ReachesOutput.output)
  have zero (i : Fin C.gates.length) : (liveInputs n C i).count (n+j.val) = 0 :=
    List.count_eq_zero_of_not_mem (fun mem => dead (live_input_properties mem).1)
  simp [liveReads,readCount,notOutput,zero] at positive

/-- The selected live gate depends only on earlier live gates. In the prefix
    the selected gate has exactly one read, and no other read count increases. -/
theorem live_gate_signal_bound {n : ℕ} (ρ : Signal n → ℕ) (B : ℕ) (sums : Sums ρ)
    (raw : ∀ v : Fin n, ρ (fun x => x v) ≤ B) (C : Circuit) (mono : Monotone2 C)
    (j : Fin C.gates.length) (active : ReachesOutput n C (n+j.val))
    (shared : ∀ i : Fin C.gates.length, i.val < j.val → 1 < liveReads n C i →
      ρ (signal n C (n+i.val)) ≤ B) :
    ρ (signal n C (n+j.val)) ≤ B*(C.size+1) := by
  classical
  let cut := n+j.val
  let W (w : ℕ) := if w ≤ cut ∧ ReachesOutput n C w then ρ (signal n C w) else 0
  let I (k : Fin C.gates.length) := if k ≤ j then liveInputs n C k else []
  have arity (k : Fin C.gates.length) : (I k).length ≤ 2 := by
    dsimp [I,liveInputs]
    split <;> try decide
    split
    · exact (List.length_filter_le ..).trans ((List.dedup_sublist _).length_le.trans
        (mono _ (gateAt_mem k.isLt)).2)
    · decide
  have outside (w : ℕ) (bad : w < n ∨ n+C.gates.length ≤ w) : W w ≤ B := by
    dsimp [W]
    split
    · rcases bad with rawWire | invalid
      · exact (input_signal C ⟨w,rawWire⟩ ▸ raw ⟨w,rawWire⟩ : ρ (signal n C w) ≤ B)
      · simp [invalid_signal C invalid,sums.const]
    · exact Nat.zero_le _
  have gate (k : Fin C.gates.length) : W (n+k.val) ≤ ((I k).map W).sum := by
    by_cases both : n+k.val ≤ cut ∧ ReachesOutput n C (n+k.val)
    · have le : k ≤ j := Nat.le_of_add_le_add_left both.1
      have eq : (dependencies n C k).map W =
          (dependencies n C k).map (fun w => ρ (signal n C w)) := by
        apply List.map_congr_left
        intro w mem
        have used : w ∈ liveInputs n C k := by simpa [liveInputs,both.2] using mem
        have prop := live_input_properties used
        exact ite_eq_left ⟨prop.2.le.trans both.1,prop.1⟩
      simpa [I,le,liveInputs,both.2,show W (n+k.val) = ρ (signal n C (n+k.val)) from ite_eq_left both,eq]
        using dependent_gate sums mono k
    · simp [W,both]
  have sharedSmall (k : Fin C.gates.length) (many : 1 < readCount I cut (n+k.val)) : W (n+k.val) ≤ B := by
    by_cases eq : k = j
    · subst k
      have zero (i : Fin C.gates.length) : (I i).count (n+j.val) = 0 := by
        apply List.count_eq_zero_of_not_mem
        intro mem
        by_cases le : i ≤ j
        · have used : n+j.val ∈ liveInputs n C i := by simpa [I,le] using mem
          have lt := (live_input_properties used).2
          omega
        · simp [I,le] at mem
      simp [readCount,cut,zero] at many
    · by_cases both : n+k.val ≤ cut ∧ ReachesOutput n C (n+k.val)
      · have lt : k.val < j.val := by
          have ne : k.val ≠ j.val := fun he => eq (Fin.ext he)
          have le : k ≤ j := Nat.le_of_add_le_add_left both.1
          omega
        have different : cut ≠ n+k.val := by dsimp [cut]; omega
        have leReads : readCount I cut (n+k.val) ≤ liveReads n C k := by
          unfold liveReads readCount
          simp only [different,ite_false,zero_add]
          apply le_trans _ (Nat.le_add_left ..)
          apply sum_le_sum
          intro i _
          by_cases le : i ≤ j <;> simp [I,le]
        simpa [W,both] using shared k lt (many.trans_le leReads)
      · simp [W,both]
  have bound := rank_telescope n C.gates.length B cut I W arity outside gate sharedSmall
  simpa [W,cut,active,Circuit.size] using bound

end GirthFiveCore
