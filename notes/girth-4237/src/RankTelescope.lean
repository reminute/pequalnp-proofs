import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic

namespace GirthFiveCore

open Finset

/-- The output contributes one read. Multiple occurrences of one wire in a
    gate's input list are distinct reads. -/
def readCount {s : ℕ} (inputs : Fin s → List ℕ) (out w : ℕ) : ℕ :=
  (if out = w then 1 else 0) + ∑ i, (inputs i).count w

/-- Every extra read of a gate pays only its weight above the input budget. -/
theorem rank_with_extra_reads (n s B out : ℕ) (inputs : Fin s → List ℕ) (weight : ℕ → ℕ)
    (arity : ∀ i, (inputs i).length ≤ 2)
    (outside : ∀ w, w < n ∨ n+s ≤ w → weight w ≤ B)
    (gateBound : ∀ i : Fin s, weight (n+i.val) ≤ ((inputs i).map weight).sum) :
    weight out ≤ B*(s+1) +
      ∑ i : Fin s, (readCount inputs out (n+i.val)-1) * (weight (n+i.val)-B) := by
  classical
  let excess (i : Fin s) := weight (n+i.val) - B
  let indicator (w : ℕ) (i : Fin s) : ℕ := if w = n+i.val then 1 else 0
  have one (w : ℕ) : weight w ≤ B + ∑ i, indicator w i * excess i := by
    by_cases ext : w < n ∨ n+s ≤ w
    · exact (outside w ext).trans (Nat.le_add_right ..)
    · let i : Fin s := ⟨w-n,by omega⟩
      have heq : w = n+i.val := by dsimp [i]; omega
      have lower : indicator w i * excess i ≤ ∑ j, indicator w j * excess j :=
        single_le_sum (fun j _ => Nat.zero_le (indicator w j * excess j)) (mem_univ i)
      have seen : indicator w i = 1 := by simp [indicator,heq]
      rw [seen,one_mul] at lower
      have hw : weight w ≤ B+excess i := by dsimp [excess]; rw [← heq]; omega
      exact hw.trans (Nat.add_le_add_left lower B)
  have many (ws : List ℕ) :
      (ws.map weight).sum ≤ ws.length*B + ∑ j : Fin s, ws.count (n+j.val)*excess j := by
    induction ws with
    | nil => simp
    | cons x xs ih =>
      have both := Nat.add_le_add (one x) ih
      have joined :
          (∑ j, indicator x j * excess j) + (∑ j : Fin s, xs.count (n+j.val)*excess j) =
          ∑ j : Fin s, (x::xs).count (n+j.val)*excess j := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro j _
        by_cases eq : x = n+j.val
        · simp [indicator,eq,Nat.add_mul,Nat.add_comm]
        · simp [indicator,eq,List.count_cons_of_ne]
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
      omega
  have atGate (i : Fin s) : excess i ≤ B + ∑ j : Fin s, (inputs i).count (n+j.val) * excess j := by
    have a := gateBound i
    have b := many (inputs i)
    have c := Nat.mul_le_mul_right B (arity i)
    change weight (n+i.val) - B ≤ B + ∑ j : Fin s, (inputs i).count (n+j.val)*excess j
    omega
  have spent :
      (∑ j, indicator out j * excess j) + (∑ i, ∑ j : Fin s, (inputs i).count (n+j.val)*excess j)
        ≤ (∑ j, excess j) + ∑ j, (readCount inputs out (n+j.val)-1) * excess j := by
    calc
      _ = ∑ j : Fin s, readCount inputs out (n+j.val) * excess j := by
        simp only [readCount,indicator,Nat.add_mul,Finset.sum_mul,Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun i j : Fin s => (inputs i).count (n+j.val)*excess j)]
      _ ≤ _ := by
        rw [← sum_add_distrib]
        apply sum_le_sum
        intro i _
        cases readCount inputs out (n+i.val) <;> simp [Nat.succ_mul, Nat.add_comm]
  have summed := sum_le_sum (s := (univ : Finset (Fin s))) (fun i _ => atGate i)
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at summed
  change (∑ i, excess i) ≤ s*B + ∑ i, ∑ j : Fin s, (inputs i).count (n+j.val)*excess j at summed
  have final := one out
  change weight out ≤ B*(s+1) + ∑ j, (readCount inputs out (n+j.val)-1) * excess j
  rw [Nat.mul_succ,Nat.mul_comm B s]
  omega

/-- Bounding the weight of every shared gate suffices for a linear output bound. -/
theorem rank_telescope (n s B out : ℕ) (inputs : Fin s → List ℕ) (weight : ℕ → ℕ)
    (arity : ∀ i, (inputs i).length ≤ 2)
    (outside : ∀ w, w < n ∨ n+s ≤ w → weight w ≤ B)
    (gateBound : ∀ i : Fin s, weight (n+i.val) ≤ ((inputs i).map weight).sum)
    (shared : ∀ i : Fin s, 1 < readCount inputs out (n+i.val) → weight (n+i.val) ≤ B) :
    weight out ≤ B*(s+1) := by
  have zero (i : Fin s) :
      (readCount inputs out (n+i.val)-1) * (weight (n+i.val)-B) = 0 := by
    by_cases h : 1 < readCount inputs out (n+i.val)
    · simp [Nat.sub_eq_zero_of_le (shared i h)]
    · simp [Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h)]
  simpa only [zero, Finset.sum_const_zero, Nat.add_zero] using
    rank_with_extra_reads n s B out inputs weight arity outside gateBound

end GirthFiveCore
