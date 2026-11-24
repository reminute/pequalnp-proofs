import PlaneFormulaCore
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Basic.Real.Basic

open Matrix

namespace PlaneKW

theorem rank_sum_le {ι κ : Type} [Fintype ι] [Fintype κ] (A B : Matrix ι κ ℝ) :
    (A+B).rank ≤ A.rank+B.rank := by
  change Module.finrank ℝ (LinearMap.range (A+B).mulVecLin) ≤ _
  refine (Submodule.finrank_mono ?_).trans
    (Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range A.mulVecLin)
      (LinearMap.range B.mulVecLin))
  rintro _ ⟨x,rfl⟩
  rw [Matrix.mulVecLin_add,LinearMap.add_apply]
  exact Submodule.add_mem_sup ⟨x,rfl⟩ ⟨x,rfl⟩

def block {ι κ : Type} (M : Matrix ι κ ℝ) (r : ι → Bool) (c : κ → Bool) :
    Matrix ι κ ℝ := fun i j => if r i && c j then M i j else 0

theorem formula_rank {α ι κ : Type} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) (pos : ι → α → Bool) (neg : κ → α → Bool)
    (leafBound : ∀ (a : α) (r : ι → Bool) (c : κ → Bool),
      (∀ i, r i = true → pos i a = true) →
      (∀ j, c j = true → neg j a = false) → (block M r c).rank ≤ 1)
    (t : PlaneFormula α) (accept : ∀ i, t.eval (pos i) = true)
    (reject : ∀ j, t.eval (neg j) = false) : M.rank ≤ t.leaves.length := by
  have part (u : PlaneFormula α) (r : ι → Bool) (c : κ → Bool)
      (right : ∀ i, r i = true → u.eval (pos i) = true)
      (left : ∀ j, c j = true → u.eval (neg j) = false) :
      (block M r c).rank ≤ u.leaves.length := by
    induction u generalizing r c with
    | bot =>
      have zero : block M r c = 0 := by
        ext i j
        have off : r i = false := by
          cases e : r i
          · rfl
          · have impossible : false = true := right i e
            contradiction
        simp [block,off]
      simp [zero]
    | leaf a => exact leafBound a r c right left
    | or a b ha hb =>
      let z (i : ι) := a.eval (pos i)
      let r₁ (i : ι) := r i && z i
      let r₂ (i : ι) := r i && !z i
      have splitM : block M r c = block M r₁ c + block M r₂ c := by
        ext i j
        by_cases e : z i = true <;> simp [block,r₁,r₂,e,Matrix.add_apply]
      have h₁ := ha r₁ c (fun i h => (Bool.and_eq_true_iff.mp h).2)
        (fun j h => (Bool.or_eq_false_iff.mp (left j h)).1)
      have h₂ := hb r₂ c (fun i h => by
        obtain ⟨hr,hz⟩ := Bool.and_eq_true_iff.mp h
        rcases Bool.or_eq_true_iff.mp (right i hr) with yes | yes
        · change (!z i) = true at hz
          have e : z i = true := yes
          simp [e] at hz
        · exact yes) (fun j h => (Bool.or_eq_false_iff.mp (left j h)).2)
      rw [splitM]
      exact (rank_sum_le _ _).trans (by simpa [PlaneFormula.leaves] using Nat.add_le_add h₁ h₂)
    | and a b ha hb =>
      let z (j : κ) := a.eval (neg j)
      let c₁ (j : κ) := c j && !z j
      let c₂ (j : κ) := c j && z j
      have splitM : block M r c = block M r c₁ + block M r c₂ := by
        ext i j
        by_cases e : z j = true <;> simp [block,c₁,c₂,e,Matrix.add_apply]
      have h₁ := ha r c₁ (fun i h => (Bool.and_eq_true_iff.mp (right i h)).1)
        (fun j h => by
          have e : (!z j) = true := (Bool.and_eq_true_iff.mp h).2
          simpa [z] using e)
      have h₂ := hb r c₂ (fun i h => (Bool.and_eq_true_iff.mp (right i h)).2)
        (fun j h => by
          obtain ⟨hc,hz⟩ := Bool.and_eq_true_iff.mp h
          have v := left j hc
          change (z j && b.eval (neg j)) = false at v
          simpa [hz] using v)
      rw [splitM]
      exact (rank_sum_le _ _).trans (by simpa [PlaneFormula.leaves] using Nat.add_le_add h₁ h₂)
  have h := part t (fun _ => true) (fun _ => true) (fun i _ => accept i) (fun j _ => reject j)
  have eqn : block M (fun _ => true) (fun _ => true) = M := by ext; rfl
  simpa only [eqn] using h

end PlaneKW
