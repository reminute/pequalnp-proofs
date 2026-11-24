import PlaneFormulaRankKW
import Mathlib.Tactic

namespace GirthPotential

open Matrix PlaneKW

variable {X I J : Type} [Fintype I] [Fintype J]
variable (M : Matrix I J ℝ) (pos : I → X) (neg : J → X)

noncomputable def weight (f : X → Bool) : ℕ :=
  (block M (fun i => f (pos i)) (fun j => !(f (neg j)))).rank

theorem block_mono {r R : I → Bool} {c C : J → Bool}
    (hr : ∀ i, r i = true → R i = true) (hc : ∀ j, c j = true → C j = true) :
    (block M r c).rank ≤ (block M R C).rank := by
  classical
  let row : Matrix I I ℝ := diagonal (fun i => if r i then 1 else 0)
  let col : Matrix J J ℝ := diagonal (fun j => if c j then 1 else 0)
  have eq : row * block M R C * col = block M r c := by
    ext i j
    simp only [row, col, mul_diagonal, diagonal_mul]
    by_cases h : r i = true
    · by_cases h' : c j = true
      · simp [h,h',hr i h,hc j h',block]
      · simp [h',block]
    · simp [h,block]
  rw [← eq]
  exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

omit [Fintype I] in
theorem const_weight (b : Bool) : weight M pos neg (fun _ => b) = 0 := by
  have z : block M (fun _ => b) (fun _ => !b) = 0 := by
    ext i j
    cases b <;> simp [block]
  simp [weight,z]

theorem or_weight (f g : X → Bool) :
    weight M pos neg (fun x => f x || g x) ≤ weight M pos neg f + weight M pos neg g := by
  let c (j : J) := !(f (neg j) || g (neg j))
  let r₁ (i : I) := f (pos i)
  let r₂ (i : I) := !f (pos i) && g (pos i)
  have eq : block M (fun i => f (pos i) || g (pos i)) c =
      block M r₁ c + block M r₂ c := by
    ext i j
    cases h : f (pos i) <;> simp [r₁,r₂,block,Matrix.add_apply,h]
  change (block M _ c).rank ≤ _
  rw [eq]
  refine (PlaneKW.rank_sum_le _ _).trans (Nat.add_le_add ?_ ?_)
  · apply block_mono M (fun _ h => h)
    intro j h
    change !(f (neg j) || g (neg j)) = true at h
    cases h' : f (neg j) <;> simp_all
  · apply block_mono M
    · exact fun i h => (Bool.and_eq_true_iff.mp h).2
    · intro j h
      change !(f (neg j) || g (neg j)) = true at h
      cases h' : g (neg j) <;> simp_all

theorem and_weight (f g : X → Bool) :
    weight M pos neg (fun x => f x && g x) ≤ weight M pos neg f + weight M pos neg g := by
  let r (i : I) := f (pos i) && g (pos i)
  let c₁ (j : J) := !f (neg j)
  let c₂ (j : J) := f (neg j) && !g (neg j)
  have eq : block M r (fun j => !(f (neg j) && g (neg j))) =
      block M r c₁ + block M r c₂ := by
    ext i j
    cases h : f (neg j) <;> simp [c₁,c₂,block,Matrix.add_apply,h]
  change (block M r _).rank ≤ _
  rw [eq]
  refine (PlaneKW.rank_sum_le _ _).trans (Nat.add_le_add ?_ ?_)
  · exact block_mono M (fun i h => (Bool.and_eq_true_iff.mp h).1) (fun _ h => h)
  · exact block_mono M (fun i h => (Bool.and_eq_true_iff.mp h).2)
      (fun j h => (Bool.and_eq_true_iff.mp h).2)

end GirthPotential
