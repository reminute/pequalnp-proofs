import RankGates

namespace GirthPartition

open PlaneKW GirthPotential Matrix

variable {X I J : Type} [Fintype I] [Fintype J]
variable (M : Matrix I J ℝ) (pos : I → X) (neg : J → X)

def rowOff (h : X → Bool) : Matrix I J ℝ :=
  block M (fun i => !(h (pos i))) (fun _ => true)

def bothOn (h : X → Bool) : Matrix I J ℝ :=
  block M (fun i => h (pos i)) (fun j => h (neg j))

def crossed (h : X → Bool) : Matrix I J ℝ :=
  block M (fun i => h (pos i)) (fun j => !(h (neg j)))

omit [Fintype I] [Fintype J] in
theorem block_comm (r R : I → Bool) (c C : J → Bool) :
    block (block M r c) R C = block (block M R C) r c := by
  ext i j
  by_cases a : r i && c j <;> by_cases b : R i && C j <;> simp [block,a,b]

theorem restricted_le (r : I → Bool) (c : J → Bool) :
    (block M r c).rank ≤ M.rank := by
  have e : block M (fun _ => true) (fun _ => true) = M := by ext; rfl
  simpa only [e] using
    (block_mono M (r := r) (c := c) (R := fun _ => true) (C := fun _ => true)
      (fun _ _ => rfl) (fun _ _ => rfl))

theorem weight_le (r : I → Bool) (c : J → Bool) (f : X → Bool) :
    weight (block M r c) pos neg f ≤ weight M pos neg f := by
  unfold weight
  rw [block_comm]
  exact restricted_le _ _ _

omit [Fintype I] in
theorem rowOff_zero (h : X → Bool) : weight (rowOff M pos h) pos neg h = 0 := by
  have z : crossed (rowOff M pos h) pos neg h = 0 := by
    ext i j
    cases e : h (pos i) <;> simp [crossed, rowOff, block, e]
  change (crossed (rowOff M pos h) pos neg h).rank = 0
  simp [z]

omit [Fintype I] in
theorem bothOn_zero (h : X → Bool) : weight (bothOn M pos neg h) pos neg h = 0 := by
  have z : crossed (bothOn M pos neg h) pos neg h = 0 := by
    ext i j
    cases e : h (neg j) <;> simp [crossed, bothOn, block, e]
  change (crossed (bothOn M pos neg h) pos neg h).rank = 0
  simp [z]

/-- Partition into a pair of subproblems where h has zero weight, plus its crossing block. -/
theorem split_weight (f h : X → Bool) :
    weight M pos neg f ≤ weight (rowOff M pos h) pos neg f +
      weight (bothOn M pos neg h) pos neg f + weight M pos neg h := by
  let r (i : I) := f (pos i)
  let c (j : J) := !(f (neg j))
  have eq : block M r c = block (rowOff M pos h) r c +
      block (bothOn M pos neg h) r c + block (crossed M pos neg h) r c := by
    ext i j
    cases a : h (pos i) <;> cases b : h (neg j) <;>
      by_cases active : r i && c j <;> simp [Matrix.add_apply, block, rowOff, bothOn, crossed, a,b,active]
  change (block M r c).rank ≤ _
  rw [eq]
  exact (rank_sum_le _ _).trans (Nat.add_le_add (rank_sum_le _ _) (restricted_le _ _ _))

end GirthPartition
