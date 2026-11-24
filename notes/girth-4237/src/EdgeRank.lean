import PlaneFormulaRankKW
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

-- The intersection matrix is from Jukna, Boolean Function Complexity, Theorem 7.2.
-- The right inverse here works over the reals: the two endpoint columns minus
-- the edge column give a coordinate vector.
namespace GirthRank

open Matrix Finset

variable {V : Type} [Fintype V] [DecidableEq V] (E : Finset (Finset V))

def columnSet : V ⊕ ↥E → Finset V
  | .inl v => {v}
  | .inr f => f.val

def overlap (e : ↥E) (y : V ⊕ ↥E) : ℝ :=
  if Disjoint e.val (columnSet E y) then 0 else 1

def mat : Matrix (↥E) (V ⊕ ↥E) ℝ := overlap E

omit [Fintype V] in
theorem endpoint_column (e : ↥E) (u : V) :
    mat E e (.inl u) = if u ∈ e.val then 1 else 0 := by
  simp only [mat, overlap, columnSet, Finset.disjoint_singleton_right]
  split_ifs <;> simp_all

theorem isolate (two : ∀ x ∈ E, x.card = 2) (f : ↥E) :
    ∃ x : (V ⊕ ↥E) → ℝ, (mat E).mulVec x = Pi.single f 1 := by
  classical
  obtain ⟨u,v,ne,pair⟩ := Finset.card_eq_two.mp (two f.val f.property)
  refine ⟨Pi.single (.inl u) 1 + Pi.single (.inl v) 1 - Pi.single (.inr f) 1,?_⟩
  ext e
  simp only [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_single, Pi.sub_apply,
    Pi.add_apply, MulOpposite.op_one, one_smul]
  change mat E e (.inl u) + mat E e (.inl v) - mat E e (.inr f) = _
  rw [endpoint_column,endpoint_column]
  have last : mat E e (.inr f) = if u ∈ e.val ∨ v ∈ e.val then 1 else 0 := by
    simp only [mat,overlap,columnSet,pair,Finset.disjoint_insert_right,Finset.disjoint_singleton_right]
    split_ifs <;> simp_all
  have eq_iff : e = f ↔ u ∈ e.val ∧ v ∈ e.val := by
    constructor
    · rintro rfl
      simp [pair]
    · rintro ⟨hu,hv⟩
      apply Subtype.ext
      have sub : f.val ⊆ e.val := by
        rw [pair]
        exact Finset.insert_subset hu (Finset.singleton_subset_iff.mpr hv)
      have card : e.val.card ≤ f.val.card := by rw [two _ e.property,two _ f.property]
      exact (Finset.eq_of_subset_of_card_le sub card).symm
  rw [last,Pi.single_apply]
  by_cases hu : u ∈ e.val <;> by_cases hv : v ∈ e.val <;>
    simp_all only [or_true, true_or, false_or, and_true, true_and,
      false_and, and_false, if_true, if_false] <;> grind

theorem rows_independent (two : ∀ x ∈ E, x.card = 2) : E.card ≤ (mat E).rank := by
  classical
  choose col hcol using isolate E two
  let R : Matrix (V ⊕ ↥E) (↥E) ℝ := fun y f => col f y
  have product : mat E * R = 1 := by
    ext e f
    change (mat E).mulVec (col f) e = _
    rw [hcol,Pi.single_apply, Matrix.one_apply]
  have bound := Matrix.rank_mul_le_left (mat E) R
  simpa only [product,Matrix.rank_one,Fintype.card_coe] using bound

end GirthRank
