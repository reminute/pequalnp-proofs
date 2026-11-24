import EdgeRank

namespace GirthRank

variable {V : Type} [Fintype V] [DecidableEq V] (E : Finset (Finset V))
variable (A : V → V → Prop) [DecidableRel A]

def positive (e : ↥E) (v : V) : Bool := decide (v ∈ e.val)

def negative (y : V ⊕ ↥E) (v : V) : Bool :=
  decide (v ∉ columnSet E y ∧ ∃ w ∈ columnSet E y, A v w)

theorem leaf_rank (adj : ∀ e ∈ E, ∀ v ∈ e, ∀ w ∈ e, v ≠ w → A v w)
    (v : V) (r : ↥E → Bool) (c : V ⊕ ↥E → Bool)
    (pos : ∀ e, r e = true → positive E e v = true)
    (neg : ∀ y, c y = true → negative E A y v = false) :
    (PlaneKW.block (mat E) r c).rank ≤ 1 := by
  classical
  let left (e : ↥E) : ℝ := if r e then 1 else 0
  let right (y : V ⊕ ↥E) : ℝ := if c y = true ∧ v ∈ columnSet E y then 1 else 0
  have factor : PlaneKW.block (mat E) r c = Matrix.vecMulVec left right := by
    ext e y
    by_cases hr : r e = true
    · by_cases hc : c y = true
      · have hv : v ∈ e.val := of_decide_eq_true (pos e hr)
        by_cases inside : v ∈ columnSet E y
        · have meet := Finset.not_disjoint_iff.mpr ⟨v,hv,inside⟩
          simp [PlaneKW.block,Matrix.vecMulVec,left,right,mat,overlap,hr,hc,inside,meet]
        · have off : Disjoint e.val (columnSet E y) := by
            by_contra h
            obtain ⟨w,hwe,hwy⟩ := Finset.not_disjoint_iff.mp h
            have diff : v ≠ w := fun eq => inside (eq ▸ hwy)
            have bad : negative E A y v = true :=
              decide_eq_true ⟨inside,w,hwy,adj e.val e.property v hv w hwe diff⟩
            rw [neg y hc] at bad
            exact Bool.noConfusion bad
          simp [PlaneKW.block,Matrix.vecMulVec,left,right,mat,overlap,hr,hc,inside,off]
      · simp [PlaneKW.block,Matrix.vecMulVec,left,right,hr,hc]
    · simp [PlaneKW.block,Matrix.vecMulVec,left,right,hr]
  rw [factor]
  exact Matrix.rank_vecMulVec_le _ _

theorem formula_lower (two : ∀ e ∈ E, e.card = 2)
    (adj : ∀ e ∈ E, ∀ v ∈ e, ∀ w ∈ e, v ≠ w → A v w)
    (t : PlaneFormula V) (accept : ∀ e, t.eval (positive E e) = true)
    (reject : ∀ y, t.eval (negative E A y) = false) : E.card ≤ t.leaves.length :=
  (rows_independent E two).trans (PlaneKW.formula_rank (mat E) _ _ (leaf_rank E A adj) t accept reject)

end GirthRank
