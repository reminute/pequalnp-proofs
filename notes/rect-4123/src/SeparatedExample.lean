import GraphTransfer
import ColumnMasks

namespace Rect4123.SeparatedExample

abbrev V := Fin 6
abbrev Input := V → Bool

/-- Three disjoint edges with endpoints (0,1), (2,3), and (4,5). -/
def H : SimpleGraph V where
  Adj a b := a.val / 2 = b.val / 2 ∧ a ≠ b
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

instance : DecidableRel H.Adj := fun a b =>
  inferInstanceAs (Decidable (a.val / 2 = b.val / 2 ∧ a ≠ b))

def f (x : Input) := (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)
def bits (m : Nat) (v : V) := m.testBit v.val
abbrev blocked := ColumnMasks.blocked H

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem spec : GraphTransfer.Spec H f := by
  unfold GraphTransfer.Spec
  decide +kernel

/-- Marginally both signs occur among graph samples. No one column realizes both. -/
theorem columns :
    blocked 1 1 0 ∧ blocked 3 3 2 ∧
      ∀ c d : V, c = d ∨ H.Adj c d → ¬ (blocked c d 0 ∧ blocked c d 2) := by
  unfold blocked ColumnMasks.blocked
  decide +kernel

private theorem component {u w : V} (p : H.Walk u w) : u.val / 2 = w.val / 2 := by
  induction p with
  | nil => rfl
  | cons edge _ ih => exact edge.1.trans ih

theorem separated : ColumnMasks.Separated H {0,2} := by
  intro u hu w hw neq both
  obtain ⟨p,_⟩ := both
  have unique : ∀ u ∈ ({0,2} : Finset V), ∀ w ∈ ({0,2} : Finset V),
      u.val / 2 = w.val / 2 → u = w := by decide
  exact neq (unique u hu w hw (component p))

/-- Two essential coordinates both separate the very same rejecting assignment
    from the same accepting assignment with the negative polarity. -/
theorem full_inputs :
    f (bits 48) = true ∧ f (bits 5) = false ∧
    bits 48 0 = false ∧ bits 5 0 = true ∧ bits 48 2 = false ∧ bits 5 2 = true ∧
    f (bits 2) = false ∧ f (Function.update (bits 2) 0 true) = true ∧
    f (bits 8) = false ∧ f (Function.update (bits 8) 2 true) = true := by decide

private abbrev hit (x y : Input) (i : V) := x i = false ∧ y i = true

private noncomputable def label (x y : Input) : V := by
  classical
  exact if hit x y 0 then 0 else if hit x y 2 then 2 else
    if h : ∃ i : V, x i = true ∧ y i = false then h.choose else 0

private def polarity (x y : Input) := !(decide (hit x y 0 ∨ hit x y 2))

private theorem label_zero {x y : Input} (h : hit x y 0) : label x y = 0 := by
  rw [label, ite_eq_left h]

private theorem label_two {x y : Input} (h : ¬hit x y 0) (h' : hit x y 2) : label x y = 2 := by
  rw [label, ite_eq_right h, ite_eq_left h']

private theorem label_ok (x y : Input) (on : f x = true) (off : f y = false) :
    x (label x y) = polarity x y ∧ y (label x y) ≠ polarity x y := by
  classical
  by_cases a : hit x y 0
  · rw [label_zero a]
    simp [polarity,a]
  by_cases b : hit x y 2
  · rw [label_two a b]
    simp [polarity,b]
  have differs : ∃ i : V, x i = true ∧ y i = false := by
    obtain ⟨u,v,uv,xu,xv⟩ := (spec _).mp on
    by_cases yu : y u = false
    · exact ⟨u,xu,yu⟩
    by_cases yv : y v = false
    · exact ⟨v,xv,yv⟩
    have yes := (spec _).mpr ⟨u,v,uv,Bool.eq_true_of_not_eq_false yu,Bool.eq_true_of_not_eq_false yv⟩
    exact False.elim (Bool.noConfusion (off.symm.trans yes))
  simp [label,polarity,a,b,dite_eq_left differs,differs.choose_spec.1,differs.choose_spec.2]

/-- Both designated negative labels occur in nonempty rectangles of a real signed
    partition, even on the same rejecting column. All other labels are positive. -/
theorem signed_partition :
    ∃ (k : Nat) (A B : Fin k → Input → Bool) (p : Fin k → Nat) (s : Fin k → Bool),
      PEqualNP.MetaComplexity.IsLiteralPartition 6 f k A B p s ∧
      (∀ j, s j = false → p j = 0 ∨ p j = 2) ∧
      (∃ j, p j = 0 ∧ s j = false ∧ A j (bits 12) = true ∧ B j (bits 5) = true) ∧
      (∃ j, p j = 2 ∧ s j = false ∧ A j (bits 3) = true ∧ B j (bits 5) = true) := by
  classical
  let e := Fintype.equivFin (Input × Input)
  let A (j : Fin _) (x : Input) := decide (x = (e.symm j).1 ∧ f x = true)
  let B (j : Fin _) (y : Input) := decide (y = (e.symm j).2 ∧ f y = false)
  let p (j : Fin _) := (label (e.symm j).1 (e.symm j).2).val
  let s (j : Fin _) := polarity (e.symm j).1 (e.symm j).2
  refine ⟨_,A,B,p,s,⟨?_,?_,?_,?_⟩,?_,?_,?_⟩
  · intro j x h; exact (of_decide_eq_true h).2
  · intro j y h; exact (of_decide_eq_true h).2
  · intro j x y hx hy
    obtain ⟨rfl,on⟩ := of_decide_eq_true hx
    obtain ⟨rfl,off⟩ := of_decide_eq_true hy
    exact ⟨_,rfl,label_ok _ _ on off⟩
  · intro x y on off
    refine ⟨e (x,y),⟨by simp [A,on],by simp [B,off]⟩,?_⟩
    rintro j ⟨hx,hy⟩
    apply e.symm.injective
    rw [e.symm_apply_apply]
    exact Prod.ext (of_decide_eq_true hx).1.symm (of_decide_eq_true hy).1.symm
  · intro j low
    by_cases h : hit (e.symm j).1 (e.symm j).2 0
    · exact Or.inl (by simp [p,label_zero h])
    by_cases h' : hit (e.symm j).1 (e.symm j).2 2
    · exact Or.inr (by simp [p,label_two h h'])
    · simp [s,polarity,h,h'] at low
  · refine ⟨e (bits 12,bits 5),?_⟩
    simp only [p,s,A,B,e.symm_apply_apply]
    have h : hit (bits 12) (bits 5) 0 := by decide
    simp [label_zero h,polarity,h,show f (bits 12) = true by decide,show f (bits 5) = false by decide]
  · refine ⟨e (bits 3,bits 5),?_⟩
    simp only [p,s,A,B,e.symm_apply_apply]
    have h : ¬hit (bits 3) (bits 5) 0 := by decide
    have h' : hit (bits 3) (bits 5) 2 := by decide
    simp [label_two h h',polarity,h',show f (bits 3) = true by decide,show f (bits 5) = false by decide]

end Rect4123.SeparatedExample

#print axioms Rect4123.SeparatedExample.spec
#print axioms Rect4123.SeparatedExample.columns
#print axioms Rect4123.SeparatedExample.separated
#print axioms Rect4123.SeparatedExample.full_inputs
#print axioms Rect4123.SeparatedExample.signed_partition
