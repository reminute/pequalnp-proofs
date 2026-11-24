import LiftRow

namespace Rect4123.LiftRow

theorem slot_count {k : ℕ} (sign : Fin k → Bool) (D : Finset (Fin k)) :
    Fintype.card (Slots sign D) =
      (Finset.univ.filter (fun j => sign j = true)).card +
      (D.filter (fun j => sign j = true)).card := by
  classical
  let P := Finset.univ.filter (fun j => sign j = true)
  let T := D.filter (fun j => sign j = true)
  let e : Slots sign D ≃ (↥P ⊕ ↥T) := {
    toFun := fun s => if h : s.val.2 = true then
      .inr ⟨s.val.1,Finset.mem_filter.mpr ⟨s.property.2 h,s.property.1⟩⟩
      else .inl ⟨s.val.1,Finset.mem_filter.mpr ⟨Finset.mem_univ _,s.property.1⟩⟩
    invFun := fun s => match s with
      | .inl j => ⟨(j.val,false),(Finset.mem_filter.mp j.property).2,by simp⟩
      | .inr j => ⟨(j.val,true),(Finset.mem_filter.mp j.property).2,fun _ => (Finset.mem_filter.mp j.property).1⟩
    left_inv := by
      rintro ⟨⟨j,b⟩,prop⟩
      cases b <;> simp <;> rfl
    right_inv := by
      rintro (j|j) <;> simp }
  change Fintype.card (Slots sign D) = P.card + T.card
  simpa only [Fintype.card_sum,Fintype.card_coe] using Fintype.card_congr e

theorem same_budget {k : ℕ} (sign : Fin k → Bool) (D : Finset (Fin k))
    (spare : (D.filter (fun j => sign j = true)).card ≤
      (Finset.univ.filter (fun j => sign j = false)).card) :
    Fintype.card (Slots sign D) ≤ k := by
  rw [slot_count]
  have total := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
    (p := fun j => sign j = true)
  simpa using (Nat.add_le_add_left spare (Finset.univ.filter (fun j => sign j = true)).card).trans_eq
    (by simpa using total)

end Rect4123.LiftRow

#print axioms Rect4123.LiftRow.slot_count
#print axioms Rect4123.LiftRow.same_budget
