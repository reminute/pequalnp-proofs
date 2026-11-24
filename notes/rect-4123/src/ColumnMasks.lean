import Cell

namespace Rect4123.ColumnMasks

open SimpleGraph

variable {n : ℕ} {H : SimpleGraph (Fin n)} {c d u w : Fin n}

def blocked (H : SimpleGraph (Fin n)) (c d u : Fin n) : Prop :=
  (H.Adj c u ∨ H.Adj d u) ∧ u≠c ∧ u≠d

abbrev Separated (H : SimpleGraph (Fin n)) (D : Finset (Fin n)) : Prop :=
  ∀ u ∈ D, ∀ w ∈ D, u ≠ w → ¬ ∃ p : H.Walk u w, p.length ≤ 3

noncomputable def masked (H : SimpleGraph (Fin n)) (D : Finset (Fin n)) (c d : Fin n) :
    Finset (Fin n) := by
  classical
  exact D.filter (blocked H c d)

@[simp] theorem mem_masked {D : Finset (Fin n)} :
    u ∈ masked H D c d ↔ u ∈ D ∧ blocked H c d u := by
  classical
  simp [masked]

/-- Use two edges if both blocked vertices meet the same endpoint. Otherwise the
column's own edge supplies a third edge joining those endpoints. -/
theorem short_walk (shape : c=d ∨ H.Adj c d) (hu : blocked H c d u) (hw : blocked H c d w) :
    ∃ p : H.Walk u w, p.length ≤ 3 := by
  have via {z : Fin n} (zu : H.Adj z u) (zw : H.Adj z w) :
      ∃ p : H.Walk u w, p.length ≤ 3 :=
    ⟨.cons zu.symm (.cons zw .nil), by change 2 ≤ 3; decide⟩
  rcases shape with rfl | cd
  · exact via (hu.1.elim id id) (hw.1.elim id id)
  · rcases hu.1 with cu | du <;> rcases hw.1 with cw | dw
    · exact via cu cw
    · exact ⟨.cons cu.symm (.cons cd (.cons dw .nil)), le_rfl⟩
    · exact ⟨.cons du.symm (.cons cd.symm (.cons cw .nil)), le_rfl⟩
    · exact via du dw

theorem card_mask_le_one {D : Finset (Fin n)} (sep : Separated H D) (shape : c=d ∨ H.Adj c d) :
    (masked H D c d).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu w hw
  obtain ⟨uD,bu⟩ := mem_masked.mp hu
  obtain ⟨wD,bw⟩ := mem_masked.mp hw
  by_contra different
  exact sep u uD w wD different (short_walk shape bu bw)

theorem unique_mark {D : Finset (Fin n)} (sep : Separated H D) (shape : c=d ∨ H.Adj c d)
    (nonempty : (masked H D c d).Nonempty) : ∃! u, u∈D ∧ blocked H c d u := by
  obtain ⟨u,hu⟩ := nonempty
  refine ⟨u,mem_masked.mp hu,?_⟩
  intro w hw
  exact (Finset.card_le_one.mp (card_mask_le_one sep shape)) w (mem_masked.mpr hw) u hu

end Rect4123.ColumnMasks

#print axioms Rect4123.ColumnMasks.short_walk
#print axioms Rect4123.ColumnMasks.card_mask_le_one
#print axioms Rect4123.ColumnMasks.unique_mark
