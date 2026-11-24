import GraphRepair

namespace Rect4123.SignBudget

open PEqualNP.MetaComplexity LiftRow GraphTransfer

/-- Count the positive slots once, and a second time only when their label
    is different from the unique negatively labelled coordinate. -/
theorem split_bound {n k m : ℕ} (v : Fin n) (f : Input n → Bool)
    (A B : Fin k → Input n → Bool) (pos : Fin k → ℕ) (sign : Fin k → Bool)
    (part : IsLiteralPartition n f k A B pos sign)
    (raises : ∀ x, f x = true → f (Function.update x v true) = true)
    (neg : ∀ j, sign j = false → pos j = v.val)
    (budget : (Finset.univ.filter (fun j => sign j = true)).card +
      (Finset.univ.filter (fun j => pos j ≠ v.val ∧ sign j = true)).card ≤ m) :
    ∃ U V p, IsLiteralPartition n f m U V p (fun _ => true) := by
  classical
  let D := Finset.univ.filter (fun j => pos j ≠ v.val)
  apply repair v f A B pos sign part raises neg D
  · intro j posj clean x y _ byes yv
    have same : pos j = v.val := by simpa [D] using clean
    have emptyRow (t : Input n) : A j t = false := by
      cases h : A j t with
      | false => rfl
      | true =>
        obtain ⟨i,pi,_,reject⟩ := part.2.2.1 j t y h byes
        have eq : i = v := Fin.ext (pi.symm.trans same)
        exact (reject (eq ▸ (yv.trans posj.symm))).elim
    rw [emptyRow,emptyRow]
  · rw [slot_count]
    simpa only [D,Finset.filter_filter] using budget

theorem graph_bound {n k m : ℕ} (G H : SimpleGraph (Fin n)) (z v : Fin n)
    (f : Input n → Bool) (girth : ∀ u (p : G.Walk u u), p.IsCycle → 7 ≤ p.length)
    (deleted : H = G.deleteEdges (G.incidenceSet z)) (spec : Spec H f)
    (A B : Fin k → Input n → Bool) (pos : Fin k → ℕ) (sign : Fin k → Bool)
    (part : IsLiteralPartition n f k A B pos sign)
    (neg : ∀ j, sign j = false → pos j = v.val)
    (budget : (Finset.univ.filter (fun j => sign j = true)).card +
      (Finset.univ.filter (fun j => pos j ≠ v.val ∧ sign j = true)).card ≤ m) :
    Rectangles H m := by
  obtain ⟨U,V,p,cert⟩ := split_bound v f A B pos sign part (raise_preserves H f spec v) neg budget
  exact of_positive G H z f girth deleted spec cert

end Rect4123.SignBudget

#print axioms Rect4123.SignBudget.graph_bound
