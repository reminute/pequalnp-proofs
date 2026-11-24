import GraphTransfer
import LowerColumn

namespace Rect4123.GraphRepair

open PEqualNP.MetaComplexity GraphTransfer LiftRow

private theorem lowers {n : ℕ} (H : SimpleGraph (Fin n)) (f : Input n → Bool)
    (spec : Spec H f) (v : Fin n) (y : Input n) (off : f y = false) :
    f (Function.update y v false) = false := by
  by_contra! high
  have on : f (Function.update y v false) = true := by
    cases h : f (Function.update y v false) <;> simp_all
  obtain ⟨a,b,ab,ha,hb⟩ := (spec _).mp on
  have original (i : Fin n) (h : Function.update y v false i = true) : y i = true := by
    by_cases eq : i=v <;> simp_all [Function.update_of_ne]
  exact Bool.noConfusion (off.symm.trans ((spec y).mpr ⟨a,b,ab,original _ ha,original _ hb⟩))

/-- A signed partition with one negatively labelled coordinate suffices when
    either admissible repair fits in the negative slots that are freed. -/
theorem same_size {n k : ℕ} (G H : SimpleGraph (Fin n)) (z v : Fin n)
    (f : Input n → Bool) (girth : ∀ u (p : G.Walk u u), p.IsCycle → 7 ≤ p.length)
    (deleted : H = G.deleteEdges (G.incidenceSet z)) (spec : Spec H f)
    (A B : Fin k → Input n → Bool) (pos : Fin k → ℕ) (sign : Fin k → Bool)
    (part : IsLiteralPartition n f k A B pos sign)
    (neg : ∀ j, sign j = false → pos j = v.val) (D : Finset (Fin k))
    (spare : (D.filter (fun j => sign j = true)).card ≤
      (Finset.univ.filter (fun j => sign j = false)).card)
    (stable :
      (∀ j, sign j = true → j ∉ D → ∀ x y, f x = true → B j y = true →
        y v = true → A j (Function.update x v true) = A j x) ∨
      (∀ j, sign j = true → j ∉ D → ∀ x y, f y = false → A j x = true →
        x v = false → B j (Function.update y v false) = B j y)) :
    Rectangles H k := by
  have bound := same_budget sign D spare
  suffices h : ∃ U V p, IsLiteralPartition n f k U V p (fun _ => true) by
    obtain ⟨U,V,p,good⟩ := h
    exact of_positive G H z f girth deleted spec good
  rcases stable with rows | cols
  · exact repair v f A B pos sign part (raise_preserves H f spec v) neg D rows bound
  · exact lower_repair v f A B pos sign part (lowers H f spec v) neg D cols bound

end Rect4123.GraphRepair

#print axioms Rect4123.GraphRepair.same_size
