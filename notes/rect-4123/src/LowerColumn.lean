import SlotCount

namespace Rect4123.LiftRow

open PEqualNP.MetaComplexity

def invert {n : ℕ} (x : Input n) : Input n := fun i => !(x i)

private theorem invol {n : ℕ} (x : Input n) : invert (invert x) = x := by
  funext i
  simp [invert]

private theorem swapped {n k : ℕ} {f : Input n → Bool}
    {A B : Fin k → Input n → Bool} {pos : Fin k → ℕ} {sign : Fin k → Bool}
    (h : IsLiteralPartition n f k A B pos sign) :
    IsLiteralPartition n (fun x => !(f (invert x))) k
      (fun j x => B j (invert x)) (fun j x => A j (invert x)) pos sign := by
  obtain ⟨rows,cols,sep,one⟩ := h
  refine ⟨fun j x yes => by simp [cols j _ yes],fun j y yes => by simp [rows j _ yes],?_,?_⟩
  · intro j x y px qy
    obtain ⟨i,atI,l,r⟩ := sep j _ _ qy px
    refine ⟨i,atI,?_,?_⟩ <;> cases xx : x i <;> cases yy : y i <;>
      cases ss : sign j <;> simp_all [invert]
  · intro x y fx fy
    obtain ⟨j,⟨py,px⟩,only⟩ := one (invert y) (invert x) (by simpa using fy) (by simpa using fx)
    exact ⟨j,⟨px,py⟩,fun k hk => only k ⟨hk.2,hk.1⟩⟩

private theorem invert_up {n : ℕ} (x : Input n) (v : Fin n) :
    invert (Function.update x v true) = Function.update (invert x) v false := by
  funext i
  by_cases h : i=v <;> simp [invert,h,Function.update_of_ne]

/-- The dual cost counts positive rectangles whose *column* sets need splitting. -/
theorem lower_repair {n k m : ℕ} (v : Fin n) (f : Input n → Bool)
    (A B : Fin k → Input n → Bool) (pos : Fin k → ℕ) (sign : Fin k → Bool)
    (partition : IsLiteralPartition n f k A B pos sign)
    (lowers : ∀ y, f y = false → f (Function.update y v false) = false)
    (negative : ∀ j, sign j = false → pos j = v.val)
    (D : Finset (Fin k))
    (stable : ∀ j, sign j = true → j ∉ D → ∀ x y, f y = false → A j x = true →
      x v = false → B j (Function.update y v false) = B j y)
    (budget : Fintype.card (Slots sign D) ≤ m) :
    ∃ A' B' pos', IsLiteralPartition n f m A' B' pos' (fun _ => true) := by
  obtain ⟨U,V,p,good⟩ := repair v _ _ _ _ _ (swapped partition)
    (by
      intro x hx
      have old : f (invert x) = false := by simpa using hx
      simp [invert_up,lowers _ old]) negative D (by
      intro j hj out x y hx hy yy
      rw [invert_up]
      exact stable j hj out (invert y) (invert x) (by simpa using hx) hy (by simp [invert,yy])) budget
  refine ⟨fun j x => V j (invert x),fun j y => U j (invert y),p,?_⟩
  simpa only [invol,Bool.not_not] using swapped good

end Rect4123.LiftRow

#print axioms Rect4123.LiftRow.lower_repair
