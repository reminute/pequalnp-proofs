import Mathlib
import PEqualNP.Defs

namespace Rect4123.LiftRow

open PEqualNP.MetaComplexity

abbrev Input (n : ℕ) := Fin n → Bool

def lifted {n : ℕ} (v : Fin n) (b : Bool) (x : Input n) :=
  if b then Function.update x v true else x

def Slots {k : ℕ} (sign : Fin k → Bool) (D : Finset (Fin k)) :=
  {p : Fin k × Bool // sign p.1 = true ∧ (p.2 = true → p.1 ∈ D)}

instance {k : ℕ} (sign : Fin k → Bool) (D : Finset (Fin k)) : Fintype (Slots sign D) :=
  inferInstanceAs (Fintype {_p : Fin k × Bool // _})

private theorem pack {n m : ℕ} {J : Type} [Fintype J] (f : Input n → Bool)
    (P Q : J → Input n → Prop) (label : J → ℕ)
    (row : ∀ j x, P j x → f x = true) (col : ∀ j y, Q j y → f y = false)
    (sound : ∀ j x y, P j x → Q j y →
      ∃ i : Fin n, label j = i.val ∧ x i = true ∧ y i ≠ true)
    (unique : ∀ x y, f x = true → f y = false → ∃! j, P j x ∧ Q j y)
    (bound : Fintype.card J ≤ m) :
    ∃ A B pos, IsLiteralPartition n f m A B pos (fun _ => true) := by
  classical
  let e := (Fintype.equivFin J).toEmbedding.trans (Fin.castLEEmb bound)
  let A (i : Fin m) (x : Input n) := decide (∃ j, e j = i ∧ P j x)
  let B (i : Fin m) (y : Input n) := decide (∃ j, e j = i ∧ Q j y)
  let out (i : Fin m) := if h : ∃ j, e j = i then label h.choose else 0
  refine ⟨A,B,out,?_,?_,?_,?_⟩
  · intro i x h
    obtain ⟨j,_,mem⟩ := of_decide_eq_true h
    exact row j x mem
  · intro i y h
    obtain ⟨j,_,mem⟩ := of_decide_eq_true h
    exact col j y mem
  · intro i x y hx hy
    obtain ⟨j,rfl,px⟩ := of_decide_eq_true hx
    obtain ⟨l,eq,py⟩ := of_decide_eq_true hy
    cases e.injective eq
    have hit : ∃ l, e l = e j := ⟨j,rfl⟩
    simpa only [out,dite_eq_left hit,e.injective hit.choose_spec] using sound j x y px py
  · intro x y hx hy
    obtain ⟨j,⟨p,q⟩,one⟩ := unique x y hx hy
    refine ⟨e j,⟨decide_eq_true ⟨j,rfl,p⟩,decide_eq_true ⟨j,rfl,q⟩⟩,?_⟩
    rintro i ⟨hi,ci⟩
    obtain ⟨l,rfl,pl⟩ := of_decide_eq_true hi
    obtain ⟨l',eq,ql⟩ := of_decide_eq_true ci
    cases e.injective eq
    exact congrArg e (one l ⟨pl,ql⟩)

/-- Lift the accepting row when the column is high at the only negated coordinate.
    A positive rectangle needs a second slot only if it cannot use its old row set. -/
theorem repair {n k m : ℕ} (v : Fin n) (f : Input n → Bool)
    (A B : Fin k → Input n → Bool) (pos : Fin k → ℕ) (sign : Fin k → Bool)
    (partition : IsLiteralPartition n f k A B pos sign)
    (raises : ∀ x, f x = true → f (Function.update x v true) = true)
    (negative : ∀ j, sign j = false → pos j = v.val)
    (D : Finset (Fin k))
    (stable : ∀ j, sign j = true → j ∉ D → ∀ x y, f x = true → B j y = true →
      y v = true → A j (Function.update x v true) = A j x)
    (budget : Fintype.card (Slots sign D) ≤ m) :
    ∃ A' B' pos', IsLiteralPartition n f m A' B' pos' (fun _ => true) := by
  classical
  obtain ⟨_,cols,labels,covers⟩ := partition
  let mode (j : Fin k) (y : Input n) := decide (j ∈ D) && y v
  let P (s : Slots sign D) (x : Input n) := f x = true ∧ A s.val.1 (lifted v s.val.2 x) = true
  let Q (s : Slots sign D) (y : Input n) := B s.val.1 y = true ∧ s.val.2 = mode s.val.1 y
  have translate (j : Fin k) (positive : sign j = true) (x y : Input n) (hx : f x = true)
      (byes : B j y = true) : A j (lifted v (mode j y) x) = A j (lifted v (y v) x) := by
    by_cases jd : j ∈ D
    · simp [mode,jd]
    · cases yv : y v with
      | false => simp [mode,jd,yv]
      | true => simpa [mode,jd,yv,lifted] using (stable j positive jd x y hx byes yv).symm
  have rel (s : Slots sign D) (x y) (hx : P s x) (hy : Q s y) :
      A s.val.1 (lifted v (y v) x) = true := by
    rw [←translate s.val.1 s.property.1 x y hx.1 hy.1,←hy.2]
    exact hx.2
  apply pack f P Q (fun s => pos s.val.1) (fun _ _ h => h.1) (fun s y h => cols _ _ h.1) _ _ budget
  · intro s x y hx hy
    obtain ⟨i,pi,on,off⟩ := labels _ _ _ (rel s x y hx hy) hy.1
    rw [s.property.1] at on off
    refine ⟨i,pi,?_,off⟩
    by_cases high : y v = true
    · have ne : i ≠ v := fun eq => off (eq ▸ high)
      simpa [lifted,high,Function.update_of_ne ne] using on
    · cases b : y v <;> simp_all [lifted]
  · intro x y fx fy
    have up : f (lifted v (y v) x) = true := by
      cases y v <;> simp [lifted,fx,raises x fx]
    obtain ⟨j,⟨hit,byes⟩,one⟩ := covers _ _ up fy
    have positive : sign j = true := by
      cases sgn : sign j with
      | true => rfl
      | false =>
        obtain ⟨i,pi,on,off⟩ := labels _ _ _ hit byes
        have eq := Fin.ext (pi.symm.trans (negative j sgn))
        subst i
        rw [sgn] at on off
        cases b : y v <;> simp_all [lifted]
    let s : Slots sign D := ⟨(j,mode j y),positive,by simpa [mode] using (fun h _ => h : j ∈ D → y v = true → j ∈ D)⟩
    refine ⟨s,⟨⟨fx,(translate j positive x y fx byes).trans hit⟩,by exact ⟨byes,rfl⟩⟩,?_⟩
    rintro t ⟨pt,qt⟩
    have same : t.val.1 = j := one _ ⟨rel t x y pt qt,qt.1⟩
    exact Subtype.ext (Prod.ext same (qt.2.trans (congrArg (fun i => mode i y) same)))

end Rect4123.LiftRow

#print axioms Rect4123.LiftRow.repair
