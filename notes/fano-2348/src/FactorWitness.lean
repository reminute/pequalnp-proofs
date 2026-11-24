import PEqualNP.Defs
import Mathlib.Tactic

namespace FanoFactor

abbrev Input := Fin 14 → Bool

def incidence (x : Input) : Bool :=
  decide (∃ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) ∧
    x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)

def unitAt (a : Fin 14) : Input := fun i => decide (i = a)

def pairAt (a b : Fin 14) : Input := fun i => decide (i = a ∨ i = b)

def Increasing (f : Input → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

-- Two fixed vertices have neighbors in at most six diagonal incidence pairs.
set_option maxHeartbeats 1000000 in
theorem spare_pair : ∀ i j : Fin 14, ∃ t : Fin 7,
    incidence (pairAt (Fin.castAdd 7 t) i) = false ∧
    incidence (pairAt (Fin.natAdd 7 t) i) = false ∧
    incidence (pairAt (Fin.castAdd 7 t) j) = false ∧
    incidence (pairAt (Fin.natAdd 7 t) j) = false := by decide +kernel

private theorem unit_left (a b : Fin 14) :
    ∀ i, unitAt a i = true → pairAt a b i = true := by simp [unitAt, pairAt]

private theorem unit_right (a b : Fin 14) :
    ∀ i, unitAt b i = true → pairAt a b i = true := by simp [unitAt, pairAt]

def dark (f : Input → Bool) (t : Fin 7) : Prop :=
  f (unitAt (Fin.castAdd 7 t)) = false ∧ f (unitAt (Fin.natAdd 7 t)) = false

/-- If both factors accept some singleton, then at one incidence their AND
    receives zero on both point-only and line-only evaluations of both factors. -/
theorem dark_factors {A B : Input → Bool} (ma : Increasing A) (mb : Increasing B)
    (sound : ∀ x, A x = true → B x = true → incidence x = true)
    {i j : Fin 14} (leftOn : A (unitAt i) = true) (rightOn : B (unitAt j) = true) :
    ∃ t : Fin 7, dark A t ∧ dark B t := by
  obtain ⟨t,pi,li,pj,lj⟩ := spare_pair i j
  have noA (a : Fin 14) (h : incidence (pairAt a j) = false) : A (unitAt a) = false := by
    cases v : A (unitAt a) with
    | false => rfl
    | true =>
      have both := sound _ (ma _ _ (unit_left a j) v) (mb _ _ (unit_right a j) rightOn)
      simp [h] at both
  have noB (a : Fin 14) (h : incidence (pairAt a i) = false) : B (unitAt a) = false := by
    cases v : B (unitAt a) with
    | false => rfl
    | true =>
      have both := sound _ (ma _ _ (unit_right a i) leftOn) (mb _ _ (unit_left a i) v)
      simp [h] at both
  exact ⟨t,⟨noA _ pj,noA _ lj⟩,⟨noB _ pi,noB _ li⟩⟩

end FanoFactor

#print axioms FanoFactor.dark_factors
