import PEqualNP.Defs

open PEqualNP.MetaComplexity

theorem Rect4123.positive_extension_case {n k m : ℕ} (H : SimpleGraph (Fin n))
    (f : (Fin n → Bool) → Bool) (A B : Fin k → (Fin n → Bool) → Bool)
    (p : Fin k → ℕ) (part : IsLiteralPartition n f k A B p (fun _ => true))
    (small : k ≤ m) :
    ∃ (D : Finset (Fin n)) (h : (Fin n → Bool) → Bool) (k : ℕ)
    (A B : Fin k → (Fin n → Bool) → Bool) (p : Fin k → ℕ) (b : Fin k → Bool)
    (F : Fin k → Finset (Fin n)),
    IsLiteralPartition n h k A B p b ∧
    (∀ x, h x = f x ∨ h x = true ∧ ∃ u ∈ D, ∃ w ∈ D, u ≠ w ∧ x u = true ∧ x w = true) ∧
    (∀ j, b j = false → ∃ v ∈ D, p j = v.val) ∧
    (∀ u ∈ D, ∀ v ∈ D, u ≠ v → ∀ w : H.Walk u v, 3 < w.length) ∧
    (∀ j, b j = true → ∀ v ∈ D, v ∉ F j → ∀ a c, H.Adj a c →
      let x := fun i : Fin n => i == a || i == c
      A j (Function.update x v true) = A j x) ∧
    (∑ j : {j : Fin k // b j = true}, (1 + (F j.val).card)) ≤ m := by
  refine ⟨∅,f,k,A,B,p,(fun _ => true),(fun _ => ∅),part,fun _ => Or.inl rfl,
    by simp,by simp,by simp,?_⟩
  simpa [Fintype.card_subtype] using small

#print axioms Rect4123.positive_extension_case
