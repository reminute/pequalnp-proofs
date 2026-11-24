import SampleLift

/-- The first child exactly as printed by the project checker. -/
theorem Rect4123.closed_extension :
∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : Fin x1) (x5 : (Fin x1 → Bool) → Bool),   (∀ (x6 : Fin x1) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) →     (∀ (x7 : Fin x1 → Bool), x5 x7 = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x3.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) →       (∃ (x8 : Finset (Fin x1)) (x9 : (Fin x1 → Bool) → Bool) (x10 : ℕ) (x11 : Fin x10 → (Fin x1 → Bool) → Bool) (x12 : Fin x10 → (Fin x1 → Bool) → Bool) (x13 : Fin x10 → ℕ) (x14 : Fin x10 → Bool) (x15 : Fin x10 → Finset (Fin x1)),           PEqualNP.MetaComplexity.IsLiteralPartition x1 x9 x10 x11 x12 x13 x14 ∧             (∀ (x16 : Fin x1 → Bool), x9 x16 = x5 x16 ∨ x9 x16 = Bool.true ∧ ∃ x17 ∈ x8, ∃ x18 ∈ x8, x17 ≠ x18 ∧ x16 x17 = Bool.true ∧ x16 x18 = Bool.true) ∧               (∀ (x16 : Fin x10), x14 x16 = Bool.false → ∃ x18 ∈ x8, x13 x16 = ↑x18) ∧                 (∀ x16 ∈ x8, ∀ x18 ∈ x8, x16 ≠ x18 → ∀ (x21 : x3.Walk x16 x18), (3 : ℕ) < x21.length) ∧                   (∀ (x16 : Fin x10),                       x14 x16 = Bool.true →                         ∀ x18 ∈ x8,                           x18 ∉ x15 x16 →                             ∀ (x21 x22 : Fin x1),                               x3.Adj x21 x22 →                                 have x24 : Fin x1 → Bool := fun (x24 : Fin x1) => x24 == x21 || x24 == x22;                                 x11 x16 (Function.update x24 x18 Bool.true) = x11 x16 x24) ∧                     ∑ x16 : { x16 : Fin x10 // x14 x16 = Bool.true }, ((1 : ℕ) + (x15 ↑x16).card) ≤ x2) →         ∃ (x9 : Fin x2 → Fin x1 → Fin x1 → Prop) (x10 : Fin x2 → Fin x1 → Fin x1 → Prop) (x11 : Fin x2 → Fin x1), ∀ (x12 x13 x14 x15 : Fin x1), x3.Adj x12 x13 → x14 = x15 ∨ x3.Adj x14 x15 → (∃! x18 : Fin x2, x9 x18 x12 x13 ∧ x10 x18 x14 x15) ∧ ∀ (x18 : Fin x2), x9 x18 x12 x13 → x10 x18 x14 x15 → (x11 x18 = x12 ∨ x11 x18 = x13) ∧ ¬((x3.Adj x14 (x11 x18) ∨ x3.Adj x15 (x11 x18)) ∧ x11 x18 ≠ x14 ∧ x11 x18 ≠ x15) := by
  intro n m H z f girth spec possible
  obtain ⟨D,h,k,A,B,p,b,F,part,extend,neg,sep,stable,budget⟩ := possible
  have accept x (hx : f x = true) : h x = true := by
    rcases extend x with eq | hit
    · exact eq.trans hx
    · exact hit.1
  have extra x (hx : h x = true) : f x = true ∨ ∃ u ∈ D, ∃ w ∈ D,
      u ≠ w ∧ x u = true ∧ x w = true := by
    rcases extend x with eq | hit
    · exact Or.inl (eq.symm.trans hx)
    · exact Or.inr hit.2
  refine Rect4123.SampleLift.of_extension H z f h girth spec A B p b part D ?_
    accept extra neg F ?_ budget
  · intro u hu v hv different short
    obtain ⟨w,length⟩ := short
    exact (Nat.not_lt_of_ge length) (sep u hu v hv different w)
  · intro j s v vv out a c ac
    have eq : Rect4123.SampleLift.row a c = (fun i => i == a || i == c) := by
      funext i
      by_cases ha : i = a <;> by_cases hc : i = c <;>
        simp_all [Rect4123.SampleLift.row]
    rw [eq]
    exact stable j s v vv out a c ac

#print axioms Rect4123.closed_extension
