import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card

namespace GirthOrdered

variable {α : Type*} [LinearOrder α]

/-- Keep exactly those elements that have no strictly earlier representative. -/
noncomputable def minimal (H : Finset α) (R : α → α → Prop) : Finset α := by
  classical
  exact H.filter fun x => ∀ y ∈ H, y < x → ¬R y x

theorem mem_minimal {H : Finset α} {R : α → α → Prop} {x : α} :
    x ∈ minimal H R ↔ x ∈ H ∧ ∀ y ∈ H, y < x → ¬R y x := by
  classical
  exact Finset.mem_filter

theorem minimal_subset (H : Finset α) (R : α → α → Prop) : minimal H R ⊆ H :=
  fun _ hx => (mem_minimal.mp hx).1

theorem separated (H : Finset α) (R : α → α → Prop) {x y : α}
    (hx : x ∈ minimal H R) (hy : y ∈ minimal H R) (earlier : x < y) : ¬R x y :=
  (mem_minimal.mp hy).2 x ((minimal_subset H R) hx) earlier

/-- Transitivity alone suffices if an element may always represent itself. -/
theorem cover_or_self (H : Finset α) (R : α → α → Prop)
    (transitive : ∀ {a b c}, R a b → R b c → R a c) {x : α} (hx : x ∈ H) :
    ∃ t ∈ minimal H R, t = x ∨ t < x ∧ R t x := by
  classical
  let ancestors := H.filter (fun y => y ≤ x ∧ (y = x ∨ R y x))
  have self : x ∈ ancestors := Finset.mem_filter.mpr ⟨hx,le_rfl,Or.inl rfl⟩
  let t := ancestors.min' ⟨x,self⟩
  have mem : t ∈ ancestors := ancestors.min'_mem _
  obtain ⟨ht,le,rep⟩ := Finset.mem_filter.mp mem
  have first : t ∈ minimal H R := by
    refine mem_minimal.mpr ⟨ht,?_⟩
    intro y hy earlier rel
    have r : R y x := rep.elim (fun eq => eq ▸ rel) (transitive rel)
    have ym : y ∈ ancestors := Finset.mem_filter.mpr ⟨hy,earlier.le.trans le,Or.inr r⟩
    exact (not_lt_of_ge (ancestors.min'_le y ym)) earlier
  refine ⟨t,first,?_⟩
  by_cases eq : t = x
  · exact Or.inl eq
  · exact Or.inr ⟨lt_of_le_of_ne le eq,rep.resolve_left eq⟩

theorem cover (H : Finset α) (R : α → α → Prop) (refl : ∀ a ∈ H, R a a)
    (transitive : ∀ {a b c}, R a b → R b c → R a c) {x : α} (hx : x ∈ H) :
    ∃ t ∈ minimal H R, t ≤ x ∧ R t x := by
  obtain ⟨t,ht,eq | ⟨lt,h⟩⟩ := cover_or_self H R transitive hx
  · subst t
    exact ⟨x,ht,le_rfl,refl x hx⟩
  · exact ⟨t,ht,lt.le,h⟩

/-- When representatives are chosen from H, every cover contains all the
    minimal elements. This direction needs no axioms on R. -/
theorem necessary (H T : Finset α) (R : α → α → Prop) (inside : T ⊆ H)
    (rep : ∀ x ∈ H, ∃ t ∈ T, t ≤ x ∧ R t x) : minimal H R ⊆ T := by
  intro x hx
  obtain ⟨xmem,none⟩ := mem_minimal.mp hx
  obtain ⟨t,ht,le,r⟩ := rep x xmem
  rcases le.lt_or_eq with earlier | eq
  · exact (none t (inside ht) earlier r).elim
  · exact eq ▸ ht

/-- Failure of all chronological covers of size k yields exactly k+1
    elements such that no earlier one represents a later one. -/
theorem packing (H : Finset α) (R : α → α → Prop) (k : ℕ) (refl : ∀ a ∈ H, R a a)
    (transitive : ∀ {a b c}, R a b → R b c → R a c)
    (noCover : ∀ T ⊆ H, T.card ≤ k → (∀ x ∈ H, ∃ t ∈ T, t ≤ x ∧ R t x) → False) :
    ∃ Q ⊆ H, Q.card = k+1 ∧ ∀ x ∈ Q, ∀ y ∈ Q, x < y → ¬R x y := by
  have large : k < (minimal H R).card := lt_of_not_ge (fun small =>
    noCover _ (minimal_subset H R) small (fun _ hx => cover H R refl transitive hx))
  obtain ⟨Q,sub,card⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt large)
  exact ⟨Q,sub.trans (minimal_subset H R),card,fun _ hx _ hy lt =>
    separated H R (sub hx) (sub hy) lt⟩

end GirthOrdered

#print axioms GirthOrdered.cover
#print axioms GirthOrdered.packing
