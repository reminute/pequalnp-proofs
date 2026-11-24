import PartnerCertificate
import GraphDensity

namespace Edge606.Sensitivity

open Finset SimpleGraph Cubic1971.PartnerCertificate
open PEqualNP.MetaComplexity.NestedCover

variable {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {v : Fin n}

/-- An assignment on fewer than deg(v) other coordinates can be completed
    to a sensitive input whenever its prescribed ones contain no edge.
    Each fixed coordinate can block at most one neighbor branch. -/
theorem complete_input (girth : GirthEdgeNegatives.GirthFive G) (P Z : Finset (Fin n))
    (away : v ∉ P) (apart : Disjoint P Z) (ind : free G P)
    (short : (P ∪ Z).card < G.degree v) :
    ∃ S, P ⊆ S ∧ Disjoint S Z ∧ sensitive G ∅ v S := by
  classical
  apply (completion_iff away apart (by simp) (by simp [clean]) ind).mpr
  by_contra no
  have pick (w : G.neighborSet v) : ∃ t : ↑(P ∪ Z), t.val = w.val ∨ (t.val ≠ v ∧ G.Adj w.val t.val) := by
    by_cases fixed : w.val ∈ Z
    · exact ⟨⟨_, mem_union_right _ fixed⟩, Or.inl rfl⟩
    · by_contra! none
      exact no ⟨w.val, w.property, fixed, fun t tp adj =>
        (none ⟨t, mem_union_left _ tp⟩).2 (fun eq => away (eq ▸ tp)) adj⟩
  choose f hf using pick
  have inj : Function.Injective f := by
    intro a b same
    apply Subtype.ext
    by_contra different
    have ha := hf a
    have hb := hf b
    rw [← same] at hb
    rcases ha with ea | ⟨off, ax⟩ <;> rcases hb with eb | ⟨off', bx⟩
    · exact different (ea.symm.trans eb)
    · rw [ea] at bx
      exact GirthEdgeNegatives.no_triangle girth b.property bx a.property.symm
    · rw [eb] at ax
      exact GirthEdgeNegatives.no_triangle girth a.property ax b.property.symm
    · exact GirthEdgeNegatives.no_square girth a.property ax bx.symm b.property.symm off.symm different
  have count := Fintype.card_le_of_injective f inj
  rw [G.card_neighborSet_eq_degree] at count
  exact (Nat.not_lt_of_ge (by simpa only [Fintype.card_coe] using count)) short

theorem bit_edge (S : Finset (Fin n)) :
    GraphDensity.edgeFunction G (bits S) = graphFun G ∅ (bits S) := by
  simp [GraphDensity.edgeFunction, graphFun]

/-- Even after one other bit is fixed to either value, flipping v can change the answer. -/
theorem one_fixed (girth : GirthEdgeNegatives.GirthFive G) (large : 1 < G.degree v)
    (w : Fin n) (other : v ≠ w) (b : Bool) :
    ∃ x y : Fin n → Bool, x w = b ∧ y w = b ∧ (∀ i, i ≠ v → x i = y i) ∧
      GraphDensity.edgeFunction G x = false ∧ GraphDensity.edgeFunction G y = true := by
  classical
  let P : Finset (Fin n) := if b then {w} else ∅
  let Z : Finset (Fin n) := if b then ∅ else {w}
  obtain ⟨S, keep, avoid, sens⟩ := complete_input (v := v) girth P Z
    (by cases b <;> simp [P, other])
    (by cases b <;> simp [P,Z])
    (by cases b <;> simp [P,free])
    (by cases b <;> simpa [P,Z] using large)
  have states := (toggle (by simp) sens.1).mp sens
  have value : bits S w = b := by
    cases b with
    | false =>
      have away : w ∉ S := fun h => disjoint_left.mp avoid h (by simp [Z])
      simp [bits, away]
    | true =>
      have high : w ∈ S := keep (by simp [P])
      simp [bits, high]
  refine ⟨bits S, bits (insert v S), value, ?_, ?_, (bit_edge S).trans states.1,
    (bit_edge _).trans states.2⟩
  · simpa [bits, other.symm] using value
  · intro i off
    simp [bits, off]

end Edge606.Sensitivity

#print axioms Edge606.Sensitivity.complete_input
#print axioms Edge606.Sensitivity.one_fixed
