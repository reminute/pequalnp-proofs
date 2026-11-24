import LeastAlias
import Structure

namespace G11Structure

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1490

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem primitive_operand (ao : IsAO2 n C) (tf : TopForm G C) {j k : ℕ}
    (marked : junk G C = {j,k}) (kj : ¬InCone n C k j) (b : Fin 2) (x : Fin n → Bool) :
    wireVal n C (opnd C j b) x = true ↔ lit (side C j b) x := by
  have member : j ∈ junk G C := by simp [marked]
  obtain ⟨bound,op,_⟩ := Finset.mem_filter.mp member
  have hj := Finset.mem_range.mp bound
  rw [operand_iff ao tf hj op b x]
  refine or_iff_left ?_
  rintro ⟨i,hi,reach,_⟩
  have facts := side_operand ao hj b
  have sub := operand_cone hj facts.1 facts.2 (orReaches_reach i _ reach).1
  rw [marked] at hi
  rcases Finset.mem_insert.mp hi with rfl | mem
  · exact lt_irrefl _ (cone_lt sub)
  · rw [Finset.mem_singleton.mp mem] at sub
    exact kj sub

theorem primitive_incomparable (least : IsLeastAO G C) (tf : TopForm G C) {j k : ℕ}
    (marked : junk G C = {j,k}) (kj : ¬ InCone n C k j) (b : Fin 2) :
    ¬ side (n:=n) C j b ⊆ side C j (1-b) := by
  intro contained
  have member : j ∈ junk G C := by simp [marked]
  have bound : j < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp member).1
  have earlier := (side_operand least.1 bound b).2
  apply G11Bypass.no_earlier_alias least bound earlier
  intro x
  have pw := primitive_operand least.1 tf marked kj b x
  have jw := primitive_junk least.1 tf marked kj x
  have eqTrue : gateVal n C j x = true ↔ wireVal n C (opnd C j b) x = true := by
    rw [pw,jw]
    refine ⟨fun all => all b,?_⟩
    rintro ⟨v,hv,on⟩ d
    have either : d=b ∨ d=1-b := by fin_cases b <;> fin_cases d <;> decide
    rcases either with rfl | rfl
    · exact ⟨v,hv,on⟩
    · exact ⟨v,contained hv,on⟩
  change gateVal n C j x = wireVal n C (opnd C j b) x
  cases l : gateVal n C j x <;> cases r : wireVal n C (opnd C j b) x <;> try rfl
  · exact l.symm.trans (eqTrue.mpr r)
  · exact ((eqTrue.mp l).symm.trans r)

end G11Structure
