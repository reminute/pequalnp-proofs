import Structure
import G11FourBound

namespace G11FourClauses

open Finset ClauseWitness G11Certificate G11Structure
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def jointEdges (C : Circuit) (j k : ℕ) : Finset (Fin 16) :=
  univ.filter fun e =>
    let x := pairInput (edgeAt e).1 (edgeAt e).2
    gateVal 11 C j x = true ∧ gateVal 11 C k x = true

theorem commonTop (C : Circuit) (j k t : ℕ) (ao : IsAO2 11 C) (tf : TopForm graph C)
    (marked : junk graph C = {j,k}) (jk : ¬ InCone 11 C j k) (kj : ¬ InCone 11 C k j)
    (top : t ∈ tops graph C) (jt : InCone 11 C j t) (kt : InCone 11 C k t) :
    (∃ b : Fin 2, OrReaches 11 C (opnd C t b) j ∧ OrReaches 11 C (opnd C t b) k ∧
      side C t (1-b) ⊆ wmax graph C j ∩ wmax graph C k) ∨ (jointEdges C j k).card ≤ 8 := by
  classical
  rcases merge_dichotomy ao tf marked jk kj top jt kt with same | clean
  · exact Or.inl same
  right
  let F := fourClauses 11 C j k
  have cap := belowGraph_upper F (by
    intro X d
    let x (v : Fin 11) := decide (v ∈ X)
    have on : ∀ i : Fin 4, lit (F i) x := by
      intro i
      obtain ⟨v,hx,hv⟩ := d i
      exact ⟨v,hv,decide_eq_true hx⟩
    have yes := clean x on
    have edgeHit : ∃ u v, graph.Adj u v ∧ u ∈ X ∧ v ∈ X := by
      simpa [graphFun,x] using yes
    obtain ⟨u,v,adj,hu,hv⟩ := edgeHit
    exact ⟨u,hu,v,hv,adj⟩)
  apply (card_le_card ?_).trans cap
  intro e he
  have h := (four_semantics ao tf marked jk kj _).mpr (mem_filter.mp he).2
  apply mem_filter.mpr
  refine ⟨mem_univ _,fun i => ?_⟩
  obtain ⟨v,hv,on⟩ := h i
  exact ⟨v,by simpa [edge,pairInput] using on,hv⟩

end G11FourClauses
