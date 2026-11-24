import RareFree
import G11MergeBound

namespace G11Residual

open G11Certificate G11FourClauses G11Structure
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def symEdge (e : Fin 16) : Sym2 (Fin 11) := s((edgeAt e).1,(edgeAt e).2)

def residualIndices (C : Circuit) : Finset (Fin 16) :=
  Finset.univ.filter fun e => symEdge e ∈ Ustar graph C

theorem indices_image (C : Circuit) : (residualIndices C).image symEdge = Ustar graph C := by
  ext edgeSym
  constructor
  · rintro h
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp h
    exact (Finset.mem_filter.mp he).2
  · intro h
    induction edgeSym using Sym2.ind with
    | _ u v =>
      have isEdge := (Finset.mem_sdiff.mp h).1
      rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] at isEdge
      obtain ⟨e,he⟩ := (graph_edges u v).mp isEdge
      have symEq : symEdge e = s(u,v) := by
        apply Sym2.ext
        intro z
        rw [← Sym2.mem_toFinset,← Sym2.mem_toFinset, symEdge,Sym2.toFinset_mk_eq,Sym2.toFinset_mk_eq]
        change z ∈ edge e ↔ z ∈ {u,v}
        rw [he]
      exact Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,symEq.symm ▸ h⟩,symEq⟩

theorem indexed_joint (C : Circuit) (j k : ℕ)
    (joint : ∀ u v : Fin 11, s(u,v) ∈ Ustar graph C →
      gateVal 11 C j (pairInput u v) = true ∧ gateVal 11 C k (pairInput u v) = true) :
    residualIndices C ⊆ jointEdges C j k ∧
    Ustar graph C ⊆ (jointEdges C j k).image symEdge := by
  have sub : residualIndices C ⊆ jointEdges C j k := by
    intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,joint _ _ (Finset.mem_filter.mp he).2⟩
  refine ⟨sub,?_⟩
  rw [← indices_image C]
  exact Finset.image_mono symEdge sub

theorem four_raw_residual (C : Circuit) (j k : ℕ) (ao : IsAO2 11 C)
    (rare : orN graph C \ lam graph C = ∅)
    (sides : ∀ a ∈ tops graph C, ∀ u ∈ side C a 0, ∀ v ∈ side C a 1, graph.Adj u v) :
    ∀ i : Fin 4, (fourClauses 11 C j k i).card ≤ 1 ∨ ∃ c : Fin 11,
      ∀ v ∈ fourClauses 11 C j k i, (graph.deleteEdges (Ustar graph C : Set _)).Adj c v := by
  intro i
  fin_cases i
  · exact rare_free_raw_clause ao rare sides (opnd C j 0)
  · exact rare_free_raw_clause ao rare sides (opnd C j 1)
  · exact rare_free_raw_clause ao rare sides (opnd C k 0)
  · exact rare_free_raw_clause ao rare sides (opnd C k 1)

end G11Residual
