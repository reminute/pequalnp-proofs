import OneGuard
import TwoRounds

namespace G11Residual

open G11Certificate G11FourClauses G11Structure
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem capture_eq (U : Finset (Fin 16)) (Y : Finset (Fin 24)) :
    capture U Y = G11TwoRounds.captured U Y := by
  ext e
  simp [capture,G11TwoRounds.captured,edge,Finset.insert_subset_iff,Finset.singleton_subset_iff]

theorem no_rare_two {C : Circuit} {j k t : ℕ} (least : IsLeastAO graph C) (tf : TopForm graph C)
    (sides : ∀ a ∈ tops graph C, ∀ u ∈ side C a 0, ∀ v ∈ side C a 1, graph.Adj u v)
    (source : ∀ u v : Fin 11, s(u,v) ∈ Ustar graph C → ∃ z ∈ tops graph C, ∃ b : Fin 2, ∃ i : ℕ,
      (i = j ∨ i = k) ∧ gateVal 11 C z (pairInput u v) = true ∧
      OrReaches 11 C (opnd C z b) i ∧ gateVal 11 C i (pairInput u v) = true)
    (count : 17 + (tops graph C \ centreless graph C).card + 2*(centreless graph C).card +
      (orN graph C \ lam graph C).card ≤ C.size + (Ustar graph C).card)
    (minimum : ∀ K : Finset (Fin 11), IsMinCover (graph.deleteEdges ↑(Ustar graph C)) K →
      K.card ≤ (tops graph C \ centreless graph C).card)
    (distinct : j < k) (marked : junk graph C = {j,k}) (jk : ¬ InCone 11 C j k) (kj : ¬ InCone 11 C k j)
    (top : t ∈ tops graph C) (jt : InCone 11 C j t) (kt : InCone 11 C k t)
    (rare : orN graph C \ lam graph C = ∅) (two : (centreless graph C).card = 2) : 22 ≤ C.size := by
  classical
  by_contra! short
  let U := residualIndices C
  obtain ⟨K,hK⟩ := G11SmallUncovered.exists_minimum (graph.deleteEdges ↑(Ustar graph C))
  have minK := minimum K hK
  have symBound : (Ustar graph C).card ≤ U.card := by
    rw [← indices_image C]
    exact Finset.card_image_le
  have cover : G11Protected.covers U K := by
    intro e
    by_cases removed : e ∈ U
    · exact Or.inl removed
    have accepted : graph.Adj (edgeAt e).1 (edgeAt e).2 :=
      (graph_edges _ _).mpr ⟨e,rfl⟩
    apply Or.inr (hK.1 (SimpleGraph.deleteEdges_adj.mpr ⟨accepted,?_⟩))
    exact fun he => removed (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
  have budget : K.card ≤ U.card := by omega
  obtain ⟨Y,z,hz,r1,r2⟩ := G11TwoRounds.two_rounds U K cover budget
  have blocks : obstruction U := by
    refine ⟨Y,z,hz,r1,?_⟩
    rw [capture_eq]
    exact r2
  obtain ⟨clean,S,card,safeS,coversS⟩ :=
    residual_guards least.1 tf rare distinct.ne marked jk kj sides top jt kt source
  exact forbidden_profile least.1 tf rare marked jk kj sides clean S (by omega)
    (fun g hg => (safeS g hg).2) coversS blocks

end G11Residual
