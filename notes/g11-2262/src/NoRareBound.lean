import RareIndex
import SmallUncovered
import ProtectedObstruction

namespace G11Residual

open G11Certificate G11FourClauses G11Structure
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem index_endpoints (u v : Fin 11) (adj : graph.Adj u v) :
    ∃ e : Fin 16, ((edgeAt e).1 = u ∧ (edgeAt e).2 = v) ∨ ((edgeAt e).1 = v ∧ (edgeAt e).2 = u) := by
  obtain ⟨e,eq⟩ := (graph_edges u v).mp adj
  refine ⟨e,?_⟩
  have se : symEdge e = s(u,v) := by
    apply Sym2.ext
    intro z
    rw [← Sym2.mem_toFinset,← Sym2.mem_toFinset,symEdge,Sym2.toFinset_mk_eq,Sym2.toFinset_mk_eq]
    change z ∈ edge e ↔ z ∈ {u,v}
    rw [eq]
  have eqp := (@Sym2.mk_eq_mk_iff _ (edgeAt e) (u,v)).mp se
  exact eqp.imp (fun eq => ⟨congrArg Prod.fst eq,congrArg Prod.snd eq⟩)
    (fun eq => ⟨congrArg Prod.fst eq,congrArg Prod.snd eq⟩)

theorem neighbors_index (C : Circuit) (u v : Fin 11)
    (adj : (graph.deleteEdges (Ustar graph C : Set _)).Adj u v) :
    v ∈ G11Protected.neighbors (residualIndices C) u := by
  obtain ⟨edgeGood,kept⟩ := SimpleGraph.deleteEdges_adj.mp adj
  obtain ⟨e,orientation⟩ := index_endpoints u v edgeGood
  have same : symEdge e = s(u,v) := by
    rcases orientation with ⟨f,g⟩ | ⟨f,g⟩
    · rw [symEdge,f,g]
    · rw [symEdge,f,g,Sym2.eq_swap]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,e,fun he => kept (same ▸ (Finset.mem_filter.mp he).2),orientation⟩

theorem no_rare_one {C : Circuit} {j k t : ℕ} (least : IsLeastAO graph C) (tf : TopForm graph C)
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
    (rare : orN graph C \ lam graph C = ∅) (one : (centreless graph C).card = 1) : 22 ≤ C.size := by
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
  have budget : K.card ≤ U.card+2 := by omega
  obtain ⟨z,blocks⟩ := G11Protected.blocking_negative U K cover budget
  let F := fourClauses 11 C j k
  have pattern := rare_free_joint least.1 tf marked jk kj top jt kt rare one.le source
  have hits (i : Fin 4) (e : Fin 16) (he : e ∈ U) : ¬ Disjoint (edge e) (F i) := by
    have uv := pattern (edgeAt e).1 (edgeAt e).2 (Finset.mem_filter.mp he).2
    obtain ⟨v,inA,on⟩ := (four_semantics least.1 tf marked jk kj _).mpr uv i
    exact Finset.not_disjoint_iff.mpr ⟨v,by simpa [edge,pairInput] using on,inA⟩
  have allowed (i : Fin 4) : G11Protected.allowed U (F i) := by
    rcases four_raw_residual C j k least.1 rare sides i with small | ⟨c,adj⟩
    · exact Or.inl (Finset.card_le_one_iff_subset_singleton.mp small)
    · exact Or.inr ⟨c,fun v hv => neighbors_index C c v (adj v hv)⟩
  let x (v : Fin 11) := decide (v ∈ negative z)
  have litAll (i : Fin 4) : lit (F i) x := by
    obtain ⟨v,vA,vZ⟩ := Finset.not_disjoint_iff.mp (blocks (F i) (allowed i) (hits i))
    exact ⟨v,vA,decide_eq_true vZ⟩
  obtain ⟨jMem,kMem⟩ : j ∈ junk graph C ∧ k ∈ junk graph C := by simp [marked]
  have clean := (merge_dichotomy least.1 tf marked jk kj top jt kt).resolve_left (by
    rintro ⟨b,bj,bk,_⟩
    have ej := rare_free_direct least.1 rare jMem bj
    have ek := rare_free_direct least.1 rare kMem bk
    omega)
  have impossible := clean x litAll
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,
    decide_eq_true_eq,x] at impossible
  obtain ⟨u,v,adj,hu,hv⟩ := impossible
  exact graph_independent z u v hu hv adj

end G11Residual
