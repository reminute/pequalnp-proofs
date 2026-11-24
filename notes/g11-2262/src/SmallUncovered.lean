import Structure
import G11NineEdges

namespace G11SmallUncovered

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.EdgeOwnership

-- The two disjoint triangles and the disjoint five-cycle give the cover bound.
-- These cycles also appear in the recorded parent reduction R_meta_1597_318.
theorem seven (K : Finset (Fin 11)) (hK : G11Certificate.graph.IsVertexCover (↑K)) : 7 ≤ K.card := by
  classical
  let w (i : Fin 11) : ℕ := if i ∈ K then 1 else 0
  have ew (u v : Fin 11) (he : G11Certificate.graph.Adj u v) : 1 ≤ w u + w v := by
    rcases hK he with hu | hv
    · change u ∈ K at hu
      simp [w,hu]
    · change v ∈ K at hv
      simp [w,hv]
  have e0 := ew 1 4 (by decide)
  have e1 := ew 4 8 (by decide)
  have e2 := ew 8 1 (by decide)
  have e3 := ew 3 6 (by decide)
  have e4 := ew 6 7 (by decide)
  have e5 := ew 7 3 (by decide)
  have e6 := ew 0 9 (by decide)
  have e7 := ew 9 5 (by decide)
  have e8 := ew 5 2 (by decide)
  have e9 := ew 2 10 (by decide)
  have e10 := ew 10 0 (by decide)
  have hw : ∑ i, w i = K.card := by simp [w]
  rw [Fin.sum_univ_succ] at hw
  simp [Fin.sum_univ_succ] at hw
  omega

theorem residual_cover (U : Finset (Sym2 (Fin 11))) (K : Finset (Fin 11))
    (cover : (G11Certificate.graph.deleteEdges (↑U)).IsVertexCover (↑K)) : 7 ≤ K.card + U.card := by
  classical
  let A := U.image fun e => e.out.1
  have full : G11Certificate.graph.IsVertexCover (↑(K ∪ A)) := by
    intro u v edge
    by_cases deleted : s(u,v) ∈ U
    · have chosen : s(u,v).out.1 ∈ A := Finset.mem_image_of_mem _ deleted
      have endpoint := Sym2.out_fst_mem s(u,v)
      rw [Sym2.mem_iff] at endpoint
      rcases endpoint with eq | eq
      · exact Or.inl (Finset.mem_union_right _ (eq ▸ chosen))
      · exact Or.inr (Finset.mem_union_right _ (eq ▸ chosen))
    · exact (cover (SimpleGraph.deleteEdges_adj.mpr ⟨edge,deleted⟩)).imp
        (Finset.mem_union_left _) (Finset.mem_union_left _)
  have bound := seven (K ∪ A) full
  have union := Finset.card_union_le K A
  have count : A.card ≤ U.card := Finset.card_image_le
  omega

theorem exists_minimum {n : ℕ} (H : SimpleGraph (Fin n)) :
    ∃ K : Finset (Fin n), IsMinCover H K := by
  classical
  let P (m : ℕ) := ∃ K : Finset (Fin n), H.IsVertexCover (↑K) ∧ K.card = m
  have existsP : ∃ m, P m := ⟨_,Finset.univ,by simp,rfl⟩
  obtain ⟨K,hK,card⟩ := Nat.find_spec existsP
  exact ⟨K,hK,fun A cover => card.trans_le (Nat.find_min' existsP ⟨A,cover,rfl⟩)⟩

theorem small {G : SimpleGraph (Fin 11)} [DecidableRel G.Adj] {C : Circuit} {i j : ℕ}
    (g11 : G = G11Certificate.graph) (least : IsLeastAO G C) (top : TopForm G C)
    (count : 17 + (tops G C \ centreless G C).card + 2 * (centreless G C).card +
      (orN G C \ lam G C).card ≤ C.size + (Ustar G C).card)
    (residual : ∀ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑(Ustar G C)) K →
      K.card ≤ (tops G C \ centreless G C).card)
    (order : i < j) (dirty : junk G C = {i,j}) (ij : ¬ InCone 11 C i j)
    (ji : ¬ InCone 11 C j i) (common : ∃ t ∈ tops G C, InCone 11 C i t ∧ InCone 11 C j t)
    (few : (Ustar G C).card ≤ 2) : 22 ≤ C.size := by
  classical
  obtain ⟨t,ht,hin,hjn⟩ := common
  have paid : 2 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card := by
    by_cases centered : t ∈ centreless G C
    · have pos := Finset.card_pos.mpr ⟨t,centered⟩
      omega
    · have two := G11Structure.two_rare_of_common_top least.1 top (Nat.ne_of_lt order) dirty
        ij ji ht hin hjn centered
      omega
  obtain ⟨K,minimal⟩ := exists_minimum (G.deleteEdges ↑(Ustar G C))
  have coverT := residual K minimal
  have bound : 7 ≤ K.card + (Ustar G C).card := by
    apply residual_cover
    have e := minimal.1
    rwa [← g11]
  omega

end G11SmallUncovered
