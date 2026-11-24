import PrimitiveSides
import OneGuard
import RareAlternatives

namespace G11GuardCircuit

open G11Certificate G11FourClauses G11Structure G11Residual
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def exception : Finset (Fin 16) := Finset.univ.filter fun e => (18453 : ℕ).testBit e.val

theorem exception_cover (K : Finset (Fin 11)) (cov : G11Protected.covers exception K) :
    4 ≤ K.card := by
  open G11Protected in
    have h15 : 1 ≤ weight K 8 + weight K 9 := endpoint_charge cov 15 (by decide)
    have h9 : 1 ≤ weight K 4 + weight K 10 := endpoint_charge cov 9 (by decide)
    have h7 : 1 ≤ weight K 3 + weight K 7 := endpoint_charge cov 7 (by decide)
    have h12 : 1 ≤ weight K 6 + weight K 7 := endpoint_charge cov 12 (by decide)
    have h6 : 1 ≤ weight K 3 + weight K 6 := endpoint_charge cov 6 (by decide)
    have count := total_weight K
    omega

theorem bound_of_cap {C : Circuit}
    (count : 17 + (tops graph C \ centreless graph C).card + 2*(centreless graph C).card +
      (orN graph C \ lam graph C).card ≤ C.size + (Ustar graph C).card)
    (minimum : ∀ K : Finset (Fin 11), IsMinCover (graph.deleteEdges ↑(Ustar graph C)) K →
      K.card ≤ (tops graph C \ centreless graph C).card)
    (three : 3 ≤ (centreless graph C).card)
    (cap : (residualIndices C).card ≤ 4 ∨ ∀ e ∈ residualIndices C, (18453 : ℕ).testBit e.val = true) :
    22 ≤ C.size := by
  classical
  obtain ⟨K,hK⟩ := G11SmallUncovered.exists_minimum (graph.deleteEdges ↑(Ustar graph C))
  have minK := minimum K hK
  have symBound : (Ustar graph C).card ≤ (residualIndices C).card := by
    rw [← indices_image C]
    exact Finset.card_image_le
  rcases cap with small | contained
  · have cover := G11SmallUncovered.residual_cover _ K hK.1
    omega
  · have inc : residualIndices C ⊆ exception := fun e he =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,contained e he⟩
    have sz := Finset.card_le_card inc
    have szMax : exception.card = 5 := by decide
    have four := exception_cover K (by
      intro e
      by_cases removed : e ∈ residualIndices C
      · exact Or.inl (inc removed)
      have accepted : graph.Adj (edgeAt e).1 (edgeAt e).2 := (graph_edges _ _).mpr ⟨e,rfl⟩
      exact Or.inr (hK.1 (SimpleGraph.deleteEdges_adj.mpr ⟨accepted,fun h =>
        removed (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)⟩)))
    omega

def fires (A B row : Finset (Fin 11)) : Prop := ¬Disjoint row A ∧ ¬Disjoint row B

def visible (A B : Finset (Fin 11)) (e : Fin 16) : Prop :=
  fires A B (edge e) ∧ ∃ v ∈ edge e, ∀ z : Fin 24, fires A B (negative z) → v ∉ negative z

theorem nonedge_row : ∀ u v : Fin 11, ¬graph.Adj u v →
    ∃ z : Fin 24, u ∈ negative z ∧ v ∈ negative z := by decide

theorem dirty_row {C : Circuit} {g : ℕ} (mem : g ∈ junk graph C)
    (sem : ∀ x, gateVal 11 C g x = true ↔ ∀ b : Fin 2, lit (side C g b) x) :
    ∃ z : Fin 24, fires (side C g 0) (side C g 1) (negative z) := by
  obtain ⟨_,_,_,x,on,off⟩ := Finset.mem_filter.mp mem
  obtain ⟨u,hu,ux⟩ := (sem x).mp on 0
  obtain ⟨v,hv,vx⟩ := (sem x).mp on 1
  have nonedge : ¬graph.Adj u v := by
    intro adjacent
    have yes : graphFun graph ∅ x = true := by
      apply Bool.or_eq_true_iff.mpr
      exact Or.inr (decide_eq_true ⟨u,v,adjacent,ux,vx⟩)
    simp [off] at yes
  obtain ⟨z,uz,vz⟩ := nonedge_row u v nonedge
  exact ⟨z,Finset.not_disjoint_iff.mpr ⟨u,uz,hu⟩,Finset.not_disjoint_iff.mpr ⟨v,vz,hv⟩⟩

theorem gate_profile {C : Circuit} {g : ℕ}
    (sem : ∀ x, gateVal 11 C g x = true ↔ ∀ b : Fin 2, lit (side C g b) x) :
    (∀ e, gateVal 11 C g (edgeInput e) = true ↔ fires (side C g 0) (side C g 1) (edge e)) ∧
    (∀ z, gateVal 11 C g (negInput z) = true ↔ fires (side C g 0) (side C g 1) (negative z)) := by
  constructor
  · intro e
    rw [sem]
    exact ⟨fun h => ⟨(positive_lit _ _).mp (h 0),(positive_lit _ _).mp (h 1)⟩,
      fun h b => (positive_lit _ _).mpr (by fin_cases b; exact h.1; exact h.2)⟩
  · intro z
    rw [sem]
    exact ⟨fun h => ⟨Disjoint.symm.mt ((negative_lit _ _).mp (h 0)),
      Disjoint.symm.mt ((negative_lit _ _).mp (h 1))⟩,fun h b =>
      (negative_lit _ _).mpr (Disjoint.symm.mt (by fin_cases b; exact h.1; exact h.2))⟩

abbrev capRule := ∀ (U : Finset (Fin 16)) (A B D E : Finset (Fin 11)),
  G11Protected.allowed U A → G11Protected.allowed U B → G11Protected.allowed U D → G11Protected.allowed U E →
  A.Nonempty → B.Nonempty → D.Nonempty → E.Nonempty →
  (¬ A ⊆ B) → (¬ B ⊆ A) → (¬ D ⊆ E) → (¬ E ⊆ D) →
  (∃ z, fires A B (negative z)) → (∃ z, fires D E (negative z)) →
  (∀ z, ¬(fires A B (negative z) ∧ fires D E (negative z))) →
  (∀ e ∈ U, (fires A B (edge e) ∧ fires D E (edge e)) ∨ visible A B e ∨ visible D E e) →
  U.card ≤ 4 ∨ ∀ e ∈ U, (18453 : ℕ).testBit e.val = true

theorem no_rare_three (numeric : capRule) {C : Circuit} {j k t : ℕ}
    (least : IsLeastAO graph C) (tf : TopForm graph C)
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
    (rare : orN graph C \ lam graph C = ∅) (three : 3 ≤ (centreless graph C).card) : 22 ≤ C.size := by
  classical
  apply bound_of_cap count minimum three
  let U := residualIndices C
  have swapped := marked.trans (Finset.pair_comm _ _)
  have sj := primitive_junk least.1 tf marked kj
  have sk := primitive_junk least.1 tf swapped jk
  have ⟨pj,nj⟩ := gate_profile sj
  have ⟨pk,nk⟩ := gate_profile sk
  have incJ := primitive_incomparable least tf marked kj
  have incK := primitive_incomparable least tf swapped jk
  have allow (g : ℕ) (b : Fin 2) : G11Protected.allowed U (side C g b) :=
    allowed_wire C least.1 rare sides (opnd C g b)
  have nonempty {a b : Finset (Fin 11)} (h : ¬a ⊆ b) : a.Nonempty := by
    by_contra! empty
    exact h (empty ▸ Finset.empty_subset _)
  have j0 := incJ 0
  have j1 := incJ 1
  have k0 := incK 0
  have k1 := incK 1
  refine numeric U _ _ _ _ (allow j 0) (allow j 1) (allow k 0) (allow k 1)
    (nonempty j0) (nonempty j1) (nonempty k0) (nonempty k1) j0 j1 k0 k1
    (dirty_row (by simp [marked]) sj) (dirty_row (by simp [marked]) sk) ?_ ?_
  · intro z ⟨first,second⟩
    have clean := (residual_guards least.1 tf rare distinct.ne marked jk kj sides top jt kt source).1
    have wrong := clean _ ((nj z).mpr first) ((nk z).mpr second)
    rw [negative_off] at wrong
    exact Bool.noConfusion wrong
  · intro e he
    obtain joint | ⟨i,mem,hit,endpoint⟩ := other_witness least.1 tf marked source
      (edgeAt e).1 (edgeAt e).2 (Finset.mem_filter.mp he).2
    · exact Or.inl ⟨(pj e).mp joint.1,(pk e).mp joint.2⟩
    · obtain ⟨v,ev,can⟩ : ∃ v ∈ edge e, v ∈ wmax graph C i := by
        rcases endpoint with left | right
        · exact ⟨_,Finset.mem_insert_self _ _,left⟩
        · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_singleton_self _),right⟩
      have safe (z : Fin 24) (on : gateVal 11 C i (negInput z) = true) : v ∉ negative z := by
        intro contained
        have bad := (Finset.mem_filter.mp can).2 (negInput z) on (decide_eq_true contained)
        rw [negative_off] at bad
        exact Bool.noConfusion bad
      simp only [marked,Finset.mem_insert,Finset.mem_singleton] at mem
      rcases mem with rfl | rfl
      · exact Or.inr (Or.inl ⟨(pj e).mp hit,v,ev,fun z row => safe z ((nj z).mpr row)⟩)
      · exact Or.inr (Or.inr ⟨(pk e).mp hit,v,ev,fun z row => safe z ((nk z).mpr row)⟩)

end G11GuardCircuit
