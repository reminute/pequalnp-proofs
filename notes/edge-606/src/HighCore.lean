import CorePeel

namespace Edge606.HighCore

open Finset SimpleGraph GirthFiveCore

variable {n : Nat}

/-- Keep the original vertex indices, isolating every vertex outside S. -/
def restrict (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj a b := G.Adj a b ∧ a ∈ S ∧ b ∈ S
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

instance (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) :
    DecidableRel (restrict G S).Adj := fun a b =>
  inferInstanceAs (Decidable (G.Adj a b ∧ a ∈ S ∧ b ∈ S))

theorem restrict_le (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : restrict G S ≤ G :=
  fun _ _ h => h.1

/-- Peel an edge set, then restore every original edge between its surviving
    endpoints. This can only improve the surviving degrees and the edge budget. -/
theorem exists_core (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (d : Nat) :
    ∃ S : Finset (Fin n),
      (∀ v ∈ S, d < (restrict G S).degree v) ∧
      (∀ v ∉ S, (restrict G S).degree v = 0) ∧
      G.edgeFinset.card + d * S.card ≤ (restrict G S).edgeFinset.card + d * G.support.toFinset.card := by
  classical
  obtain ⟨T,sub,core,cost⟩ := peel d G.edgeFinset
  let S := ends T
  let H := restrict G S
  have inside : T ⊆ H.edgeFinset := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
      apply SimpleGraph.mem_edgeFinset.mpr
      exact ⟨SimpleGraph.mem_edgeFinset.mp (sub he),
        Finset.mem_filter.mpr ⟨mem_univ _,s(a,b),he,by simp⟩,
        Finset.mem_filter.mpr ⟨mem_univ _,s(a,b),he,by simp⟩⟩
  refine ⟨S,?_,?_,?_⟩
  · intro v hv
    obtain ⟨e,he,ve⟩ := (Finset.mem_filter.mp hv).2
    have alive : (atVertex T v).Nonempty := ⟨e,Finset.mem_filter.mpr ⟨he,ve⟩⟩
    have high := (core v).resolve_left (Nat.ne_of_gt alive.card_pos)
    have inc : atVertex T v ⊆ H.incidenceFinset v := by
      rw [H.incidenceFinset_eq_filter]
      intro e h
      obtain ⟨he,ev⟩ := Finset.mem_filter.mp h
      exact Finset.mem_filter.mpr ⟨inside he,ev⟩
    exact high.trans_le ((Finset.card_le_card inc).trans_eq (H.card_incidenceFinset_eq_degree v))
  · intro v away
    by_contra nonzero
    obtain ⟨w,adj⟩ := (H.degree_pos_iff_mem_support v).mp (Nat.pos_of_ne_zero nonzero)
    exact away adj.2.1
  · rw [ends_edges] at cost
    exact cost.trans (Nat.add_le_add_right (Finset.card_le_card inside) _)

theorem positive_degree_core (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (d : Nat) :
    ∃ S : Finset (Fin n),
      (∀ v, (restrict G S).degree v = 0 ∨ d < (restrict G S).degree v) ∧
      G.edgeFinset.card ≤ (restrict G S).edgeFinset.card + d * G.support.toFinset.card := by
  obtain ⟨S,high,zero,cost⟩ := exists_core G d
  refine ⟨S,fun v => ?_,(Nat.le_add_right _ _).trans cost⟩
  by_cases h : v ∈ S
  · exact Or.inr (high v h)
  · exact Or.inl (zero v h)

end Edge606.HighCore

#print axioms Edge606.HighCore.exists_core
#print axioms Edge606.HighCore.positive_degree_core
