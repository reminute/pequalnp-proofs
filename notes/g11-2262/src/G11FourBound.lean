import G11Sharpness
import G11NineEdges

namespace G11FourClauses

open Finset ClauseWitness G11Certificate

noncomputable def acceptedEdges (clauses : Fin 4 → Finset (Fin 11)) : Finset (Fin 16) :=
  open Classical in univ.filter fun e => accepts clauses (edge e)

theorem upper (clauses : Fin 4 → Finset (Fin 11))
    (reject : ∀ i : Fin 24, ¬ accepts clauses (negative i)) :
    (acceptedEdges clauses).card ≤ 8 := by
  classical
  by_contra! many
  obtain ⟨z, _, clique⟩ := nine_edges (acceptedEdges clauses) (by omega)
  apply incompatibleNegatives clauses (fun i => negative (z i)) (fun i => reject (z i))
  intro i j diff
  obtain ⟨e, mem, sub⟩ := clique i j diff
  exact accepts_mono sub (mem_filter.mp mem).2

theorem sharp : (acceptedEdges exampleClauses).card = 8 := by
  classical
  have cap := upper exampleClauses fun i yes => by
    obtain ⟨e, impossible⟩ := example_sound _ yes
    exact independent_negatives i e impossible
  have covers : eightEdges ⊆ acceptedEdges exampleClauses := by
    intro e he
    exact mem_filter.mpr ⟨mem_univ _,tight_example.2 e he⟩
  have low := card_le_card covers
  rw [tight_example.1] at low
  omega

theorem belowGraph_upper (clauses : Fin 4 → Finset (Fin 11))
    (sound : ∀ X, accepts clauses X → ∃ u ∈ X, ∃ v ∈ X, graph.Adj u v) :
    (acceptedEdges clauses).card ≤ 8 := by
  apply upper
  intro i yes
  obtain ⟨u,hu,v,hv,adj⟩ := sound _ yes
  exact graph_independent i u v hu hv adj

end G11FourClauses
