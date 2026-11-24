import EdgeNegatives

namespace Rect4123.Cell

open SimpleGraph GirthEdgeNegatives

/-- The label condition in the posted rectangle problem, for a fixed column. -/
def allowed {n : ℕ} (H : SimpleGraph (Fin n)) (c d z : Fin n) : Prop :=
  ¬ ((H.Adj c z ∨ H.Adj d z) ∧ z ≠ c ∧ z ≠ d)

theorem cell {n : ℕ} (H : SimpleGraph (Fin n)) (girth : GirthFive H)
    {a b c d : Fin n} (row : H.Adj a b) (column : c=d ∨ H.Adj c d) :
    ∃ z : Fin n, (z=a ∨ z=b) ∧ allowed H c d z := by
  classical
  let S : Finset (Fin n) := {c,d}
  have clique : H.IsClique (S : Set (Fin n)) := by
    rcases column with rfl | cd
    · simp [S]
    · simpa [S,cd.ne] using cd
  have independent := outer_independent_of_clique girth S clique
  have forbidden (z : Fin n) (no : ¬ allowed H c d z) : z ∈ outer H S := by
    have cut : (H.Adj c z ∨ H.Adj d z) ∧ z≠c ∧ z≠d := Classical.byContradiction no
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,by simp [S,cut.2.1,cut.2.2],?_⟩
    rcases cut.1 with cz | dz
    · exact ⟨c,by simp [S],cz.symm⟩
    · exact ⟨d,by simp [S],dz.symm⟩
  by_cases left : allowed H c d a
  · exact ⟨a,Or.inl rfl,left⟩
  · refine ⟨b,Or.inr rfl,?_⟩
    by_contra right
    exact independent (forbidden a left) (forbidden b right) row.ne row

theorem girth_of_subgraph {n : ℕ} {G H : SimpleGraph (Fin n)} (sub : H ≤ G)
    (girth : ∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) : GirthFive H := by
  have hG : 5 ≤ G.egirth := by
    apply le_egirth.mpr
    intro v p cycle
    exact_mod_cast (le_trans (by decide : 5 ≤ 7) (girth v p cycle))
  have hH : 5 ≤ H.egirth := hG.trans (egirth_anti sub)
  intro v p cycle
  exact_mod_cast (le_egirth.mp hH v p cycle)

/-- The graph in the desk statement deletes every edge incident to one vertex. -/
theorem after_deletion {n : ℕ} (G H : SimpleGraph (Fin n)) (v : Fin n)
    (girth : ∀ u (p : G.Walk u u), p.IsCycle → 7 ≤ p.length)
    (deleted : H = G.deleteEdges (G.incidenceSet v))
    (a b c d : Fin n) (row : H.Adj a b) (column : c=d ∨ H.Adj c d) :
    ∃ z : Fin n, (z=a ∨ z=b) ∧ ¬ ((H.Adj c z ∨ H.Adj d z) ∧ z≠c ∧ z≠d) := by
  have sub : H ≤ G := deleted ▸ SimpleGraph.deleteEdges_le _
  exact cell H (girth_of_subgraph sub girth) row column

end Rect4123.Cell

#print axioms Rect4123.Cell.after_deletion
