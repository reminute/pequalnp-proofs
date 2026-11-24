import Mathlib
import PEqualNP.Defs

namespace GirthEdgeNegatives

open SimpleGraph
open PEqualNP.MetaComplexity.NestedCover

variable {n : ℕ} {G : SimpleGraph (Fin n)}

abbrev GirthFive (G : SimpleGraph (Fin n)) : Prop :=
  ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length

theorem no_triangle (girth : GirthFive G) {a b c : Fin n}
    (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a) : False := by
  let p : G.Walk a a := .cons ab (.cons bc (.cons ca .nil))
  have cyc : p.IsCycle := by
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    simp [p,Walk.isPath_def,ab.ne.symm,bc.ne,ca.ne]
  have bad := girth a p cyc
  simp [p] at bad

theorem no_square (girth : GirthFive G) {a b c d : Fin n}
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d) (da : G.Adj d a)
    (ac : a ≠ c) (bd : b ≠ d) : False := by
  let p : G.Walk a a := .cons ab (.cons bc (.cons cd (.cons da .nil)))
  have cyc : p.IsCycle := by
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    simp [p,Walk.isPath_def,ab.ne.symm,bc.ne,cd.ne,da.ne,ac.symm,bd]
  have bad := girth a p cyc
  simp [p] at bad

theorem vertex_neighbors_independent (girth : GirthFive G) (v : Fin n) :
    G.IsIndepSet (G.neighborSet v) := by
  intro a ha b hb _ edge
  exact no_triangle girth ha edge (show G.Adj v b from hb).symm

def outer (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun z => z ∉ x ∧ ∃ w ∈ x, G.Adj z w

variable [DecidableRel G.Adj]

theorem outer_independent_of_clique (girth : GirthFive G) (x : Finset (Fin n))
    (clique : G.IsClique (x : Set (Fin n))) : G.IsIndepSet (outer G x : Set (Fin n)) := by
  intro a ha b hb _ edge
  obtain ⟨aOut,p,hp,ap⟩ := (Finset.mem_filter.mp ha).2
  obtain ⟨bOut,q,hq,bq⟩ := (Finset.mem_filter.mp hb).2
  by_cases same : p=q
  · subst q
    exact no_triangle girth ap bq.symm edge.symm
  · have aq : a ≠ q := fun eq => aOut (eq ▸ hq)
    have pb : p ≠ b := fun eq => bOut (eq ▸ hp)
    exact no_square girth ap (clique hp hq same) bq.symm edge.symm aq pb

theorem edge_neighbors_independent (girth : GirthFive G) {u v : Fin n} (uv : G.Adj u v) :
    G.IsIndepSet (outer G {u,v} : Set (Fin n)) :=
  outer_independent_of_clique girth {u,v} (by simpa [uv.ne] using uv)

theorem outer_graphFun (girth : GirthFive G) (x : Finset (Fin n))
    (shape : (∃ v, x = {v}) ∨ ∃ u v, x = {u,v} ∧ G.Adj u v) :
    graphFun G ∅ (fun z => decide (z ∉ x ∧ ∃ w ∈ x, G.Adj z w)) = false := by
  have clique : G.IsClique (x : Set (Fin n)) := by
    rcases shape with ⟨v,rfl⟩ | ⟨u,v,rfl,uv⟩
    · simp
    · simpa [uv.ne] using uv
  have indep := outer_independent_of_clique girth x clique
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,
    decide_eq_false_iff_not,decide_eq_true_eq]
  rintro ⟨a,b,adj,ha,hb⟩
  exact indep (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩) adj.ne adj

end GirthEdgeNegatives
