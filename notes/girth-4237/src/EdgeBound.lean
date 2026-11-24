import EdgeFormula
import EdgeNegatives

namespace GirthEdgeBound

open PEqualNP.MetaComplexity.NestedCover
open GirthRank GirthEdgeNegatives

variable {n : ℕ} {G : SimpleGraph (Fin n)}

def edgeRows (S : Finset (Sym2 (Fin n))) : Finset (Finset (Fin n)) := S.image Sym2.toFinset

theorem rows_card (S : Finset (Sym2 (Fin n))) : (edgeRows S).card = S.card := by
  apply Finset.card_image_of_injective
  intro e f same
  apply Sym2.ext
  intro v
  rw [← Sym2.mem_toFinset,← Sym2.mem_toFinset,same]

variable [DecidableRel G.Adj] {S : Finset (Sym2 (Fin n))}

theorem row_shape (sub : S ⊆ G.edgeFinset) {r : Finset (Fin n)} (hr : r ∈ edgeRows S) :
    ∃ u v, r = {u,v} ∧ G.Adj u v := by
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hr
  induction e using Sym2.inductionOn with
  | _ u v =>
    exact ⟨u,v,Sym2.toFinset_mk_eq,SimpleGraph.mem_edgeFinset.mp (sub he)⟩

theorem row_two (sub : S ⊆ G.edgeFinset) (r : Finset (Fin n)) (hr : r ∈ edgeRows S) : r.card = 2 := by
  obtain ⟨u,v,rfl,uv⟩ := row_shape sub hr
  simp [uv.ne]

theorem row_adj (sub : S ⊆ G.edgeFinset) (r : Finset (Fin n)) (hr : r ∈ edgeRows S) :
    ∀ u ∈ r, ∀ v ∈ r, u ≠ v → G.Adj u v := by
  obtain ⟨u,v,rfl,uv⟩ := row_shape sub hr
  have clique : G.IsClique (↑({u,v} : Finset (Fin n)) : Set (Fin n)) := by
    simpa [uv.ne] using uv
  exact fun _ hx _ hy diff => clique hx hy diff

theorem positive_on (sub : S ⊆ G.edgeFinset) (e : ↥(edgeRows S)) :
    graphFun G ∅ (positive (edgeRows S) e) = true := by
  obtain ⟨u,v,eq,uv⟩ := row_shape sub e.property
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,
    decide_eq_true_eq,positive]
  exact ⟨u,v,uv,by simp [eq],by simp [eq]⟩

theorem negative_off (sub : S ⊆ G.edgeFinset) (girth : GirthFive G) (y : Fin n ⊕ ↥(edgeRows S)) :
    graphFun G ∅ (negative (edgeRows S) G.Adj y) = false := by
  have shape : (∃ v, columnSet (edgeRows S) y = {v}) ∨
      ∃ u v, columnSet (edgeRows S) y = {u,v} ∧ G.Adj u v := by
    cases y with
    | inl v => exact Or.inl ⟨v,rfl⟩
    | inr e => exact Or.inr (row_shape sub e.property)
  convert outer_graphFun girth _ shape using 2
  funext v
  apply Bool.eq_iff_iff.mpr
  simp [negative]

def sampleBlock (S : Finset (Sym2 (Fin n))) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool) :=
  PlaneKW.block (mat (edgeRows S)) (fun e => f (positive (edgeRows S) e))
    (fun y => !(f (negative (edgeRows S) G.Adj y)))

theorem raw_rank (sub : S ⊆ G.edgeFinset) (v : Fin n) : (sampleBlock S G (fun x => x v)).rank ≤ 1 := by
  apply leaf_rank (edgeRows S) G.Adj (row_adj sub) v
  · exact fun _ h => h
  · intro y h
    simpa using h

theorem output_rank (sub : S ⊆ G.edgeFinset) (girth : GirthFive G) :
    S.card ≤ (sampleBlock S G (graphFun G ∅)).rank := by
  have all : sampleBlock S G (graphFun G ∅) = mat (edgeRows S) := by
    ext e y
    simp [sampleBlock,PlaneKW.block,positive_on sub,negative_off sub girth]
  rw [all,← rows_card]
  exact rows_independent _ (row_two sub)

theorem formula_lower (sub : S ⊆ G.edgeFinset) (girth : GirthFive G) (t : PlaneFormula (Fin n))
    (computes : ∀ x, t.eval x = graphFun G ∅ x) : S.card ≤ t.leaves.length := by
  rw [← rows_card]
  apply GirthRank.formula_lower (edgeRows S) G.Adj (row_two sub) (row_adj sub) t
  · intro e
    rw [computes,positive_on sub]
  · intro y
    rw [computes,negative_off sub girth]

end GirthEdgeBound
