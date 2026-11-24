import GraphDensity
import EdgeNegatives

namespace Edge606.TwinGraph

open GraphDensity GirthEdgeNegatives

variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

def Twins (u v : Fin n) : Prop :=
  ∀ w, w ≠ u → w ≠ v → (G.Adj u w ↔ G.Adj v w)

private def pair (a b i : Fin n) := decide (i = a ∨ i = b)

private theorem pair_iff (a b : Fin n) : edgeFunction G (pair a b) = true ↔ G.Adj a b := by
  simp only [edgeFunction,pair,decide_eq_true_eq]
  constructor
  · rintro ⟨i,j,ij,hi,hj⟩
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      first | exact ij | exact ij.symm | exact (G.irrefl ij).elim
  · intro ab
    exact ⟨a,b,ab,Or.inl rfl,Or.inr rfl⟩

theorem twins_of_swap {u v : Fin n} (uv : u ≠ v)
    (symmetry : ∀ x : Fin n → Bool, edgeFunction G (x ∘ Equiv.swap u v) = edgeFunction G x) :
    Twins G u v := by
  intro w wu wv
  have flip : pair u w ∘ Equiv.swap u v = pair v w := by
    funext z
    by_cases zu : z = u
    · subst z; simp [pair,uv,wu.symm,uv.symm,wv.symm]
    by_cases zv : z = v
    · subst z; simp [pair]
    simp [pair,Equiv.swap_apply_of_ne_of_ne zu zv,zu,zv]
  have equal := symmetry (pair u w)
  rw [flip] at equal
  rw [← pair_iff G u w,← pair_iff G v w,equal]

theorem swap_of_twins {u v : Fin n} (twins : Twins G u v) (x : Fin n → Bool) :
    edgeFunction G (x ∘ Equiv.swap u v) = edgeFunction G x := by
  have left (w : Fin n) (uw : G.Adj u w) : G.Adj v (Equiv.swap u v w) := by
    by_cases eq : w = v
    · subst w; simpa using uw.symm
    rw [Equiv.swap_apply_of_ne_of_ne uw.ne.symm eq]
    exact (twins w uw.ne.symm eq).mp uw
  have right (w : Fin n) (vw : G.Adj v w) : G.Adj u (Equiv.swap u v w) := by
    by_cases eq : w = u
    · subst w; simpa using vw.symm
    rw [Equiv.swap_apply_of_ne_of_ne eq vw.ne.symm]
    exact (twins w eq vw.ne.symm).mpr vw
  have preserves (a b : Fin n) (ab : G.Adj a b) : G.Adj (Equiv.swap u v a) (Equiv.swap u v b) := by
    by_cases au : a = u
    · subst a; simpa using left b ab
    by_cases av : a = v
    · subst a; simpa using right b ab
    by_cases bu : b = u
    · subst b; simpa using (left a ab.symm).symm
    by_cases bv : b = v
    · subst b; simpa using (right a ab.symm).symm
    simpa only [Equiv.swap_apply_of_ne_of_ne au av,Equiv.swap_apply_of_ne_of_ne bu bv] using ab
  apply Bool.eq_iff_iff.mpr
  simp only [edgeFunction,decide_eq_true_eq,Function.comp_apply]
  constructor
  · rintro ⟨a,b,ab,xa,xb⟩
    exact ⟨_,_,preserves a b ab,xa,xb⟩
  · rintro ⟨a,b,ab,xa,xb⟩
    exact ⟨_,_,preserves a b ab,by simpa using xa,by simpa using xb⟩

/-- In girth at least five the two vertices are isolated, are the endpoints
    of an isolated edge, or are leaves with a common neighbor. -/
theorem classify (girth : GirthFive G) {u v : Fin n} (uv : u ≠ v) (twins : Twins G u v) :
    (G.neighborFinset u = ∅ ∧ G.neighborFinset v = ∅) ∨
    (G.neighborFinset u = {v} ∧ G.neighborFinset v = {u}) ∨
    ∃ w, w ≠ u ∧ w ≠ v ∧ G.neighborFinset u = {w} ∧ G.neighborFinset v = {w} := by
  classical
  by_cases adjacent : G.Adj u v
  · right; left
    have isolate {a b : Fin n} (ab : G.Adj a b) (same : Twins G a b) : G.neighborFinset a = {b} := by
      ext t
      simp only [SimpleGraph.mem_neighborFinset,Finset.mem_singleton]
      constructor
      · intro at'
        by_contra tb
        exact no_triangle girth ab ((same t at'.ne.symm tb).mp at') at'.symm
      · rintro rfl; exact ab
    exact ⟨isolate adjacent twins,isolate adjacent.symm (fun w wv wu => (twins w wu wv).symm)⟩
  · have same (w : Fin n) : G.Adj u w ↔ G.Adj v w := by
      by_cases wu : w = u
      · subst w; simp only [SimpleGraph.irrefl,false_iff]; exact fun e => adjacent e.symm
      by_cases wv : w = v
      · subst w; simp [adjacent]
      exact twins w wu wv
    have eq : G.neighborFinset u = G.neighborFinset v := by
      ext w; simpa only [SimpleGraph.mem_neighborFinset] using same w
    by_cases live : (G.neighborFinset u).Nonempty
    · obtain ⟨w,member⟩ := live
      have uw := (G.mem_neighborFinset u w).mp member
      have vw := (same w).mp uw
      have one : G.neighborFinset u = {w} := by
        ext a
        simp only [SimpleGraph.mem_neighborFinset,Finset.mem_singleton]
        constructor
        · intro ua
          by_contra aw
          exact no_square girth uw vw.symm ((same a).mp ua) ua.symm uv (Ne.symm aw)
        · rintro rfl; exact uw
      exact Or.inr (Or.inr ⟨w,uw.ne.symm,vw.ne.symm,one,eq.symm.trans one⟩)
    · have empty := Finset.not_nonempty_iff_eq_empty.mp live
      exact Or.inl ⟨empty,eq.symm.trans empty⟩

theorem degree_le_one_of_swap (girth : GirthFive G) {u v : Fin n} (uv : u ≠ v)
    (symmetry : ∀ x : Fin n → Bool, edgeFunction G (x ∘ Equiv.swap u v) = edgeFunction G x) :
    G.degree u ≤ 1 ∧ G.degree v ≤ 1 := by
  rw [← G.card_neighborFinset_eq_degree u,← G.card_neighborFinset_eq_degree v]
  rcases classify G girth uv (twins_of_swap G uv symmetry) with h | h | ⟨w,_,_,h⟩
  all_goals simp [h.1,h.2]

end Edge606.TwinGraph

#print axioms Edge606.TwinGraph.twins_of_swap
#print axioms Edge606.TwinGraph.swap_of_twins
#print axioms Edge606.TwinGraph.classify
#print axioms Edge606.TwinGraph.degree_le_one_of_swap
