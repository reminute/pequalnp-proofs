import Cell
import Mathlib.Combinatorics.SimpleGraph.VertexCover

namespace Rect4123.Obstruction

open Rect4123.Cell

variable {n : ℕ} {ι : Type*} {H : SimpleGraph (Fin n)}
variable {R S : ι → Fin n → Fin n → Prop} {label : ι → Fin n}

/-- The exact coverage and labeling clauses, allowing any type of rectangle indices. -/
def Valid (H : SimpleGraph (Fin n)) (R S : ι → Fin n → Fin n → Prop) (label : ι → Fin n) : Prop :=
  ∀ a b c d, H.Adj a b → c=d ∨ H.Adj c d →
    (∃! i, R i a b ∧ S i c d) ∧
    ∀ i, R i a b → S i c d → (label i=a ∨ label i=b) ∧ allowed H c d (label i)

def Repeated (label : ι → Fin n) (u : Fin n) : Prop :=
  ∃ i j, i ≠ j ∧ label i=u ∧ label j=u

private theorem force_left (valid : Valid H R S label) {a b c d : Fin n}
    (ab : H.Adj a b) (col : c=d ∨ H.Adj c d) (forbid : ¬allowed H c d b) :
    ∃ i, R i a b ∧ S i c d ∧ label i=a := by
  obtain ⟨one,law⟩ := valid a b c d ab col
  obtain ⟨i,ri,si⟩ := one.exists
  obtain ⟨ends,yes⟩ := law i ri si
  exact ⟨i,ri,si,ends.resolve_right (fun e => forbid (e ▸ yes))⟩

/-- Singleton columns at the endpoints activate rectangles carrying both labels on
the central row. These may belong to different columns. -/
theorem both_on_row (valid : Valid H R S label) {u v : Fin n} (uv : H.Adj u v) :
    (∃ i, R i u v ∧ S i u u ∧ label i=u) ∧
    (∃ j, R j u v ∧ S j v v ∧ label j=v) := by
  constructor
  · exact force_left valid uv (Or.inl rfl) (fun yes => yes ⟨Or.inl uv,uv.ne.symm,uv.ne.symm⟩)
  · obtain ⟨one,law⟩ := valid u v v v uv (Or.inl rfl)
    obtain ⟨j,rj,sj⟩ := one.exists
    obtain ⟨ends,yes⟩ := law j rj sj
    refine ⟨j,rj,sj,ends.resolve_left (fun e => ?_)⟩
    rw [e] at yes
    exact yes ⟨Or.inl uv.symm,uv.ne,uv.ne⟩

/-- Repeated labels cover each edge whose endpoints each have a second neighbor.
No distinctness between the two outside neighbors is needed. -/
theorem repeat_on_edge (valid : Valid H R S label) {u v a b : Fin n}
    (uv : H.Adj u v) (ua : H.Adj u a) (av : a≠v) (vb : H.Adj v b) (bu : b≠u) :
    Repeated label u ∨ Repeated label v := by
  obtain ⟨⟨i,ri,_,li⟩,⟨j,rj,_,lj⟩⟩ := both_on_row valid uv
  obtain ⟨i',_,si,li'⟩ := force_left valid ua (Or.inr uv)
    (fun yes => yes ⟨Or.inl ua,ua.ne.symm,av⟩)
  obtain ⟨j',_,sj,lj'⟩ := force_left valid vb (Or.inr uv)
    (fun yes => yes ⟨Or.inr vb,bu,vb.ne.symm⟩)
  by_cases left : i=i'
  · by_cases right : j=j'
    · subst i'; subst j'
      obtain ⟨k,_,unique⟩ := (valid u v u v uv (Or.inr uv)).1
      have eq : i=j := (unique i ⟨ri,si⟩).trans (unique j ⟨rj,sj⟩).symm
      exact (uv.ne (li.symm.trans ((congrArg label eq).trans lj))).elim
    · exact Or.inr ⟨j,j',right,lj,lj'⟩
  · exact Or.inl ⟨i,i',left,li,li'⟩

theorem repeat_of_degrees (valid : Valid H R S label) {u v : Fin n} (uv : H.Adj u v)
    (du : 2 ≤ (H.neighborSet u).ncard) (dv : 2 ≤ (H.neighborSet v).ncard) :
    Repeated label u ∨ Repeated label v := by
  classical
  have other {x y : Fin n} (xy : H.Adj x y) (deg : 2 ≤ (H.neighborSet x).ncard) :
      ∃ z, H.Adj x z ∧ z≠y := by
    have card : 2 ≤ (H.neighborFinset x).card := by
      change 2 ≤ H.degree x
      rwa [← H.ncard_neighborSet]
    have mem : y ∈ H.neighborFinset x := (H.mem_neighborFinset x y).mpr xy
    have nonempty : 0 < ((H.neighborFinset x).erase y).card := by
      rw [Finset.card_erase_of_mem mem]; omega
    obtain ⟨z,mz⟩ := Finset.card_pos.mp nonempty
    obtain ⟨ne,adj⟩ := Finset.mem_erase.mp mz
    exact ⟨z,(H.mem_neighborFinset x z).mp adj,ne⟩
  obtain ⟨a,ua,av⟩ := other uv du
  obtain ⟨b,vb,bu⟩ := other uv.symm dv
  exact repeat_on_edge valid uv ua av vb bu

/-- A vertex still incident to an edge after this deletion has lost at most one
of its three neighbors. The deleted vertex itself is now isolated. -/
theorem survivor_degree {G H : SimpleGraph (Fin n)} (z : Fin n)
    (degrees : ∀ x : Fin n, (G.neighborSet x).ncard=0 ∨ (G.neighborSet x).ncard=3)
    (deleted : H = G.deleteEdges (G.incidenceSet z)) {u v : Fin n} (uv : H.Adj u v) :
    2 ≤ (H.neighborSet u).ncard := by
  classical
  have adj (a b : Fin n) : H.Adj a b ↔ G.Adj a b ∧ a≠z ∧ b≠z := by
    rw [deleted]
    exact SimpleGraph.deleteIncidenceSet_adj
  obtain ⟨original,uz,_⟩ := (adj u v).mp uv
  have before : (G.neighborFinset u).card=3 := by
    have positive : 0 < (G.neighborFinset u).card :=
      Finset.card_pos.mpr ⟨v,(G.mem_neighborFinset u v).mpr original⟩
    have alternatives := degrees u
    rw [G.ncard_neighborSet] at alternatives
    exact alternatives.resolve_left (Nat.ne_of_gt positive)
  have neighbors : H.neighborFinset u = (G.neighborFinset u).erase z := by
    ext w
    simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset, adj]
    tauto
  rw [H.ncard_neighborSet]
  change 2 ≤ (H.neighborFinset u).card
  rw [neighbors]
  by_cases had : z ∈ G.neighborFinset u
  · rw [Finset.card_erase_of_mem had,before]
  · rw [Finset.erase_eq_of_notMem had,before]
    decide

/-- For the graph of the posted problem the vertices labeling at least two
distinct rectangles cover every surviving edge. -/
theorem cover_after_deletion {G H : SimpleGraph (Fin n)} (z : Fin n)
    (degrees : ∀ x : Fin n, (G.neighborSet x).ncard=0 ∨ (G.neighborSet x).ncard=3)
    (deleted : H = G.deleteEdges (G.incidenceSet z)) (valid : Valid H R S label) :
    H.IsVertexCover {u | Repeated label u} := by
  intro u v uv
  exact repeat_of_degrees valid uv (survivor_degree z degrees deleted uv)
    (survivor_degree z degrees deleted uv.symm)

end Rect4123.Obstruction

#print axioms Rect4123.Obstruction.repeat_of_degrees
#print axioms Rect4123.Obstruction.cover_after_deletion
