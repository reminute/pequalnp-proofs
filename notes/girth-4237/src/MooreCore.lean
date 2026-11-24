import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

namespace GirthFiveCore

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

abbrev LongCycles (H : SimpleGraph V) := ∀ v (p : H.Walk v v), p.IsCycle → 5 ≤ p.length

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem noThree (girth : LongCycles G) {a b c : V}
    (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a) : False := by
  let p : G.Walk a a := .cons ab (.cons bc (.cons ca .nil))
  have h : p.IsCycle := by
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    simp [p, Walk.isPath_def, bc.ne,ca.ne,ab.ne.symm]
  have bound := girth a p h
  change 5 ≤ 3 at bound
  omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem noFour (girth : LongCycles G) {a b c d : V}
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d) (da : G.Adj d a)
    (ac : a ≠ c) (bd : b ≠ d) : False := by
  let p : G.Walk a a := .cons ab (.cons bc (.cons cd (.cons da .nil)))
  have h : p.IsCycle := by
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    simp [p, Walk.isPath_def, bc.ne,cd.ne,da.ne,bd,ab.ne.symm,ac.symm]
  have bound := girth a p h
  change 5 ≤ 4 at bound
  omega

/-- The neighbors and distance-two vertices reached through each first neighbor
    occupy disjoint blocks, each as large as the degree of that neighbor. -/
theorem moore_sum (girth : LongCycles G) (v : V) (on : v ∈ G.support) :
    1 + ∑ w ∈ G.neighborFinset v, G.degree w ≤ G.support.toFinset.card := by
  classical
  let block (w : V) := insert w ((G.neighborFinset w).erase v)
  have block_card {w : V} (adj : G.Adj v w) : (block w).card = G.degree w := by
    have hh : v ∈ G.neighborFinset w := (G.mem_neighborFinset _ _).mpr adj.symm
    have self : w ∉ (G.neighborFinset w).erase v := fun h =>
      (G.loopless.irrefl w) ((G.mem_neighborFinset _ _).mp (mem_erase.mp h).2)
    change (insert w ((G.neighborFinset w).erase v)).card = G.degree w
    rw [card_insert_of_notMem self,card_erase_add_one hh,G.card_neighborFinset_eq_degree]
  have pairwise : ∀ w ∈ G.neighborFinset v, ∀ q ∈ G.neighborFinset v, w ≠ q →
      Disjoint (block w) (block q) := by
    intro w hw q hq neq
    have vw := (G.mem_neighborFinset _ _).mp hw
    have vq := (G.mem_neighborFinset _ _).mp hq
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    rcases mem_insert.mp hz with rfl | left
    · rcases mem_insert.mp hz' with eq | right
      · exact neq eq
      · exact noThree girth vw ((G.mem_neighborFinset _ _).mp (mem_erase.mp right).2).symm vq.symm
    · rcases mem_insert.mp hz' with rfl | right
      · exact noThree girth vw ((G.mem_neighborFinset _ _).mp (mem_erase.mp left).2) vq.symm
      · exact noFour girth vw ((G.mem_neighborFinset _ _).mp (mem_erase.mp left).2)
          ((G.mem_neighborFinset _ _).mp (mem_erase.mp right).2).symm vq.symm (mem_erase.mp left).1.symm neq
  let around := (G.neighborFinset v).biUnion block
  have no_center : v ∉ around := by
    intro h
    obtain ⟨w,hw,mem⟩ := mem_biUnion.mp h
    rcases mem_insert.mp mem with rfl | other
    · exact (G.loopless.irrefl v) ((G.mem_neighborFinset _ _).mp hw)
    · exact (mem_erase.mp other).1 rfl
  have incl : insert v around ⊆ G.support.toFinset := by
    intro z hz
    apply Set.mem_toFinset.mpr
    rcases mem_insert.mp hz with rfl | aroundZ
    · exact on
    · obtain ⟨w,hw,mem⟩ := mem_biUnion.mp aroundZ
      rcases mem_insert.mp mem with rfl | other
      · exact ⟨v,((G.mem_neighborFinset _ _).mp hw).symm⟩
      · exact ⟨w,((G.mem_neighborFinset _ _).mp (mem_erase.mp other).2).symm⟩
  have sz := card_le_card incl
  rw [card_insert_of_notMem no_center] at sz
  have exact_count : around.card = ∑ w ∈ G.neighborFinset v, G.degree w := by
    change ((G.neighborFinset v).biUnion block).card = _
    rw [card_biUnion]
    · exact sum_congr rfl (fun w hw => block_card ((G.mem_neighborFinset _ _).mp hw))
    · exact fun _ hw _ hq neq => pairwise _ hw _ hq neq
  omega

/-- A nonempty finite core of minimum positive degree d has at least 1+d²
    incident vertices whenever its girth is at least five. -/
theorem moore_min (girth : LongCycles G) {d : ℕ}
    (minimum : ∀ w ∈ G.support, d ≤ G.degree w) (nonempty : G.support.Nonempty) :
    1 + d*d ≤ G.support.toFinset.card := by
  obtain ⟨v,hv⟩ := nonempty
  have bound := moore_sum girth v hv
  have sep : ∑ _w ∈ G.neighborFinset v, d ≤ ∑ w ∈ G.neighborFinset v, G.degree w := by
    exact sum_le_sum fun w hw => minimum w ⟨v,((G.mem_neighborFinset _ _).mp hw).symm⟩
  simp only [sum_const,nsmul_eq_mul,G.card_neighborFinset_eq_degree] at sep
  exact (Nat.add_le_add_left ((Nat.mul_le_mul_right d (minimum v hv)).trans sep) 1).trans bound

end GirthFiveCore

