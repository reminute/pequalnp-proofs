import PEqualNP.Defs
import NeighborCube

namespace Cubic1971.GraphStar

open NeighborCube

def input {n : Nat} (v : Fin n) (leaf : Fin 3 → Fin n) (x : Bool) (s : Bits)
    (u : Fin n) : Bool :=
  decide ((u = v ∧ x = true) ∨ ∃ i, u = leaf i ∧ s i = true)

private theorem any_on (s : Bits) : anyNeighbor s = true ↔ ∃ i, s i = true := by
  simp only [anyNeighbor, Bool.or_eq_true]
  constructor
  · rintro ((h | h) | h)
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
  · rintro ⟨i,hi⟩
    have choice : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases choice with rfl | rfl | rfl <;> tauto

theorem evaluates {n : Nat} (G : SimpleGraph (Fin n)) (U : Finset (Fin n))
    (f : (Fin n → Bool) → Bool)
    (spec : ∀ t, f t = true ↔ (∃ u ∈ U, t u = true) ∨
       ∃ a b, G.Adj a b ∧ t a = true ∧ t b = true)
    (unmarked : ∀ a b, G.Adj a b → a ∉ U)
    (v : Fin n) (leaf : Fin 3 → Fin n) (star : ∀ i, G.Adj v (leaf i))
    (independent : ∀ i j, ¬ G.Adj (leaf i) (leaf j)) (s : Bits) (x : Bool) :
    f (input v leaf x s) = (x && anyNeighbor s) := by
  apply Bool.eq_iff_iff.mpr
  rw [spec, Bool.and_eq_true, any_on]
  simp only [input,decide_eq_true_eq]
  constructor
  · rintro (⟨u,mark,ev⟩ | ⟨a,b,edge,evA,evB⟩)
    · rcases ev with ⟨rfl,_⟩ | ⟨i,rfl,_⟩
      · exact (unmarked _ _ (star 0) mark).elim
      · exact (unmarked _ _ (star i).symm mark).elim
    · rcases evA with ⟨rfl,on⟩ | ⟨i,rfl,lit⟩ <;>
        rcases evB with ⟨rfl,on'⟩ | ⟨j,rfl,lit'⟩
      · exact (G.loopless.irrefl _ edge).elim
      · exact ⟨on,j,lit'⟩
      · exact ⟨on',i,lit⟩
      · exact (independent i j edge).elim
  · rintro ⟨on,i,lit⟩
    exact Or.inr ⟨v, leaf i, star i, Or.inl ⟨rfl,on⟩, Or.inr ⟨i,rfl,lit⟩⟩

theorem evaluates_reader {n : Nat} (G : SimpleGraph (Fin n)) (U : Finset (Fin n))
    (f : (Fin n → Bool) → Bool)
    (spec : ∀ t, f t = true ↔ (∃ u ∈ U, t u = true) ∨
       ∃ a b, G.Adj a b ∧ t a = true ∧ t b = true)
    (unmarked : ∀ a b, G.Adj a b → a ∉ U)
    (v : Fin n) (leaf : Fin 3 → Fin n) (star : ∀ i, G.Adj v (leaf i))
    (independent : ∀ i j, ¬ G.Adj (leaf i) (leaf j)) (s : Bits) (x : Bool) :
    f (fun w => if w = v then x else decide (∃ i : Fin 3, leaf i = w ∧ s i = true)) =
      (x && anyNeighbor s) := by
  have rowEq : (fun w => if w = v then x else decide (∃ i : Fin 3, leaf i = w ∧ s i = true))
      = input v leaf x s := by
    funext w
    by_cases h : w = v
    · subst w
      have no : ¬ ∃ i, v = leaf i ∧ s i = true := by
        rintro ⟨i,eq,_⟩
        exact G.loopless.irrefl _ (eq ▸ star i)
      cases x <;> simp [input, no]
    · simp only [input,h,↓reduceIte,false_and,false_or]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor <;> rintro ⟨i,hi,lit⟩ <;> exact ⟨i,hi.symm,lit⟩
  rw [rowEq]
  exact evaluates G U f spec unmarked v leaf star independent s x

theorem branches {n : Nat} (G : SimpleGraph (Fin n)) (v : Fin n)
    (degree : (G.neighborSet v).ncard = 3)
    (girth : ∀ w (p : G.Walk w w), p.IsCycle → 7 ≤ p.length) :
    ∃ leaf : Fin 3 → Fin n, Function.Injective leaf ∧
      (∀ i, G.Adj v (leaf i)) ∧ (∀ i j, ¬G.Adj (leaf i) (leaf j)) := by
  classical
  have count : Fintype.card (G.neighborSet v) = 3 := by
    simpa only [Set.ncard_eq_toFinset_card',Set.toFinset_card] using degree
  let e := (Fintype.equivFinOfCardEq count).symm
  let leaf := fun i : Fin 3 => (e i).val
  have star (i) : G.Adj v (leaf i) := (e i).property
  refine ⟨leaf,Subtype.val_injective.comp e.injective,star,?_⟩
  intro i j edge
  have va := G.ne_of_adj (star i)
  have vb := G.ne_of_adj (star j)
  have ab := G.ne_of_adj edge
  let p := SimpleGraph.Walk.cons (star i) (.cons edge (.cons (star j).symm .nil))
  have cyc : p.IsCycle := by
    change (SimpleGraph.Walk.cons (star i) (.cons edge (.cons (star j).symm .nil))).IsCycle
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    constructor
    · simp [SimpleGraph.Walk.cons_isPath_iff, ab, Ne.symm va, Ne.symm vb]
    · simp [va, vb, ab, Ne.symm va]
  have long := girth v p cyc
  change 7 ≤ 3 at long
  omega

end Cubic1971.GraphStar

#print axioms Cubic1971.GraphStar.evaluates
#print axioms Cubic1971.GraphStar.evaluates_reader
#print axioms Cubic1971.GraphStar.branches
