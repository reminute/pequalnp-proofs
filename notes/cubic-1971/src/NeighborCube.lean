import Std

namespace Cubic1971.NeighborCube

abbrev Bits := Fin 3 → Bool
def anyNeighbor (s : Bits) : Bool := s 0 || s 1 || s 2
def blank : Bits := fun _ => false

private theorem empty_face (s : Bits) (h : anyNeighbor s = false) : s = blank := by
  have off : (s 0 = false ∧ s 1 = false) ∧ s 2 = false := by simpa [anyNeighbor] using h
  funext i
  have one : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases one with rfl | rfl | rfl
  · exact off.1.1
  · exact off.1.2
  · exact off.2

/-- On a three-neighbor star the graph output with centre x is x AND anyNeighbor.
If the centre reaches the suffix only through one AND (respectively OR),
the partner and suffix can depend arbitrarily on all three other bits. -/
theorem classified (partner : Bits → Bool) (suffix : Bits → Bool → Bool) (readerIsAnd : Bool)
    (works : ∀ s x, suffix s (if readerIsAnd then x && partner s else x || partner s) =
      (x && anyNeighbor s)) :
    (∀ s, partner s = readerIsAnd) ∨
    (∀ s, partner s = if readerIsAnd then anyNeighbor s else !(anyNeighbor s)) := by
  have enabled (s : Bits) (active : anyNeighbor s = true) : partner s = readerIsAnd := by
    have lo := works s false
    have hi := works s true
    cases readerIsAnd <;> cases e : partner s <;> simp_all
  by_cases root : partner blank = readerIsAnd
  · left
    intro s
    cases h : anyNeighbor s with
    | false => simpa only [empty_face s h] using root
    | true => exact enabled s h
  · right
    intro s
    cases h : anyNeighbor s with
    | false =>
      rw [empty_face s h]
      cases readerIsAnd <;> cases v : partner blank <;> simp_all
    | true => rw [enabled s h]; cases readerIsAnd <;> rfl

end Cubic1971.NeighborCube

#print axioms Cubic1971.NeighborCube.classified
