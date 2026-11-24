import SlotCount

namespace Rect4123.TwoEdges

open PEqualNP.MetaComplexity Rect4123.LiftRow

/-- The four coordinates are a, b, c and d. The graph edges are ab and cd. -/
def f (x : Input 4) : Bool := (x 0 && x 1) || (x 2 && x 3)

def first (x : Input 4) : Bool := x 0 && x 1
def second (x : Input 4) : Bool := f x && !(first x)

def A (j : Fin 6) (x : Input 4) : Bool :=
  match j.val with
  | 0 => first x
  | 1 => first x && x 2
  | 2 => first x && !(x 2)
  | 3 => first x
  | _ => second x

def B (j : Fin 6) (y : Input 4) : Bool :=
  !(f y) && match j.val with
  | 0 => !(y 0) && !(y 2)
  | 1 | 2 => !(y 0) && y 2
  | 3 => y 0
  | 4 => !(y 2)
  | _ => y 2

def pos (j : Fin 6) : ℕ :=
  match j.val with
  | 0 | 1 => 0
  | 2 | 4 => 2
  | 3 => 1
  | _ => 3

def sign (j : Fin 6) : Bool := decide (j ≠ 2)
def D : Finset (Fin 6) := {1}

-- Rectangles are numbered 0 through 5. Rectangle 2 has the negative literal ¬c.
def xAB (i : Fin 4) : Bool := decide (i=0 ∨ i=1)
def yC (i : Fin 4) : Bool := decide (i=2)

theorem negative_cell :
    f xAB=true ∧ f yC=false ∧ sign 2=false ∧ pos 2=2 ∧
    A 2 xAB=true ∧ B 2 yC=true ∧ xAB 2=false ∧ yC 2=true := by decide

theorem unstable_positive :
    sign 1=true ∧ B 1 yC=true ∧ A 1 xAB=false ∧ A 1 (Function.update xAB 2 true)=true := by decide

theorem essential_c : ∃ x : Input 4, f x=false ∧ f (Function.update x 2 true)=true := by
  exact ⟨fun i => decide (i=3),by decide⟩

theorem every_part_used : ∀ j, ∃ x y, A j x=true ∧ B j y=true := by
  let rowMask : Fin 6 → ℕ := ![3,7,3,3,12,12]
  let colMask : Fin 6 → ℕ := ![0,4,4,1,0,4]
  let bits (m : ℕ) (i : Fin 4) := m.testBit i.val
  have works : ∀ j, A j (bits (rowMask j))=true ∧ B j (bits (colMask j))=true := by decide
  exact fun j => ⟨_,_,works j⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem partition : IsLiteralPartition 4 f 6 A B pos sign := by
  refine ⟨?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · unfold ExistsUnique
    decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem stable : ∀ j, sign j=true → j∉D → ∀ x y, f x=true → B j y=true → y 2=true →
    A j (Function.update x 2 true)=A j x := by decide +kernel

theorem capacity : Fintype.card (Slots sign D) = 6 := by
  rw [slot_count]
  decide

theorem repaired : ∃ A' B' pos', IsLiteralPartition 4 f 6 A' B' pos' (fun _ => true) := by
  apply repair (2 : Fin 4) f A B pos sign partition _ _ D stable capacity.le
  · decide +kernel
  · decide

end Rect4123.TwoEdges

#print axioms Rect4123.TwoEdges.partition
#print axioms Rect4123.TwoEdges.repaired
