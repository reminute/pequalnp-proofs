import Std

namespace Petersen3831

def edges : List Nat := [3, 6, 12, 24, 17, 33, 66, 132, 264, 160, 320, 288]
def target (m : Nat) : Bool := edges.any fun e => m &&& e == e
def sensitive (m : Nat) : Bool := !m.testBit 0 && target m != target (m ||| 1)

def witnesses : List (Nat × Nat × Nat) :=
  [(1,16,2), (2,2,20), (3,2,10), (4,2,16), (5,2,32), (6,2,80), (7,2,130), (8,2,258)]

set_option maxRecDepth 8192 in
theorem count_sensitive : ((List.range 512).filter sensitive).length = 32 := by decide

theorem both_values : ∀ a : Fin 8, ∃ w ∈ witnesses,
    w.1 = a.val+1 ∧ sensitive w.2.1 = true ∧ sensitive w.2.2 = true ∧
    w.2.1.testBit w.1 = false ∧ w.2.2.testBit w.1 = true := by decide

end Petersen3831
