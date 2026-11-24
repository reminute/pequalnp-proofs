import SeparatedExample
import SampleLift

namespace Rect4123.ExtensionExample

open SeparatedExample PEqualNP.MetaComplexity

def D : Finset V := {0,2}
def h (x : Input) := f x || (x 0 && x 2)

theorem strict : h (bits 5) = true ∧ f (bits 5) = false := by decide

/-- The two semantic premises of SampleLift.of_extension on all Boolean inputs. -/
theorem extension :
    (∀ x, f x = true → h x = true) ∧
    (∀ x, h x = true → f x = true ∨
      ∃ u ∈ D, ∃ w ∈ D, u ≠ w ∧ x u = true ∧ x w = true) := by
  refine ⟨fun x hx => by simp [h,hx],?_⟩
  intro x hx
  simp only [h,Bool.or_eq_true,Bool.and_eq_true] at hx
  rcases hx with off | ⟨a,b⟩
  · exact Or.inl off
  · exact Or.inr ⟨0,by decide,2,by decide,by decide,a,b⟩

private def col (c d i : V) :=
  decide ((H.Adj c i ∨ H.Adj d i) ∧ i ≠ c ∧ i ≠ d)

private theorem col_eq (c d : V) : SampleLift.column H c d = col c d := by
  funext i
  unfold SampleLift.column col
  exact congrArg (@decide (ColumnMasks.blocked H c d i)) (Subsingleton.elim _ _)

/-- Both functions accept every raised edge row and reject every sample column.
    The row claim even allows any of the six coordinates to be raised. -/
theorem samples :
    (∀ a b : V, H.Adj a b → ∀ q : Option V,
        f (SampleLift.raiseRow a b q) = true ∧ h (SampleLift.raiseRow a b q) = true) ∧
    (∀ c d : V, c = d ∨ H.Adj c d →
        f (SampleLift.column H c d) = false ∧ h (SampleLift.column H c d) = false) := by
  constructor
  · decide +kernel
  · have finite : ∀ c d : V, c = d ∨ H.Adj c d → f (col c d) = false ∧ h (col c d) = false := by
      decide +kernel
    simpa only [col_eq] using finite

private theorem mark_at (c wanted : V) (member : wanted ∈ D)
    (yes : ColumnMasks.blocked H c c wanted)
    (only : ∀ i ∈ D, ColumnMasks.blocked H c c i → i = wanted) :
    SampleLift.mark H D c c = some wanted := by
  classical
  have exists' : ∃ i ∈ D, ColumnMasks.blocked H c c i := ⟨wanted,member,yes⟩
  rw [SampleLift.mark,dite_eq_left exists']
  exact congrArg some (only _ exists'.choose_spec.1 exists'.choose_spec.2)

theorem both_marks :
    SampleLift.mark H D 1 1 = some 0 ∧ SampleLift.mark H D 3 3 = some 2 := by
  constructor <;> apply mark_at <;> simp only [D,ColumnMasks.blocked] <;> decide

private def first (x : Input) := x 0 && (x 1 || x 2)
private def second (x : Input) := x 2 && x 3
private def third (x : Input) := x 4 && x 5

-- The first satisfied star selects a row group. Its center or a true leaf then
-- supplies a positive literal missing from the rejecting column.
def A (j : Fin 7) (x : Input) : Bool :=
  match j.val with
  | 0 => !(second x) && first x
  | 1 => !(second x) && first x && x 1
  | 2 => !(second x) && first x && !(x 1)
  | 3 | 4 => second x
  | _ => !(first x) && !(second x) && third x

def B (j : Fin 7) (y : Input) : Bool :=
  !(h y) && match j.val with
  | 0 => !(y 0)
  | 1 | 2 => y 0
  | 3 => !(y 2)
  | 4 => y 2
  | 5 => !(y 4)
  | _ => y 4

def pos (j : Fin 7) : Nat := ![0,1,2,2,3,4,5] j

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem partition : IsLiteralPartition 6 h 7 A B pos (fun _ => true) := by
  refine ⟨?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · unfold ExistsUnique
    decide +kernel

theorem signed_tests : SampleLift.SignedTests H D A B pos (fun _ => true) := by
  intro a b c d edge shape
  exact ⟨partition.2.2.2 _ _ (samples.1 a b edge _).2 (samples.2 c d shape).2,
    fun j => partition.2.2.1 j _ _⟩

theorem sample_stable : ∀ j : Fin 7, ∀ v ∈ D, ∀ a b : V, H.Adj a b →
    A j (Function.update (SampleLift.row a b) v true) = A j (SampleLift.row a b) := by
  decide +kernel

/-- Each of the seven positive rectangles needs only one sample slot. -/
theorem graph_seven : GraphTransfer.Rectangles H 7 := by
  apply SampleLift.of_samples H 0 A B pos (fun _ => true) D separated signed_tests
    (fun _ impossible => by contradiction) (fun _ => ∅)
  · exact fun j _ v mem _ => sample_stable j v mem
  · decide +kernel

end Rect4123.ExtensionExample

#print axioms Rect4123.ExtensionExample.extension
#print axioms Rect4123.ExtensionExample.strict
#print axioms Rect4123.ExtensionExample.samples
#print axioms Rect4123.ExtensionExample.both_marks
#print axioms Rect4123.ExtensionExample.partition
#print axioms Rect4123.ExtensionExample.signed_tests
#print axioms Rect4123.ExtensionExample.sample_stable
#print axioms Rect4123.ExtensionExample.graph_seven
