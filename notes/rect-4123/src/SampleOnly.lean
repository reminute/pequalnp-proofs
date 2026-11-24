import SampleLift
import TwoEdges

namespace Rect4123.SampleOnly

open PEqualNP.MetaComplexity GraphTransfer SampleLift ColumnMasks
open TwoEdges (f A pos sign xAB)

/-- Matching edges ab and cd, with a,b,c,d numbered 0,1,2,3. -/
def H : SimpleGraph (Fin 4) where
  Adj a b := a.val / 2 = b.val / 2 ∧ a ≠ b
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

instance : DecidableRel H.Adj := fun a b =>
  inferInstanceAs (Decidable (a.val / 2 = b.val / 2 ∧ a ≠ b))

/-- Starting with the six signed rectangles of TwoEdges, discard every column
containing both a and c. This removes a genuine rejecting input. -/
def B (j : Fin 6) (y : Fin 4 → Bool) := TwoEdges.B j y && !(y 0 && y 2)

def coords : Finset (Fin 4) := {2}
def charged (j : Fin 6) : Finset (Fin 4) := if j=1 then {2} else ∅
def yAC (z : Fin 4) : Bool := decide (z=0 ∨ z=2)

private def colBits (c d z : Fin 4) : Bool :=
  decide ((H.Adj c z ∨ H.Adj d z) ∧ z≠c ∧ z≠d)

private theorem as_bits (c d : Fin 4) : column H c d = colBits c d := by
  funext z
  exact congrArg (fun inst : Decidable (blocked H c d z) => @decide _ inst)
    (Subsingleton.elim _ _)

theorem matching_spec : Spec H f := by unfold Spec; decide +kernel

private theorem column_tests : ∀ c d : Fin 4, c=d ∨ H.Adj c d →
    f (colBits c d)=false ∧ (colBits c d 0 && colBits c d 2)=false := by decide +kernel

theorem sample_unchanged (c d : Fin 4) (shape : c=d ∨ H.Adj c d) (j : Fin 6) :
    B j (column H c d) = TwoEdges.B j (column H c d) := by
  rw [as_bits]
  simp [B,(column_tests c d shape).2]

/-- All lifts are covered, so in particular the actual lift chosen by the mask
is covered. Every selected literal has the required sign on both inputs. -/
theorem all_lifts (a b c d : Fin 4) (edge : H.Adj a b) (shape : c=d ∨ H.Adj c d)
    (q : Option (Fin 4)) :
    let x := raiseRow a b q
    let y := column H c d
    (∃! j, A j x=true ∧ B j y=true) ∧
      ∀ j, A j x=true → B j y=true → ∃ i : Fin 4, pos j=i.val ∧ x i=sign j ∧ y i≠sign j := by
  dsimp only
  simp_rw [sample_unchanged c d shape]
  have pair : f (row a b)=true := (matching_spec _).mpr ⟨a,b,edge,by simp [row],by simp [row]⟩
  have on : f (raiseRow a b q)=true := by
    cases q with
    | none => exact pair
    | some v => exact raise_preserves H f matching_spec v _ pair
  have off : f (column H c d)=false := as_bits c d ▸ (column_tests c d shape).1
  exact ⟨TwoEdges.partition.2.2.2 _ _ on off,fun j => TwoEdges.partition.2.2.1 j _ _⟩

theorem signed_tests : SignedTests H coords A B pos sign :=
  fun a b c d edge shape => all_lifts a b c d edge shape _

theorem missed_pair : f xAB=true ∧ f yAC=false ∧ ∀ j, B j yAC=false := by decide

theorem not_global : ¬ IsLiteralPartition 4 f 6 A B pos sign := by
  intro part
  obtain ⟨j,_,yes⟩ := (part.2.2.2 xAB yAC missed_pair.1 missed_pair.2.1).exists
  exact Bool.noConfusion (yes.symm.trans (missed_pair.2.2 j))

theorem nonsampled_column (c d : Fin 4) (shape : c=d ∨ H.Adj c d) :
    column H c d ≠ yAC := by
  intro eqv
  have few := (column_tests c d shape).2
  rw [← as_bits c d,eqv] at few
  contradiction

theorem six_rectangles : Rectangles H 6 := by
  apply of_samples H 0 A B pos sign coords _ signed_tests _ charged _ _
  · simp [Separated,coords]
  · decide
  · decide +kernel
  · decide

end Rect4123.SampleOnly

#print axioms Rect4123.SampleOnly.signed_tests
#print axioms Rect4123.SampleOnly.not_global
#print axioms Rect4123.SampleOnly.six_rectangles
