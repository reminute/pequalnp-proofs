import FlagTransport
import SameShoreData
import Joint28

namespace Near28

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open FanoFlag FanoRename

private abbrev baseC := FanoJoint28.circuit
private theorem baseAO : IsAO2 14 baseC := by decide +kernel
private theorem baseDistinct : ∀ j<baseC.size, opnd baseC j 0 ≠ opnd baseC j 1 := by
  have finite : ∀ j : Fin 28, opnd baseC j.val 0 ≠ opnd baseC j.val 1 := by decide +kernel
  exact fun j hj => finite ⟨j,hj⟩

private def dark (i : V) := i.val≠0 ∧ i.val≠7 ∧ i.val≠11 ∧ i.val≠13
private instance (i : V) : Decidable (dark i) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

private theorem dark_anchors : ∀ r, dark (inv r 0) ∧ dark (inv r 7) := by decide +kernel
private theorem dark_wires : ∀ i : V, dark i →
    (baseC.wires (List.ofFn (FanoPadding.single i))).getD 39 false=false ∧
    (baseC.wires (List.ofFn (FanoPadding.single i))).getD 40 false=false := by decide +kernel

private theorem baseDir (a b : V) (far : dark a) : Dir baseC a b := by
  have norm := FanoJoint28.exact_circuit.2.1
  obtain ⟨v,raw,run,off⟩ := FanoPadding.trace_of_dark_and baseC norm a b (k:=27) rfl
    (by rfl) (dark_wires a far).1 (dark_wires a far).2
  refine ⟨v,?_,?_,off⟩
  · intro i hi
    simpa [Fin.ext_iff] using raw ⟨i,hi⟩
  · intro j hj
    have valid : j < baseC.gates.length := hj
    have g : baseC.gates[j]? = some (gateAt baseC j) := by
      simp [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem valid]
    obtain ⟨_,u,z,ins,_,_,_⟩ := norm _ _ g
    simpa [opnd,ins,FanoPadding.single,singletonBits] using run j _ u z g ins

private theorem preserved (r : Row) (x : V → Bool) : ReceiptF (x ∘ perm r) ↔ ReceiptF x := by
  rw [graph_spec,graph_spec]
  constructor
  · rintro ⟨a,b,e,l,h⟩
    exact ⟨perm r a,perm r b,(adj_eq r a b).trans e,l,h⟩
  · rintro ⟨a,b,e,l,h⟩
    refine ⟨inv r a,inv r b,?_,?_,?_⟩
    · simpa only [← adj_eq r (inv r a) (inv r b),right_inverse] using e
    · simpa only [Function.comp_apply,right_inverse] using l
    · simpa only [Function.comp_apply,right_inverse] using h

def buildCircuit (r : Row) := circuit (perm r) baseC

def Meets (C : Circuit) (a b : V) := C.size=28 ∧ IsAO2 14 C ∧
    (∀ j<C.size, opnd C j 0 ≠ opnd C j 1) ∧ (gateAt C 0).op=.or ∧
    ((opnd C 0 0=a.val ∧ opnd C 0 1=b.val) ∨ (opnd C 0 0=b.val ∧ opnd C 0 1=a.val)) ∧
    (∀ x, C.eval (List.ofFn x)=true ↔ ReceiptF x) ∧
    Dir C (0 : V) 7 ∧ Dir C (7 : V) 0

set_option maxHeartbeats 600000 in
theorem from_row (r : Row) {a b : V} (first : samePair (perm r 7) (perm r 12) a b) :
    Meets (buildCircuit r) a b := by
  refine ⟨(size _ baseC).trans rfl,ao _ baseAO,distinct (equiv r) baseAO baseDistinct,?_,?_,?_,?_⟩
  · change (gateAt (circuit _ baseC) 0).op=.or
    rw [at_gate]
    rfl
  · have left : opnd (buildCircuit r) 0 0 = (perm r 7).val :=
      (operand _ baseAO (by decide : 0<baseC.size) 0).trans (wire_raw (perm r) (7 : V))
    have right : opnd (buildCircuit r) 0 1 = (perm r 12).val :=
      (operand _ baseAO (by decide : 0<baseC.size) 1).trans (wire_raw (perm r) (12 : V))
    rw [left,right]
    simpa only [Fin.val_inj,samePair] using first
  · intro x
    change (circuit (perm r) baseC).eval (List.ofFn x)=true ↔ ReceiptF x
    rw [eval]
    exact (FanoJoint28.exact_circuit.2.2.1 (x ∘ perm r)).trans (preserved r x)
  · obtain ⟨h0,h7⟩ := dark_anchors r
    have f := dir_rename (equiv r) baseAO (baseDir _ (inv r 7) h0)
    have b := dir_rename (equiv r) baseAO (baseDir _ (inv r 0) h7)
    change Dir (buildCircuit r) (perm r (inv r 0)) (perm r (inv r 7)) at f
    change Dir (buildCircuit r) (perm r (inv r 7)) (perm r (inv r 0)) at b
    simpa only [right_inverse] using And.intro f b

/-- For any prescribed distinct raw pair on the same shore, the fixed-flag
    condition admits a 28-gate circuit starting with that pair's OR. -/
theorem same_shore_28 (a b : V) (ne : a≠b) (shore : a.val<7 ↔ b.val<7) :
    ∃ C : Circuit, Meets C a b := by
  obtain ⟨r,hr⟩ := all_pairs a b ne shore
  refine ⟨buildCircuit r,from_row r ?_⟩
  rcases starts_at r with ⟨e,f⟩ | ⟨e,f⟩ <;> rcases hr with ⟨g,h⟩ | ⟨g,h⟩ <;>
    simp_all [samePair]

end Near28

#print axioms Near28.same_shore_28
