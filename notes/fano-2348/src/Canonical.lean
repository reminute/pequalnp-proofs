import Desk2348

namespace FanoCanonical

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open FanoFlag FanoRename

private def diagonal (s : Fin 7) (i : V) : Bool := decide (i.val=s.val ∨ i.val=7+s.val)

-- A circuit with no gates could only return a raw input or the default
-- false output. Two disjoint positive examples rule out both possibilities.
theorem size_pos {C : Circuit} (spec : ∀ x, C.eval (List.ofFn x)=true ↔ ReceiptF x) : 0<C.size := by
  by_contra! zero
  have len : C.gates.length=0 := Nat.eq_zero_of_le_zero zero
  have empty : C.gates=[] := List.length_eq_zero_iff.mp len
  have on (s : Fin 7) : C.eval (List.ofFn (diagonal s))=true := by
    apply (spec _).2
    exact ⟨s,s,Or.inl rfl,by simp [diagonal],by simp [diagonal,Nat.add_comm]⟩
  have read (s : Fin 7) : (List.ofFn (diagonal s)).getD C.output false=true := by
    simpa only [Circuit.eval,Circuit.wires,empty,List.foldl_nil] using on s
  by_cases raw : C.output<14
  · have endpoint (s : Fin 7) : C.output=s.val ∨ C.output=7+s.val := by
      have h := read s
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using raw)] at h
      simpa only [Option.getD_some,List.getElem_ofFn,diagonal,decide_eq_true_eq] using h
    have a : C.output=0 ∨ C.output=7 := endpoint 0
    have b : C.output=1 ∨ C.output=8 := endpoint 1
    omega
  · have h := read 0
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by simpa only [List.length_ofFn] using Nat.le_of_not_gt raw)] at h
    contradiction

theorem first_raw {C : Circuit} (ao : IsAO2 14 C) (existsGate : 0<C.size) (b : Fin 2) :
    opnd C 0 b<14 := by
  have member : gateAt C 0 ∈ C.gates := by
    simp only [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (show 0<C.gates.length from existsGate),Option.getD_some]
    exact List.getElem_mem _
  have valid : b.val<(gateAt C 0).inputs.length := by rw [ao.2.2 _ member]; exact b.isLt
  have selected : opnd C 0 b ∈ (gateAt C 0).inputs := by
    rw [opnd,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem valid]
    exact List.getElem_mem _
  exact ao.2.1 0 existsGate _ selected

def First (C : Circuit) (i : R) : Prop :=
  (opnd C 0 0=(rep i).1.val ∧ opnd C 0 1=(rep i).2.val) ∨
  (opnd C 0 0=(rep i).2.val ∧ opnd C 0 1=(rep i).1.val)

theorem canonicalize {C : Circuit} (w : Witness C) :
    ∃ (g : G) (i : R), Witness (acted g C) ∧ First (acted g C) i := by
  have ao := w.2.1
  have pos : 0<C.size := size_pos w.2.2.2.2.1
  let a : V := ⟨opnd C 0 0,first_raw ao pos 0⟩
  let b : V := ⟨opnd C 0 1,first_raw ao pos 1⟩
  have ne : a≠b := fun e => w.2.2.1 0 pos (congrArg Fin.val e)
  obtain ⟨g,i,e⟩ := cover a b ne
  refine ⟨g,i,acts_witness g w,?_⟩
  have left : opnd (acted g C) 0 0=(perm g a).val :=
    (acted_operand g ao pos 0).trans (wire_raw (perm g) a)
  have right : opnd (acted g C) 0 1=(perm g b).val :=
    (acted_operand g ao pos 1).trans (wire_raw (perm g) b)
  unfold First
  rw [left,right]
  rcases e with ⟨ea,eb⟩ | ⟨ea,eb⟩
  · exact Or.inl ⟨congrArg Fin.val ea,congrArg Fin.val eb⟩
  · exact Or.inr ⟨congrArg Fin.val ea,congrArg Fin.val eb⟩

theorem canonical_iff : (¬∃ C : Circuit, Witness C) ↔ ∀ i : R, ∀ C : Circuit, First C i → ¬ Witness C := by
  constructor
  · exact fun none _ C _ w => none ⟨C,w⟩
  · rintro none ⟨C,w⟩
    obtain ⟨g,i,valid,first⟩ := canonicalize w
    exact none i (acted g C) first valid

theorem posted_iff_canonical : Desk2348.Posted ↔
    ∀ i : R, ∀ C : Circuit, First C i → ¬ Witness C :=
  Desk2348.posted_iff.trans canonical_iff

end FanoCanonical

#print axioms FanoCanonical.canonical_iff
#print axioms FanoCanonical.posted_iff_canonical
