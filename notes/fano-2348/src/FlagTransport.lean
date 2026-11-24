import InputRenaming
import FlagOrbits

namespace FanoRename

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

variable {n : ℕ}

def singletonBits (a : Fin n) (i : Fin n) := decide (i=a)

def Dir (C : Circuit) (a b : Fin n) : Prop := ∃ v : ℕ → Bool,
  let w := C.wires (List.ofFn (singletonBits a))
  (∀ i < n, v i = decide (i=b.val)) ∧
  (∀ j < C.size, let g := gateAt C j; let u := opnd C j 0; let z := opnd C j 1
    (g.op=.and → v (n+j) = ((w.getD u false && v z) || (v u && w.getD z false))) ∧
    (g.op=.or → v (n+j) = (v u || v z))) ∧ v C.output=false

theorem dir_rename (e : Fin n ≃ Fin n) {C : Circuit} (normal : IsAO2 n C)
    {a b : Fin n} (tr : Dir C a b) : Dir (circuit e C) (e a) (e b) := by
  obtain ⟨v,raw,run,miss⟩ := tr
  refine ⟨fun i => v (wire e.symm i),?_,?_,?_⟩
  · intro i hi
    let t : Fin n := ⟨i,hi⟩
    change v (wire e.symm t.val) = decide (t.val=(e b).val)
    rw [wire_raw,raw _ (e.symm t).isLt]
    have eq : ((e.symm t).val = b.val) ↔ (t.val = (e b).val) := by
      simp only [Fin.val_inj]
      exact e.symm_apply_eq
    simp only [eq]
  · intro j hj
    rw [size] at hj
    have input : singletonBits (e a) ∘ e = singletonBits a := by
      funext t
      simp [singletonBits]
    have values (i : ℕ) :
        ((circuit e C).wires (List.ofFn (singletonBits (e a)))).getD (wire e i) false =
        (C.wires (List.ofFn (singletonBits a))).getD i false := by rw [wires,input]
    have high : n ≤ n+j := by omega
    simpa only [at_gate,gate,operand e normal hj,values,wire_high e.symm high,undo]
      using run j hj
  · change v (wire e.symm (wire e C.output))=false
    rw [undo]
    exact miss

def permEquiv (g : FanoFlag.G) : Fin 14 ≃ Fin 14 :=
  ⟨FanoFlag.perm g,FanoFlag.perm (FanoFlag.inv g),FanoFlag.left_inv g,FanoFlag.right_inv g⟩

def acted (g : FanoFlag.G) (C : Circuit) := circuit (FanoFlag.perm g) C

theorem acted_operand (g : FanoFlag.G) {C : Circuit} (normal : IsAO2 14 C) {j : ℕ}
    (valid : j<C.size) (b : Fin 2) :
    opnd (acted g C) j b = wire (FanoFlag.perm g) (opnd C j b) :=
  operand (FanoFlag.perm g) normal valid b

def Witness (C : Circuit) : Prop := C.size ≤ 27 ∧ IsAO2 14 C ∧
  (∀ j<C.size, opnd C j 0 ≠ opnd C j 1) ∧ (gateAt C 0).op=.or ∧
  (∀ x, C.eval (List.ofFn x)=true ↔ FanoFlag.ReceiptF x) ∧
  Dir C (0 : Fin 14) 7 ∧ Dir C (7 : Fin 14) 0

theorem acts_witness (g : FanoFlag.G) {C : Circuit} (w : Witness C) : Witness (acted g C) := by
  obtain ⟨bound,shape,diff,first,correct,forward,back⟩ := w
  refine ⟨by simpa only [acted,size] using bound,ao _ shape,distinct (permEquiv g) shape diff,
    ?_,?_,?_⟩
  · change (gateAt (circuit _ C) 0).op=.or
    rw [at_gate]
    exact first
  · intro x
    rw [acted,eval,correct]
    exact FanoFlag.keeps_incidence g x
  · have f := dir_rename (permEquiv g) shape forward
    have b := dir_rename (permEquiv g) shape back
    change Dir (acted g C) (FanoFlag.perm g 0) (FanoFlag.perm g 7) at f
    change Dir (acted g C) (FanoFlag.perm g 7) (FanoFlag.perm g 0) at b
    rcases FanoFlag.fixes_flag g with ⟨u,v⟩ | ⟨u,v⟩
    · rw [u,v] at f b
      exact ⟨f,b⟩
    · rw [u,v] at f b
      exact ⟨b,f⟩

-- Unpack the paired direction parameter used in the literal desk statement.
theorem paired_iff (C : Circuit) :
    (∀ s : Bool, Dir C (if s=true then (0 : Fin 14) else 7)
        (if s=true then (7 : Fin 14) else 0)) ↔
      Dir C (0 : Fin 14) 7 ∧ Dir C (7 : Fin 14) 0 := by
  constructor
  · exact fun h => ⟨h true,h false⟩
  · rintro ⟨f,b⟩ s
    cases s
    · exact b
    · exact f

end FanoRename

#print axioms FanoRename.acts_witness
