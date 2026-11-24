import FanoPadding
import SignalFactor

namespace FanoJoint

open PEqualNP.CircuitLowerBounds FanoPadding FanoFactor

def H (x : Input) : Bool := decide (∃ u t : Fin 7, u≠0 ∧
  (u=t ∨ u=t+1 ∨ u=t+3) ∧ x (Fin.castAdd 7 u)=true ∧ x (Fin.natAdd 7 t)=true)

def N (x : Input) : Bool := decide (∃ t : Fin 7, (0=t ∨ 0=t+1 ∨ 0=t+3) ∧ x (Fin.natAdd 7 t)=true)

theorem factor (x : Input) : ((H x || x 0) && (H x || N x)) = true ↔
    ∃ u t : Fin 7, (u=t ∨ u=t+1 ∨ u=t+3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true := by
  simp only [Bool.and_eq_true_iff,Bool.or_eq_true_iff,H,N,decide_eq_true_eq]
  constructor
  · rintro ⟨left,right⟩
    rcases left with ⟨u,t,_,e,a,b⟩ | on
    · exact ⟨u,t,e,a,b⟩
    rcases right with ⟨u,t,_,e,a,b⟩ | ⟨t,e,b⟩
    · exact ⟨u,t,e,a,b⟩
    · exact ⟨0,t,e,on,b⟩
  · rintro ⟨u,t,e,a,b⟩
    by_cases zero : u=0
    · subst u; exact ⟨Or.inr a,Or.inr ⟨t,e,b⟩⟩
    · exact ⟨Or.inl ⟨u,t,zero,e,a,b⟩,Or.inl ⟨u,t,zero,e,a,b⟩⟩

def suffix (C : Circuit) (h n : Nat) : List Gate :=
  [⟨.or,[h,0]⟩,⟨.or,[h,n]⟩,⟨.and,[14+C.size,14+C.size+1]⟩]

def extend (C : Circuit) (h n : Nat) : Circuit := ⟨C.gates++suffix C h n,14+C.size+2⟩

theorem old_signal (C : Circuit) (h n : Nat) (x : Input) {w : Nat} (bound : w<14+C.size) :
    signal (extend C h n) w x = signal C w x := by
  change ((C.gates++suffix C h n).foldl step (List.ofFn x)).getD w false = _
  rw [List.foldl_append]
  obtain ⟨extra,eq,_⟩ := eval_extends (suffix C h n) (C.wires (List.ofFn x))
  change ((suffix C h n).foldl step (C.wires (List.ofFn x))).getD w false = _
  rw [eq,earlier (by rw [length_wires]; exact bound)]
  rfl

theorem normalized (C : Circuit) (normal : Normal C) {h n : Nat} (hb : h<14+C.size) (nb : n<14+C.size)
    (hz : h≠0) (hn : h≠n) : Normal (extend C h n) := by
  intro j g atGate
  change (C.gates++suffix C h n)[j]? = some g at atGate
  by_cases old : j<C.gates.length
  · rw [List.getElem?_append_left old] at atGate; exact normal j g atGate
  have member : j < (C.gates++suffix C h n).length := by
    by_contra! large
    rw [List.getElem?_eq_none large] at atGate
    contradiction
  have upper : j<C.size+3 := by simpa [suffix,Circuit.size] using member
  have lower : C.size ≤ j := Nat.le_of_not_gt old
  have cases : j=C.size ∨ j=C.size+1 ∨ j=C.size+2 := by omega
  rcases cases with rfl | rfl | rfl
  · have ident : (⟨.or,[h,0]⟩ : Gate) = g := by simpa [Circuit.size,suffix] using atGate
    subst g; exact ⟨Or.inr rfl,h,0,rfl,hz,hb,by omega⟩
  · have ident : (⟨.or,[h,n]⟩ : Gate) = g := by simpa [Circuit.size,suffix] using atGate
    subst g; exact ⟨Or.inr rfl,h,n,rfl,hn,by omega,by omega⟩
  · have ident : (⟨.and,[14+C.size,14+C.size+1]⟩ : Gate) = g := by simpa [Circuit.size,suffix] using atGate
    subst g; exact ⟨Or.inl rfl,_,_,rfl,by omega,by omega,by omega⟩

theorem gadget_traces (C : Circuit) (normal : Normal C) {h n : Nat}
    (validH : h<14+C.size) (validN : n<14+C.size)
    (computesH : ∀ x : Input, signal C h x=H x) (computesN : ∀ x : Input, signal C n x=N x) :
    Normal (extend C h n) ∧ Spec (extend C h n) ∧
      Trace (extend C h n) point line ∧ Trace (extend C h n) line point := by
  let D := extend C h n
  have hz : h≠0 := by
    intro eq
    have a := computesH (single 0)
    rw [eq] at a
    change (C.wires (List.ofFn (single 0))).getD 0 false = _ at a
    rw [raw] at a
    have off : H (single 0)=false := by decide
    rw [off] at a
    contradiction
  have hn : h≠n := by
    intro eq
    let test := single (Fin.natAdd 7 (0 : Fin 7))
    have a := computesH test
    rw [eq,computesN] at a
    have different : N test ≠ H test := by decide
    exact different a
  have norm : Normal D := normalized C normal validH validN hz hn
  have first : D.gates[C.size]?=some ⟨.or,[h,0]⟩ := by simp [D,extend,suffix,Circuit.size]
  have second : D.gates[C.size+1]?=some ⟨.or,[h,n]⟩ := by simp [D,extend,suffix,Circuit.size]
  have last : D.gates[C.size+2]?=some ⟨.and,[14+C.size,14+C.size+1]⟩ := by simp [D,extend,suffix,Circuit.size]
  have leftValue (x : Input) : signal D (14+C.size) x = (H x || x 0) := by
    rw [equation first validH (by omega) x,old_signal C h n x validH,computesH]
    change GateOp.or.eval [H x,(D.wires (List.ofFn x)).getD 0 false]=_
    rw [raw]
    simp [GateOp.eval]
  have rightValue (x : Input) : signal D (14+C.size+1) x = (H x || N x) := by
    rw [Nat.add_assoc, equation second (by omega) (by omega) x,
      old_signal C h n x validH,old_signal C h n x validN,computesH,computesN]
    simp [GateOp.eval]
  have out : D.output=14+(C.size+2) := by dsimp [D,extend]; omega
  have spec : Spec D := by
    intro x
    change signal D D.output x = true ↔ _
    rw [out,equation last (by omega) (by omega) x,leftValue,rightValue]
    simpa [GateOp.eval] using factor x
  have trace (base initial : Fin 14) (darkH : H (single base)=false)
      (darkN : N (single base)=false) (dark0 : single base 0=false) : Trace D base initial := by
    apply trace_of_dark_and D norm base initial out last
    · change signal D (14+C.size) _=false
      rw [leftValue,darkH,dark0]; rfl
    · change signal D (14+C.size+1) _=false
      rw [rightValue,darkH,darkN]; rfl
  refine ⟨norm,spec,?_,?_⟩
  · apply trace <;> decide
  · apply trace <;> decide

theorem from_joint (C : Circuit) (size : C.size≤24) (normal : Normal C) {h n : Nat}
    (validH : h<14+C.size) (validN : n<14+C.size)
    (computesH : ∀ x : Input, signal C h x=H x) (computesN : ∀ x : Input, signal C n x=N x) :
    Posted := by
  obtain ⟨norm,spec,left,right⟩ := gadget_traces C normal validH validN computesH computesN
  exact finish (extend C h n) (by simpa [extend,suffix,Circuit.size] using Nat.add_le_add_right size 3)
    norm spec 1 1 (Or.inl rfl) left right

end FanoJoint

#print axioms FanoJoint.from_joint
