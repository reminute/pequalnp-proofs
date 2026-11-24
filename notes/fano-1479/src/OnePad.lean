import FanoPadding
import SignalFactor

namespace FanoOnePad

open PEqualNP.CircuitLowerBounds FanoPadding FanoFactor

def gate (C : Circuit) (q : Nat) : Gate := ⟨.and,[C.output,q]⟩
def append (C : Circuit) (q : Nat) : Circuit := ⟨C.gates++[gate C q],14+C.size⟩

theorem normal_append (C : Circuit) (normal : Normal C) (correct : Spec C) {q : Nat}
    (earlier : q < C.output) : Normal (append C q) := by
  intro j g hg
  change (C.gates++[gate C q])[j]? = some g at hg
  by_cases old : j < C.gates.length
  · rw [List.getElem?_append_left old] at hg
    exact normal j g hg
  · rw [List.getElem?_append_right (Nat.le_of_not_gt old)] at hg
    cases h : j-C.gates.length with
    | zero =>
      have eq : j=C.size := by simp only [Circuit.size]; omega
      rw [h] at hg
      obtain rfl : gate C q=g := Option.some.inj hg
      have out := (valid_output C correct).1
      exact ⟨Or.inl rfl,C.output,q,rfl,Nat.ne_of_gt earlier,by omega,by omega⟩
    | succ k => simp [h] at hg

theorem wires_append (C : Circuit) (q : Nat) (x : Fin 14 → Bool) :
    (append C q).wires (List.ofFn x) = C.wires (List.ofFn x) ++ [C.eval (List.ofFn x) && signal C q x] := by
  simp [append,gate,Circuit.wires,Circuit.eval,signal,PEqualNP.Outside.L_meta_1490.val,
    List.foldl_append,GateOp.eval]

theorem eval_append (C : Circuit) (q : Nat) (x : Fin 14 → Bool) :
    (append C q).eval (List.ofFn x) = (C.eval (List.ofFn x) && signal C q x) := by
  change ((append C q).wires (List.ofFn x)).getD (14+C.size) false = _
  rw [wires_append,← length_wires C x]
  simp [List.getD_eq_getElem?_getD]

theorem from_upper (C : Circuit) (size : C.size ≤ 26) (normal : Normal C) (correct : Spec C)
    {q : Nat} (ear : q < C.output) (upper : ∀ x, C.eval (List.ofFn x)=true → signal C q x=true)
    (p l : Fin 7) (incident : p=l ∨ p=l+1 ∨ p=l+3)
    (offPoint : signal C q (single (Fin.castAdd 7 p))=false)
    (offLine : signal C q (single (Fin.natAdd 7 l))=false) : Posted := by
  have dn := normal_append C normal correct ear
  have ds : Spec (append C q) := by
    intro x
    rw [eval_append,Bool.and_eq_true_iff,←correct x]
    exact ⟨And.left,fun on => ⟨on,upper x on⟩⟩
  have last : (append C q).gates[C.size]? = some ⟨.and,[C.output,q]⟩ := by simp [append,gate,Circuit.size]
  have trace (s t : Fin 14) (dark : signal C q (single s)=false) : Trace (append C q) s t := by
    apply trace_of_dark_and (append C q) dn s t rfl last
    · rw [wires_append,FanoPadding.earlier]
      · exact single_off C correct s
      · rw [length_wires]; exact (valid_output C correct).1
    · rw [wires_append,FanoPadding.earlier]
      · exact dark
      · rw [length_wires]; exact ear.trans (valid_output C correct).1
  apply finish (append C q) (by simpa [append,Circuit.size] using (Nat.add_le_add_right size 1))
    dn ds p l incident (trace _ _ offPoint) (trace _ _ offLine)

theorem from_operand (C : Circuit) (size : C.size ≤ 26) (normal : Normal C) (correct : Spec C)
    {k a b q : Nat} (output : C.output=14+k) (hg : C.gates[k]?=some ⟨.and,[a,b]⟩)
    (operand : q=a ∨ q=b) (p l : Fin 7) (incident : p=l ∨ p=l+1 ∨ p=l+3)
    (offPoint : signal C q (single (Fin.castAdd 7 p))=false)
    (offLine : signal C q (single (Fin.natAdd 7 l))=false) : Posted := by
  obtain ⟨_,a',b',he,_,ha,hb⟩ := normal k _ hg
  obtain ⟨rfl,rfl⟩ : a=a' ∧ b=b' := by simpa using he
  apply from_upper C size normal correct (q := q) _ _ p l incident offPoint offLine
  · rw [output]; rcases operand with rfl | rfl <;> assumption
  · intro x on
    change signal C C.output x = true at on
    rw [output,equation hg ha hb x] at on
    have both : signal C a x=true ∧ signal C b x=true := by simpa [GateOp.eval] using on
    rcases operand with rfl | rfl
    · exact both.1
    · exact both.2

end FanoOnePad

#print axioms FanoOnePad.from_operand
