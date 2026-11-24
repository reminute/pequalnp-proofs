import SignalFactor
import Mathlib.Tactic.IntervalCases

namespace FanoJoint25

open PEqualNP.CircuitLowerBounds

-- Wire 36 joins the six nonzero point stars. Wire 38 joins the three lines
-- incident to point zero, without involving the point input itself.
def circuit : Circuit := ⟨[
  ⟨.or,[7,12]⟩,
  ⟨.or,[8,14]⟩,
  ⟨.and,[1,15]⟩,
  ⟨.or,[8,13]⟩,
  ⟨.or,[9,17]⟩,
  ⟨.and,[2,18]⟩,
  ⟨.or,[9,7]⟩,
  ⟨.or,[10,20]⟩,
  ⟨.and,[3,21]⟩,
  ⟨.or,[10,8]⟩,
  ⟨.or,[11,23]⟩,
  ⟨.and,[4,24]⟩,
  ⟨.or,[11,9]⟩,
  ⟨.or,[12,26]⟩,
  ⟨.and,[5,27]⟩,
  ⟨.or,[12,10]⟩,
  ⟨.or,[13,29]⟩,
  ⟨.and,[6,30]⟩,
  ⟨.or,[28,31]⟩,
  ⟨.or,[25,32]⟩,
  ⟨.or,[22,33]⟩,
  ⟨.or,[19,34]⟩,
  ⟨.or,[16,35]⟩,
  ⟨.or,[13,11]⟩,
  ⟨.or,[7,37]⟩],36⟩

def points : List (Fin 7) := [1,2,3,4,5,6]
def lines (p : Fin 7) : List (Fin 7) := [p,p-1,p-3]

theorem point_mem : ∀ p : Fin 7, p∈points ↔ p≠0 := by decide
theorem line_mem : ∀ p t : Fin 7, t∈lines p ↔ (p=t ∨ p=t+1 ∨ p=t+3) := by decide

def pencil (x : Fin 14 → Bool) (p : Fin 7) := (lines p).any fun t => x (Fin.natAdd 7 t)
def remainder (x : Fin 14 → Bool) := points.any fun p => x (Fin.castAdd 7 p) && pencil x p

theorem pencil_spec (x : Fin 14 → Bool) (p : Fin 7) :
    pencil x p=true ↔ ∃ t : Fin 7, (p=t ∨ p=t+1 ∨ p=t+3) ∧ x (Fin.natAdd 7 t)=true := by
  simp only [pencil,List.any_eq_true,line_mem]

theorem remainder_spec (x : Fin 14 → Bool) :
    remainder x=true ↔ ∃ p t : Fin 7, p≠0 ∧ (p=t ∨ p=t+1 ∨ p=t+3) ∧
      x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 t)=true := by
  simp only [remainder,List.any_eq_true,Bool.and_eq_true_iff,point_mem,pencil_spec]
  constructor
  · rintro ⟨p,nz,pt,t,inc,line⟩; exact ⟨p,t,nz,inc,pt,line⟩
  · rintro ⟨p,t,nz,inc,pt,line⟩; exact ⟨p,nz,pt,t,inc,line⟩

theorem outputs (x : Fin 14 → Bool) :
    (circuit.wires (List.ofFn x)).getD 36 false = remainder x ∧
      (circuit.wires (List.ofFn x)).getD 38 false = pencil x 0 := by
  let w (i : Nat) := FanoFactor.signal circuit i x
  have input (i : Fin 14) : w i.val = x i := by
    change PEqualNP.Outside.L_meta_1490.val circuit (List.ofFn x) i.val = x i
    rw [PEqualNP.Outside.L_meta_1490.val_input List.length_ofFn i.isLt]
    rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using i.isLt)]
    simp only [Option.getD_some,List.getElem_ofFn]
  have evalOr (k a b : Nat) (hg : circuit.gates[k]?=some ⟨.or,[a,b]⟩)
      (ha : a<14+k) (hb : b<14+k) : w (14+k) = (w a || w b) := by
    change FanoFactor.signal circuit (14+k) x = _
    rw [FanoFactor.equation hg ha hb]
    simp [GateOp.eval,w]
  have evalAnd (k a b : Nat) (hg : circuit.gates[k]?=some ⟨.and,[a,b]⟩)
      (ha : a<14+k) (hb : b<14+k) : w (14+k) = (w a && w b) := by
    change FanoFactor.signal circuit (14+k) x = _
    rw [FanoFactor.equation hg ha hb]
    simp [GateOp.eval,w]
  have r1 : w 1=x 1 := input 1
  have r2 : w 2=x 2 := input 2
  have r3 : w 3=x 3 := input 3
  have r4 : w 4=x 4 := input 4
  have r5 : w 5=x 5 := input 5
  have r6 : w 6=x 6 := input 6
  have r7 : w 7=x 7 := input 7
  have r8 : w 8=x 8 := input 8
  have r9 : w 9=x 9 := input 9
  have r10 : w 10=x 10 := input 10
  have r11 : w 11=x 11 := input 11
  have r12 : w 12=x 12 := input 12
  have r13 : w 13=x 13 := input 13
  have e14 : w 14=(w 7 || w 12) := evalOr 0 7 12 rfl (by decide) (by decide)
  have e15 : w 15=(w 8 || w 14) := evalOr 1 8 14 rfl (by decide) (by decide)
  have e16 : w 16=(w 1 && w 15) := evalAnd 2 1 15 rfl (by decide) (by decide)
  have e17 : w 17=(w 8 || w 13) := evalOr 3 8 13 rfl (by decide) (by decide)
  have e18 : w 18=(w 9 || w 17) := evalOr 4 9 17 rfl (by decide) (by decide)
  have e19 : w 19=(w 2 && w 18) := evalAnd 5 2 18 rfl (by decide) (by decide)
  have e20 : w 20=(w 9 || w 7) := evalOr 6 9 7 rfl (by decide) (by decide)
  have e21 : w 21=(w 10 || w 20) := evalOr 7 10 20 rfl (by decide) (by decide)
  have e22 : w 22=(w 3 && w 21) := evalAnd 8 3 21 rfl (by decide) (by decide)
  have e23 : w 23=(w 10 || w 8) := evalOr 9 10 8 rfl (by decide) (by decide)
  have e24 : w 24=(w 11 || w 23) := evalOr 10 11 23 rfl (by decide) (by decide)
  have e25 : w 25=(w 4 && w 24) := evalAnd 11 4 24 rfl (by decide) (by decide)
  have e26 : w 26=(w 11 || w 9) := evalOr 12 11 9 rfl (by decide) (by decide)
  have e27 : w 27=(w 12 || w 26) := evalOr 13 12 26 rfl (by decide) (by decide)
  have e28 : w 28=(w 5 && w 27) := evalAnd 14 5 27 rfl (by decide) (by decide)
  have e29 : w 29=(w 12 || w 10) := evalOr 15 12 10 rfl (by decide) (by decide)
  have e30 : w 30=(w 13 || w 29) := evalOr 16 13 29 rfl (by decide) (by decide)
  have e31 : w 31=(w 6 && w 30) := evalAnd 17 6 30 rfl (by decide) (by decide)
  have e32 : w 32=(w 28 || w 31) := evalOr 18 28 31 rfl (by decide) (by decide)
  have e33 : w 33=(w 25 || w 32) := evalOr 19 25 32 rfl (by decide) (by decide)
  have e34 : w 34=(w 22 || w 33) := evalOr 20 22 33 rfl (by decide) (by decide)
  have e35 : w 35=(w 19 || w 34) := evalOr 21 19 34 rfl (by decide) (by decide)
  have e36 : w 36=(w 16 || w 35) := evalOr 22 16 35 rfl (by decide) (by decide)
  have e37 : w 37=(w 13 || w 11) := evalOr 23 13 11 rfl (by decide) (by decide)
  have e38 : w 38=(w 7 || w 37) := evalOr 24 7 37 rfl (by decide) (by decide)
  change (w 36 = _) ∧ (w 38 = _)
  simp only [e38,e37,e36,e35,e34,e33,e32,e31,e30,e29,e28,e27,e26,e25,e24,e23,e22,e21,e20,e19,e18,e17,e16,e15,e14,
    r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,remainder,points,pencil,lines,List.any_cons,List.any_nil,Bool.or_false]
  exact ⟨rfl,rfl⟩

theorem normalized : ∀ j (g : Gate), circuit.gates[j]?=some g →
    (g.op=.and ∨ g.op=.or) ∧ ∃ a b : Nat, g.inputs=[a,b] ∧ a≠b ∧ a<14+j ∧ b<14+j := by
  intro j g eq
  have valid : j<circuit.gates.length := by
    by_contra! off
    rw [List.getElem?_eq_none off] at eq
    contradiction
  change j<25 at valid
  interval_cases j <;> simp [circuit] at eq <;> subst g
  all_goals first
    | exact ⟨Or.inl rfl,_,_,rfl,by decide,by decide,by decide⟩
    | exact ⟨Or.inr rfl,_,_,rfl,by decide,by decide,by decide⟩

theorem checked : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (25 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ ∃ (x2 : ℕ) (x3 : ℕ), x2 < (14 : ℕ) + x1.size ∧ x3 < (14 : ℕ) + x1.size ∧ ∀ (x4 : Fin (14 : ℕ) → Bool), ((x1.wires (List.ofFn x4)).getD x2 Bool.false = Bool.true ↔ ∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), x5 ≠ (0 : Fin (7 : ℕ)) ∧ (x5 = x6 ∨ x5 = x6 + (1 : Fin (7 : ℕ)) ∨ x5 = x6 + (3 : Fin (7 : ℕ))) ∧ x4 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (7 : ℕ) x6) = Bool.true) ∧ ((x1.wires (List.ofFn x4)).getD x3 Bool.false = Bool.true ↔ ∃ (x5 : Fin (7 : ℕ)), ((0 : Fin (7 : ℕ)) = x5 ∨ (0 : Fin (7 : ℕ)) = x5 + (1 : Fin (7 : ℕ)) ∨ (0 : Fin (7 : ℕ)) = x5 + (3 : Fin (7 : ℕ))) ∧ x4 (Fin.natAdd (7 : ℕ) x5) = Bool.true) := by
  refine ⟨circuit,by decide,normalized,36,38,by decide,by decide,?_⟩
  intro x
  rw [(outputs x).1,(outputs x).2]
  exact ⟨remainder_spec x,pencil_spec x 0⟩

end FanoJoint25

#print axioms FanoJoint25.checked
