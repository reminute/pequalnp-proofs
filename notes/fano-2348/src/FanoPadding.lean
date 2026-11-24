import PEqualNP.Defs

namespace FanoPadding

open PEqualNP.CircuitLowerBounds

def Normal (C : Circuit) := ∀ j g, C.gates[j]? = some g →
  (g.op = .and ∨ g.op = .or) ∧ ∃ a b : Nat, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j

def Spec (C : Circuit) := ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
  ∃ u t : Fin 7, (u=t ∨ u=t+1 ∨ u=t+3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true

def point : Fin 14 := Fin.castAdd 7 (1 : Fin 7)
def line : Fin 14 := Fin.natAdd 7 (1 : Fin 7)
def single (s : Fin 14) (i : Fin 14) := decide (i=s)

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eval_extends (gs : List Gate) (w : List Bool) :
    ∃ u : List Bool, gs.foldl step w = w++u ∧ u.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp⟩
  | cons g gs ih =>
    obtain ⟨u,hu,lu⟩ := ih (step w g)
    exact ⟨_::u,by simpa [step,List.append_assoc] using hu,by simp [lu]⟩

theorem length_wires (C : Circuit) (x : Fin 14 → Bool) :
    (C.wires (List.ofFn x)).length = 14+C.size := by
  obtain ⟨u,e,l⟩ := eval_extends C.gates (List.ofFn x)
  change (C.gates.foldl step _).length = _
  rw [e,List.length_append,List.length_ofFn,l]
  rfl

theorem earlier {w u : List Bool} {i : Nat} (h : i < w.length) :
    (w++u).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_append_left h]

theorem raw (C : Circuit) (x : Fin 14 → Bool) :
    (C.wires (List.ofFn x)).getD 0 false = x 0 := by
  obtain ⟨u,e,_⟩ := eval_extends C.gates (List.ofFn x)
  change ((C.gates.foldl step _).getD 0 false) = _
  rw [e,earlier (by simp)]
  simp [List.getD_eq_getElem?_getD]

theorem single_off (C : Circuit) (correct : Spec C) (s : Fin 14) :
    C.eval (List.ofFn (single s)) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨u,t,_,a,b⟩ := (correct _).mp h
  simp only [single,decide_eq_true_eq] at a b
  have eq := congrArg Fin.val (a.trans b.symm)
  simp at eq
  omega

theorem valid_output (C : Circuit) (correct : Spec C) : C.output < 14+C.size ∧ C.output ≠ 0 := by
  constructor
  · by_contra! h
    let x : Fin 14 → Bool := fun _ => true
    have on := (correct x).mpr ⟨0,0,Or.inl rfl,rfl,rfl⟩
    have past : (C.wires (List.ofFn x)).length ≤ C.output := (length_wires C x) ▸ h
    rw [Circuit.eval,List.getD_eq_getElem?_getD,List.getElem?_eq_none past] at on
    contradiction
  · intro eq
    have off := single_off C correct 0
    rw [Circuit.eval,eq,raw] at off
    contradiction

def joinGate (C : Circuit) : Gate := ⟨.or,[C.output,0]⟩
def meetGate (C : Circuit) : Gate := ⟨.and,[C.output,14+C.size]⟩
def pad (C : Circuit) : Circuit := ⟨C.gates++[joinGate C,meetGate C],14+C.size+1⟩

theorem pad_normal (C : Circuit) (normal : Normal C) (correct : Spec C) : Normal (pad C) := by
  obtain ⟨ear,bne⟩ := valid_output C correct
  intro j g hg
  change (C.gates++[joinGate C,meetGate C])[j]? = some g at hg
  by_cases old : j < C.gates.length
  · rw [List.getElem?_append_left old] at hg
    exact normal j g hg
  · rw [List.getElem?_append_right (Nat.le_of_not_gt old)] at hg
    cases h : j-C.gates.length with
    | zero =>
      have eq : j=C.size := by simp only [Circuit.size]; omega
      rw [h] at hg
      obtain rfl : joinGate C = g := Option.some.inj hg
      exact ⟨Or.inr rfl,C.output,0,rfl,bne,eq ▸ ear,by omega⟩
    | succ k =>
      cases k with
      | zero =>
        have eq : j=C.size+1 := by simp only [Circuit.size]; omega
        rw [h] at hg
        obtain rfl : meetGate C = g := Option.some.inj hg
        exact ⟨Or.inl rfl,C.output,14+C.size,rfl,Nat.ne_of_lt ear,by omega,by omega⟩
      | succ k => simp [h] at hg

theorem pad_wires (C : Circuit) (correct : Spec C) (x : Fin 14 → Bool) :
    (pad C).wires (List.ofFn x) =
      C.wires (List.ofFn x) ++ [C.eval (List.ofFn x) || x 0, C.eval (List.ofFn x)] := by
  let w := C.wires (List.ofFn x)
  have len : w.length=14+C.size := length_wires C x
  have isOld : C.output<w.length := len ▸ (valid_output C correct).1
  change (C.gates++[joinGate C,meetGate C]).foldl step (List.ofFn x) = _
  rw [List.foldl_append]
  change step (step w (joinGate C)) (meetGate C) = w++[w.getD C.output false || x 0,w.getD C.output false]
  have r : w.getD 0 false = x 0 := raw C x
  simp only [step,joinGate,meetGate,List.map_cons,List.map_nil,GateOp.eval,List.any_cons,
    List.all_cons,id_eq,List.any_nil,List.all_nil,Bool.or_false,Bool.and_true,r,earlier isOld,←len]
  simp [List.getD_eq_getElem?_getD,List.append_assoc]
  exact Or.inl

theorem pad_eval (C : Circuit) (correct : Spec C) (x : Fin 14 → Bool) :
    (pad C).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  rw [Circuit.eval,pad_wires C correct]
  change (_ ++ [_,_]).getD (14+C.size+1) false = _
  rw [←length_wires C x]
  simp [List.getD_eq_getElem?_getD]

def derivative (C : Circuit) (base : List Bool) (start : Nat → Bool) (i : Nat) : Bool :=
  if i < 14 then start i else
    match C.gates[i-14]? with
    | some ⟨op,[a,b]⟩ =>
      if _h : a < i ∧ b < i then
        match op with
        | .and => (base.getD a false && derivative C base start b) ||
                    (derivative C base start a && base.getD b false)
        | .or => derivative C base start a || derivative C base start b
        | _ => false
      else false
    | _ => false
termination_by i

theorem derivative_raw (C : Circuit) (base : List Bool) (start : Nat → Bool) {i : Nat} (h : i<14) :
    derivative C base start i=start i := by rw [derivative]; simp [h]

def Rules (C : Circuit) (base : List Bool) (v : Nat → Bool) := ∀ k g a b,
  C.gates[k]? = some g → g.inputs=[a,b] →
    (g.op=.and → v (14+k) = ((base.getD a false && v b) || (v a && base.getD b false))) ∧
    (g.op=.or → v (14+k) = (v a || v b))

theorem derivative_rules (C : Circuit) (normal : Normal C) (base : List Bool) (start : Nat → Bool) :
    Rules C base (derivative C base start) := by
  intro k g a b hg hab
  obtain ⟨_,c,d,cd,_,hc,hd⟩ := normal k g hg
  obtain ⟨rfl,rfl⟩ : a=c ∧ b=d := by simpa using hab.symm.trans cd
  obtain ⟨op,ins⟩ := g
  dsimp at hab
  subst ins
  rw [derivative]
  simp only [ite_eq_right (show ¬14+k<14 by omega),Nat.add_sub_cancel_left,hg]
  constructor <;> intro opEq <;> subst op <;> simp [hc,hd]

theorem dead_output (C : Circuit) (correct : Spec C) (s : Fin 14) (nz : s ≠ 0)
    (v : Nat → Bool) (rules : Rules (pad C) ((pad C).wires (List.ofFn (single s))) v) :
    v (pad C).output=false := by
  have atLast : (pad C).gates[C.size+1]?=some (meetGate C) := by
    simp [pad,Circuit.size]
  have out := (rules (C.size+1) (meetGate C) _ _ atLast rfl).1 rfl
  have len := length_wires C (single s)
  have valid : C.output<(C.wires (List.ofFn (single s))).length := len ▸ (valid_output C correct).1
  rw [pad_wires C correct,earlier valid] at out
  change _ = ((C.eval _ && _) || (_ && _)) at out
  rw [single_off C correct s,←len] at out
  have z : single s 0 = false := by simp [single,Ne.symm nz]
  simpa [pad,Nat.add_assoc,List.getD_eq_getElem?_getD,List.getElem?_append_right,z] using out

def Trace (C : Circuit) (base initial : Fin 14) : Prop :=
  ∃ v : Nat → Bool, (∀ i : Fin 14, v i.val = decide (i=initial)) ∧
    Rules C (C.wires (List.ofFn (single base))) v ∧ v C.output=false

theorem trace_of_vanishing (C : Circuit) (normal : Normal C) (base initial : Fin 14)
    (dead : ∀ v, Rules C (C.wires (List.ofFn (single base))) v → v C.output=false) :
    Trace C base initial := by
  let wires := C.wires (List.ofFn (single base))
  let start (i : Nat) : Bool := decide (i=initial.val)
  let v := derivative C wires start
  have rules : Rules C wires v := derivative_rules C normal wires start
  refine ⟨v,?_,rules,dead v rules⟩
  intro i
  change derivative C wires start i.val = _
  rw [derivative_raw C wires start i.isLt]
  simp [start,Fin.ext_iff]

theorem trace_of_dark_and (C : Circuit) (normal : Normal C) (base initial : Fin 14)
    {k a b : Nat} (output : C.output=14+k) (gate : C.gates[k]?=some ⟨.and,[a,b]⟩)
    (da : (C.wires (List.ofFn (single base))).getD a false=false)
    (db : (C.wires (List.ofFn (single base))).getD b false=false) : Trace C base initial := by
  apply trace_of_vanishing C normal
  intro v rules
  have eq := (rules k _ a b gate rfl).1 rfl
  rw [da,db] at eq
  simpa only [output,Bool.false_and,Bool.and_false,Bool.or_self] using eq

def Posted : Prop := ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 27 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧ ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (14 + ky) = (((C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 14 => decide (ey = Fin.castAdd 7 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 7, w mx.val = decide (mx = p) ∧ w (7 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + kx) = (((C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 14 => decide (ex = Fin.natAdd 7 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + kx) = (w cx || w dx))) ∧ w C.output = false)

theorem finish (C : Circuit) (bound : C.size ≤ 27) (normal : Normal C) (correct : Spec C)
    (p l : Fin 7) (incident : p=l ∨ p=l+1 ∨ p=l+3)
    (P : Trace C (Fin.castAdd 7 p) (Fin.natAdd 7 l))
    (L : Trace C (Fin.natAdd 7 l) (Fin.castAdd 7 p)) : Posted := by
  obtain ⟨v,vin,vr,vout⟩ := P
  obtain ⟨w,win,wr,wout⟩ := L
  refine ⟨C,bound,normal,correct,p,l,incident,⟨v,?_,vr,vout⟩,w,?_,wr,wout⟩
  · intro m
    refine ⟨?_,?_⟩
    · have h := vin (Fin.castAdd 7 m)
      simpa [Fin.ext_iff,show m.val ≠ l.val+7 by omega] using h
    · have h := vin (Fin.natAdd 7 m)
      simpa [Fin.ext_iff,Nat.add_comm 7] using h
  · intro m
    refine ⟨?_,?_⟩
    · have h := win (Fin.castAdd 7 m)
      simpa [Fin.ext_iff] using h
    · have h := win (Fin.natAdd 7 m)
      simpa [Fin.ext_iff,Nat.add_comm 7,show m.val+7 ≠ p.val by omega] using h

theorem from_small (C : Circuit) (size : C.size ≤ 25) (normal : Normal C) (correct : Spec C) : Posted := by
  have pnorm := pad_normal C normal correct
  apply finish (pad C) (by simpa [pad,Circuit.size] using (Nat.add_le_add_right size 2)) pnorm
    (fun x => (pad_eval C correct x) ▸ correct x) 1 1 (Or.inl rfl)
  · apply trace_of_vanishing (pad C) pnorm
    exact dead_output C correct point (by decide)
  · apply trace_of_vanishing (pad C) pnorm
    exact dead_output C correct line (by decide)

end FanoPadding

#print axioms FanoPadding.from_small
