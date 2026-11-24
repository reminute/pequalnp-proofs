import OwnershipBase

namespace FanoCert

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_1490

/-- On a positive two-input assignment, choose one child of each OR and both
    children of each AND. Indices count the two kinds of leaves and AND depth.
    A shared subcircuit is counted once for each occurrence in this tree. -/
inductive Cert (n : ℕ) (C : Circuit) (p l : Fin n) : ℕ → ℕ → ℕ → ℕ → Prop
  | point : Cert n C p l p.val 1 0 0
  | line : Cert n C p l l.val 0 1 0
  | left {j a b P L d} (gate : C.gates[j]? = some ⟨.or,[a,b]⟩) (ha : a < n+j) (hb : b < n+j)
      (child : Cert n C p l a P L d) : Cert n C p l (n+j) P L d
  | right {j a b P L d} (gate : C.gates[j]? = some ⟨.or,[a,b]⟩) (ha : a < n+j) (hb : b < n+j)
      (child : Cert n C p l b P L d) : Cert n C p l (n+j) P L d
  | both {j a b P L d Q M e} (gate : C.gates[j]? = some ⟨.and,[a,b]⟩) (ha : a < n+j) (hb : b < n+j)
      (lhs : Cert n C p l a P L d) (rhs : Cert n C p l b Q M e) :
      Cert n C p l (n+j) (P+Q) (L+M) (max d e+1)

/-- Actual gate evaluation and the first-order gate equations from the desk. -/
structure LinearRun (n : ℕ) (C : Circuit) (base deriv : ℕ → Bool) : Prop where
  plus : ∀ {j a b}, C.gates[j]? = some ⟨.or,[a,b]⟩ → a < n+j → b < n+j →
    base (n+j) = (base a || base b) ∧ deriv (n+j) = (deriv a || deriv b)
  times : ∀ {j a b}, C.gates[j]? = some ⟨.and,[a,b]⟩ → a < n+j → b < n+j →
    base (n+j) = (base a && base b) ∧ deriv (n+j) = ((base a && deriv b) || (deriv a && base b))

theorem gate_eq {n : ℕ} {C : Circuit} {xs : List Bool} (len : xs.length = n) {j a b : ℕ} {op : GateOp}
    (gate : C.gates[j]? = some ⟨op,[a,b]⟩) (ha : a < n+j) (hb : b < n+j) :
    val C xs (n+j) = op.eval [val C xs a,val C xs b] := by
  have valid : j < C.gates.length := by
    by_contra! h
    simp [List.getElem?_eq_none h] at gate
  rw [val_gate len valid]
  simp [gateAt,List.getD_eq_getElem?_getD,gate,ha,hb]

theorem of_derivative {n : ℕ} {C : Circuit} {xs : List Bool} (len : xs.length = n) (d : ℕ → Bool)
    (rules : ∀ j g a b, C.gates[j]? = some g → g.inputs = [a,b] →
      (g.op = .and → d (n+j) = ((val C xs a && d b) || (d a && val C xs b))) ∧
      (g.op = .or → d (n+j) = (d a || d b))) : LinearRun n C (val C xs) d := by
  constructor
  · intro j a b gate ha hb
    exact ⟨by simpa [GateOp.eval] using gate_eq len gate ha hb,(rules j _ a b gate rfl).2 rfl⟩
  · intro j a b gate ha hb
    exact ⟨by simpa [GateOp.eval] using gate_eq len gate ha hb,(rules j _ a b gate rfl).1 rfl⟩

variable {n : ℕ} {C : Circuit} {p l : Fin n} {w P L d : ℕ}

theorem flip (h : Cert n C p l w P L d) : Cert n C l p w L P d := by
  induction h with
  | point => exact .line
  | line => exact .point
  | left g a b _ ih => exact .left g a b ih
  | right g a b _ ih => exact .right g a b ih
  | both g a b _ _ ih jh => exact .both g a b ih jh

theorem zero_one (h : Cert n C p l w P L d) {base deriv : ℕ → Bool}
    (run : LinearRun n C base deriv) (anchor : base p.val = true) (direction : deriv l.val = true) :
    (L = 0 → base w = true) ∧ (L = 1 → deriv w = true) := by
  induction h with
  | point => exact ⟨fun _ => anchor,by simp⟩
  | line => exact ⟨by simp,fun _ => direction⟩
  | left gate ha hb _ ih =>
    obtain ⟨value,slope⟩ := run.plus gate ha hb
    exact ⟨fun z => by simp [value,ih.1 z],fun o => by simp [slope,ih.2 o]⟩
  | right gate ha hb _ ih =>
    obtain ⟨value,slope⟩ := run.plus gate ha hb
    exact ⟨fun z => by simp [value,ih.1 z],fun o => by simp [slope,ih.2 o]⟩
  | @both j a b p1 l1 d1 p2 l2 d2 gate ha hb _ _ ih jh =>
    obtain ⟨value,slope⟩ := run.times gate ha hb
    constructor
    · intro z
      simp [value,ih.1 (by omega : l1 = 0),jh.1 (by omega : l2 = 0)]
    · intro o
      have split : (l1 = 0 ∧ l2 = 1) ∨ (l1 = 1 ∧ l2 = 0) := by omega
      rcases split with ⟨z,o⟩ | ⟨o,z⟩
      · simp [slope,ih.1 z,jh.2 o]
      · simp [slope,ih.2 o,jh.1 z]

theorem leaves_le (h : Cert n C p l w P L d) : P+L ≤ 2^d := by
  induction h with
  | point | line => decide
  | left _ _ _ _ ih | right _ _ _ _ ih => exact ih
  | @both _ _ _ _ _ d1 _ _ d2 _ _ _ _ _ ih jh =>
    have a := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_max_left d1 d2)
    have b := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_max_right d1 d2)
    rw [Nat.pow_succ]
    omega

theorem multiplicity (h : Cert n C p l w P L d) {bp dp bl dl : ℕ → Bool}
    (xy : LinearRun n C bp dl) (yx : LinearRun n C bl dp)
    (a : bp p.val = true) (b : bl l.val = true) (da : dp p.val = true) (db : dl l.val = true)
    (offP : bp w = false) (offL : bl w = false) (offDP : dp w = false) (offDL : dl w = false) :
    2 ≤ P ∧ 2 ≤ L := by
  have ⟨z,o⟩ := zero_one h xy a db
  have ⟨u,v⟩ := zero_one (flip h) yx b da
  simp [offP,offL,offDP,offDL] at z o u v
  omega

theorem shallow_detected (h : Cert n C p l w P L d) (depth : d ≤ 1) {bp dp bl dl : ℕ → Bool}
    (xy : LinearRun n C bp dl) (yx : LinearRun n C bl dp)
    (a : bp p.val = true) (b : bl l.val = true) (da : dp p.val = true) (db : dl l.val = true)
    (offP : bp w = false) (offL : bl w = false) : dp w = true ∧ dl w = true := by
  obtain ⟨z,o⟩ := zero_one h xy a db
  obtain ⟨u,v⟩ := zero_one (flip h) yx b da
  simp [offP,offL] at z u
  have two := (leaves_le h).trans (Nat.pow_le_pow_right (by decide : 0 < 2) depth)
  norm_num at two
  exact ⟨v (by omega),o (by omega)⟩

/-- A normal binary monotone circuit that is true on the pair supplies a
    certificate, for any designated wire, including raw and invalid outputs. -/
theorem cert_of_true (C : Circuit) (p l : Fin n)
    (normal : ∀ j g, C.gates[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ, g.inputs = [a,b] ∧ a < n+j ∧ b < n+j)
    (w : ℕ) (on : val C (List.ofFn (fun v => decide (v = p ∨ v = l))) w = true) :
    ∃ P L d : ℕ, Cert n C p l w P L d := by
  let xs := List.ofFn (fun v => decide (v = p ∨ v = l))
  change val C xs w = true at on
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w < n
    · let i : Fin n := ⟨w,raw⟩
      rw [val_input (List.length_ofFn (f := fun v => decide (v = p ∨ v = l))) raw] at on
      have chosen : i = p ∨ i = l := by
        simpa [xs,List.getD_eq_getElem?_getD,i,raw] using on
      rcases chosen with eq | eq
      · have hw : w = p.val := congrArg Fin.val eq
        exact hw ▸ ⟨1,0,0,Cert.point⟩
      · have hw : w = l.val := congrArg Fin.val eq
        exact hw ▸ ⟨0,1,0,Cert.line⟩
    · by_cases invalid : n+C.gates.length ≤ w
      · have off : val C xs w = false := val_ge List.length_ofFn invalid
        simp [off] at on
      · let j := w-n
        have eq : w = n+j := by dsimp [j]; omega
        have hj : j < C.gates.length := by omega
        have found : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
        obtain ⟨op,⟨a,b,inputs,ha,hb⟩⟩ := normal j _ found
        let g := C.gates[j]
        have shape (s : Gate) (hs : s.inputs = [a,b]) : s = ⟨s.op,[a,b]⟩ := by
          cases s
          simpa using hs
        have gs := shape g inputs
        have gate : C.gates[j]? = some ⟨g.op,[a,b]⟩ := found.trans (congrArg some gs)
        rw [eq,gate_eq (xs := xs) List.length_ofFn gate ha hb] at on
        change g.op = .and ∨ g.op = .or at op
        rcases op with prod | plus
        · simp [prod,GateOp.eval] at on
          obtain ⟨P,L,d,ca⟩ := ih a (ha.trans_eq eq.symm) on.1
          obtain ⟨Q,M,e,cb⟩ := ih b (hb.trans_eq eq.symm) on.2
          rw [eq]
          exact ⟨_,_,_,Cert.both (prod ▸ gate) ha hb ca cb⟩
        · simp [plus,GateOp.eval] at on
          rcases on with ona | onb
          · obtain ⟨P,L,d,h⟩ := ih a (ha.trans_eq eq.symm) ona
            exact ⟨P,L,d,eq ▸ Cert.left (plus ▸ gate) ha hb h⟩
          · obtain ⟨P,L,d,h⟩ := ih b (hb.trans_eq eq.symm) onb
            exact ⟨P,L,d,eq ▸ Cert.right (plus ▸ gate) ha hb h⟩

/-- Conversely, a nonzero derivative reconstructs a certificate with exactly
    one direction leaf. The simultaneous induction also recovers a zero-leaf
    certificate from a true value on the anchor singleton. -/
theorem recover (C : Circuit) (p l : Fin n) {base deriv : ℕ → Bool} (run : LinearRun n C base deriv)
    (rawBase : ∀ i : Fin n, base i.val = decide (i = p))
    (rawDeriv : ∀ i : Fin n, deriv i.val = decide (i = l))
    (normal : ∀ j g, C.gates[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ, g.inputs = [a,b] ∧ a < n+j ∧ b < n+j)
    (w : ℕ) (valid : w < n+C.gates.length) :
    (base w = true → ∃ P d, Cert n C p l w P 0 d) ∧
    (deriv w = true → ∃ P d, Cert n C p l w P 1 d) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w < n
    · let i : Fin n := ⟨w,raw⟩
      constructor
      · intro on
        have eq := of_decide_eq_true ((rawBase i).symm.trans on)
        have hw : w = p.val := congrArg Fin.val eq
        exact hw ▸ ⟨1,0,Cert.point⟩
      · intro on
        have eq := of_decide_eq_true ((rawDeriv i).symm.trans on)
        have hw : w = l.val := congrArg Fin.val eq
        exact hw ▸ ⟨0,0,Cert.line⟩
    · let j := w-n
      have eq : w = n+j := by dsimp [j]; omega
      have hj : j < C.gates.length := by omega
      let g := C.gates[j]
      have found : C.gates[j]? = some g := List.getElem?_eq_getElem hj
      obtain ⟨op,⟨a,b,ins,ha,hb⟩⟩ := normal j g found
      have shape (s : Gate) (hs : s.inputs = [a,b]) : s = ⟨s.op,[a,b]⟩ := by cases s; simpa using hs
      have gate : C.gates[j]? = some ⟨g.op,[a,b]⟩ := found.trans (congrArg some (shape g ins))
      have la := ih a (ha.trans_eq eq.symm) (by omega)
      have lb := ih b (hb.trans_eq eq.symm) (by omega)
      rw [eq]
      rcases op with prod | plus
      · have atAnd : C.gates[j]? = some ⟨.and,[a,b]⟩ := prod ▸ gate
        obtain ⟨v,f⟩ := run.times atAnd ha hb
        constructor
        · intro h
          obtain ⟨x,y⟩ := Bool.and_eq_true_iff.mp (v.symm.trans h)
          obtain ⟨P,d,left⟩ := la.1 x
          obtain ⟨Q,e,right⟩ := lb.1 y
          exact ⟨_,_,Cert.both atAnd ha hb left right⟩
        · intro h
          rcases Bool.or_eq_true_iff.mp (f.symm.trans h) with s | s
          · obtain ⟨x,y⟩ := Bool.and_eq_true_iff.mp s
            obtain ⟨P,d,left⟩ := la.1 x
            obtain ⟨Q,e,right⟩ := lb.2 y
            exact ⟨_,_,Cert.both atAnd ha hb left right⟩
          · obtain ⟨x,y⟩ := Bool.and_eq_true_iff.mp s
            obtain ⟨P,d,left⟩ := la.2 x
            obtain ⟨Q,e,right⟩ := lb.1 y
            exact ⟨_,_,Cert.both atAnd ha hb left right⟩
      · have atOr : C.gates[j]? = some ⟨.or,[a,b]⟩ := plus ▸ gate
        obtain ⟨v,f⟩ := run.plus atOr ha hb
        have build {b1 b2 r : Bool} {m : ℕ} (on : r = (b1 || b2))
            (left : b1 = true → ∃ P d, Cert n C p l a P m d)
            (right : b2 = true → ∃ P d, Cert n C p l b P m d)
            (yes : r = true) : ∃ P d, Cert n C p l (n+j) P m d := by
          rcases Bool.or_eq_true_iff.mp (on.symm.trans yes) with z | z
          · obtain ⟨P,d,t⟩ := left z
            exact ⟨P,d,Cert.left atOr ha hb t⟩
          · obtain ⟨P,d,t⟩ := right z
            exact ⟨P,d,Cert.right atOr ha hb t⟩
        exact ⟨build v la.1 lb.1,build f la.2 lb.2⟩

theorem derivative_iff (C : Circuit) (p l : Fin n) {base deriv : ℕ → Bool} (run : LinearRun n C base deriv)
    (rawBase : ∀ i : Fin n, base i.val = decide (i = p))
    (rawDeriv : ∀ i : Fin n, deriv i.val = decide (i = l))
    (normal : ∀ j g, C.gates[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ, g.inputs = [a,b] ∧ a < n+j ∧ b < n+j)
    (w : ℕ) (valid : w < n+C.gates.length) :
    deriv w = true ↔ ∃ P d, Cert n C p l w P 1 d := by
  constructor
  · exact (recover C p l run rawBase rawDeriv normal w valid).2
  · rintro ⟨P,d,h⟩
    exact (zero_one h run (by simp [rawBase]) (by simp [rawDeriv])).2 rfl

theorem double_miss_iff (C : Circuit) (p l : Fin n) {bp dp bl dl : ℕ → Bool}
    (xy : LinearRun n C bp dl) (yx : LinearRun n C bl dp)
    (pBase : ∀ i : Fin n, bp i.val = decide (i = p)) (pDeriv : ∀ i : Fin n, dp i.val = decide (i = p))
    (lBase : ∀ i : Fin n, bl i.val = decide (i = l)) (lDeriv : ∀ i : Fin n, dl i.val = decide (i = l))
    (normal : ∀ j g, C.gates[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ, g.inputs = [a,b] ∧ a < n+j ∧ b < n+j)
    (w : ℕ) (valid : w < n+C.gates.length) (offP : bp w = false) (offL : bl w = false) :
    (dp w = false ∧ dl w = false) ↔ ∀ P L d, Cert n C p l w P L d → 2 ≤ P ∧ 2 ≤ L := by
  constructor
  · rintro ⟨a,b⟩ P L d cert
    exact multiplicity cert xy yx (by simp [pBase]) (by simp [lBase]) (by simp [pDeriv])
      (by simp [lDeriv]) offP offL a b
  · intro heavy
    constructor
    · cases on : dp w with
      | false => rfl
      | true =>
        obtain ⟨Q,d,cert⟩ := (derivative_iff C l p yx lBase pDeriv normal w valid).mp on
        have bad := (heavy _ _ _ (flip cert)).1
        omega
    · cases on : dl w with
      | false => rfl
      | true =>
        obtain ⟨Q,d,cert⟩ := (derivative_iff C p l xy pBase lDeriv normal w valid).mp on
        have bad := (heavy _ _ _ cert).2
        omega

end FanoCert

#print axioms FanoCert.shallow_detected
#print axioms FanoCert.multiplicity
#print axioms FanoCert.cert_of_true
#print axioms FanoCert.derivative_iff
#print axioms FanoCert.double_miss_iff
