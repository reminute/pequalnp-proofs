import FlagOrbits
import SignalFactor
import FanoPadding

namespace FirstAndPartner

open FanoFactor FanoFlag PEqualNP.CircuitLowerBounds

-- Propagating a true signal through an OR input gives a semantic implication.
-- Paths of length zero are included.
inductive OrPath (C : Circuit) (w : ℕ) : ℕ → Prop where
  | start : OrPath C w w
  | left {j a b} (g : C.gates[j]?=some ⟨.or,[a,b]⟩)
      (ha : a<14+j) (hb : b<14+j) (lower : OrPath C w a) : OrPath C w (14+j)
  | right {j a b} (g : C.gates[j]?=some ⟨.or,[a,b]⟩)
      (ha : a<14+j) (hb : b<14+j) (lower : OrPath C w b) : OrPath C w (14+j)

theorem along {C : Circuit} {w z : ℕ} (p : OrPath C w z) (x : Input)
    (on : signal C w x = true) : signal C z x = true := by
  induction p with
  | start => exact on
  | left g ha hb _ ih => simp [equation g ha hb,GateOp.eval,ih]
  | right g ha hb _ ih => simp [equation g ha hb,GateOp.eval,ih]

private theorem incident_of_pair : ∀ a b : V, incidence (pairAt a b)=true ↔ adj a b=true := by
  decide +kernel

private theorem common_shore : ∀ a b c : V, adj a c=true → adj b c=true →
    (a.val<7 ↔ b.val<7) := by decide +kernel

set_option maxHeartbeats 2000000 in
private theorem common_unique : ∀ a b c d : V, a≠b → adj a c=true → adj b c=true →
    adj a d=true → adj b d=true → c=d := by decide +kernel

/-- Suppose an AND produces only legal Fano incidences. If one operand accepts
    singleton inputs a and b, every singleton accepted by the other operand
    must be a common neighbor of a and b. -/
theorem common_partner {A B : Input → Bool} (ma : Increasing A) (mb : Increasing B)
    (sound : ∀ x, A x=true → B x=true → incidence x=true) {a b c : V}
    (aa : A (unitAt a)=true) (ab : A (unitAt b)=true) (bc : B (unitAt c)=true) :
    adj a c=true ∧ adj b c=true := by
  have one (i : V) (h : A (unitAt i)=true) : adj i c=true := by
    apply (incident_of_pair i c).mp
    exact sound _ (ma _ _ (by simp [unitAt,pairAt]) h) (mb _ _ (by simp [unitAt,pairAt]) bc)
  exact ⟨one a aa,one b ab⟩

theorem partner_constraint {C : Circuit} (normal : FanoPadding.Normal C)
    (correct : FanoPadding.Spec C) (a b : V) (ne : a≠b) {j u v : ℕ}
    (first : C.gates[0]?=some ⟨.or,[a.val,b.val]⟩)
    (prefixPath : OrPath C 14 u) (con : C.gates[j]?=some ⟨.and,[u,v]⟩)
    (hu : u<14+j) (hv : v<14+j) (suffixPath : OrPath C (14+j) C.output) :
    (∀ c : V, signal C v (unitAt c)=true → adj a c=true ∧ adj b c=true) ∧
    (¬(a.val<7 ↔ b.val<7) → ∀ c : V, signal C v (unitAt c)=false) ∧
    (∀ c d : V, signal C v (unitAt c)=true → signal C v (unitAt d)=true → c=d) := by
  have rawSignal (r s : V) : signal C r.val (unitAt s)=decide (r=s) := by
    rw [signal,PEqualNP.Outside.L_meta_1490.val_input List.length_ofFn r.isLt]
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using r.isLt)]
    simp only [Option.getD_some,List.getElem_ofFn,unitAt]
  have base (r : V) (h : r=a ∨ r=b) : signal C u (unitAt r)=true := by
    apply along prefixPath
    rw [show (14 : ℕ)=14+0 by rfl,equation first a.isLt b.isLt,rawSignal,rawSignal]
    rcases h with rfl|rfl <;> simp [GateOp.eval]
  have sound (x : Input) (aOn : signal C u x=true) (bOn : signal C v x=true) : incidence x=true := by
    have hit : signal C (14+j) x=true := by simp [equation con hu hv,GateOp.eval,aOn,bOn]
    simpa only [incidence,decide_eq_true_eq] using (correct x).mp (along suffixPath x hit)
  have neighborhood (c : V) (on : signal C v (unitAt c)=true) : adj a c=true ∧ adj b c=true :=
    common_partner (increasing_signal C normal u) (increasing_signal C normal v)
      sound (base a (Or.inl rfl)) (base b (Or.inr rfl)) on
  refine ⟨neighborhood,?_,?_⟩
  · intro mixed c
    apply Bool.eq_false_iff.mpr
    intro on
    obtain ⟨h1,h2⟩ := neighborhood c on
    exact mixed (common_shore a b c h1 h2)
  · intro c d hc hd
    obtain ⟨ac,bc⟩ := neighborhood c hc
    obtain ⟨ad,bd⟩ := neighborhood d hd
    exact common_unique a b c d ne ac bc ad bd

end FirstAndPartner

#print axioms FirstAndPartner.partner_constraint
