import DeskCertificates

namespace Fano2348

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_1490 FanoCert

def pairX (a c v : Fin 14) : Bool := decide (v=a ∨ v=c)
def isEdge (a c : Fin 14) : Prop := ∃ p l : Fin 7, (p=l ∨ p=l+1 ∨ p=l+3) ∧
  pairX a c (Fin.castAdd 7 p) = true ∧ pairX a c (Fin.natAdd 7 l) = true
instance (a c : Fin 14) : Decidable (isEdge a c) := by unfold isEdge; infer_instance

/-- Every ordered pair of different Fano vertices can be distinguished by
    holding one additional vertex fixed. This includes same-shore pairs. -/
theorem separate_pair : ∀ a b : Fin 14, a≠b → ∃ c : Fin 14, isEdge a c ∧ ¬isEdge b c := by decide +kernel

theorem separate_away : ∀ a b : Fin 14, a≠b → ∃ c : Fin 14,
    c≠a ∧ c≠b ∧ isEdge a c ∧ ¬isEdge b c := by decide +kernel

/-- A path starting at the raw source and using gate outputs only after gate
    zero. Each step records an actual earlier operand of its successor. -/
inductive Bypass (C : Circuit) (source : ℕ) : ℕ → Prop
  | raw : Bypass C source source
  | extend {j w : ℕ} (later : 0<j) (valid : j<C.size) (read : w ∈ (gateAt C j).inputs)
      (earlier : w<14+j) (path : Bypass C source w) : Bypass C source (14+j)

theorem bypass_reader {C : Circuit} {a w : ℕ} (path : Bypass C a w) :
    w=a ∨ ∃ j, 0<j ∧ j<C.size ∧ a ∈ (gateAt C j).inputs := by
  induction path with
  | raw => exact Or.inl rfl
  | extend later valid use _ _ ih =>
    rcases ih with eq | earlier
    · exact Or.inr ⟨_,later,valid,eq ▸ use⟩
    · exact Or.inr earlier

theorem pair_raw (C : Circuit) (a c i : Fin 14) : val C (List.ofFn (pairX a c)) i.val = pairX a c i := by
  rw [val_input List.length_ofFn i.isLt,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]

def PrivateReader (C : Circuit) (a b : ℕ) (j : ℕ) :=
  0<j ∧ j<C.size ∧ a ∈ (gateAt C j).inputs ∧ b ∉ (gateAt C j).inputs

theorem first_ordered_switch (C : Circuit) (ao : IsAO2 14 C) (correct : spec C) (a b : Fin 14) (different : a≠b)
    (first : C.gates[0]?=some ⟨.or,[a.val,b.val]⟩ ∨ C.gates[0]?=some ⟨.or,[b.val,a.val]⟩) :
    Bypass C a.val C.output ∧ (C.output = a.val ∨ ∃ j, PrivateReader C a.val b.val j) := by
  obtain ⟨c,ca,cb,adj,nonadj⟩ := separate_away a b different
  let X := List.ofFn (pairX a c)
  let Y := List.ofFn (pairX b c)
  have on : val C X C.output = true := (correct _).mpr adj
  have off : val C Y C.output = false := by
    apply Bool.eq_false_iff.mpr
    exact fun yes => nonadj ((correct _).mp yes)
  have zeroOn : val C Y (14+0) = true := by
    have cb : val C Y b.val = true := (pair_raw C b c b).trans (by simp [pairX])
    rcases first with forward | backward
    · rw [gate_eq (xs := Y) List.length_ofFn forward a.isLt b.isLt]
      simp [GateOp.eval,cb]
    · rw [gate_eq (xs := Y) List.length_ofFn backward b.isLt a.isLt]
      simp [GateOp.eval,cb]
  have Xa : val C X a.val = true := (pair_raw C a c a).trans (by simp [pairX])
  have Xb : val C X b.val = false := (pair_raw C a c b).trans (by simp [pairX,different.symm,cb.symm])
  have Ya : val C Y a.val = false := (pair_raw C b c a).trans (by simp [pairX,different,ca.symm])
  have Yb : val C Y b.val = true := (pair_raw C b c b).trans (by simp [pairX])
  have descend (w : ℕ) : val C X w = true → val C Y w = false →
      Bypass C a.val w ∧ (w = a.val ∨ ∃ j, PrivateReader C a.val b.val j) := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro high low
      by_cases raw : w<14
      · let i : Fin 14 := ⟨w,raw⟩
        have t : pairX a c i = true := (pair_raw C a c i).symm.trans high
        have f : pairX b c i = false := (pair_raw C b c i).symm.trans low
        have hit : i=a := by
          simp only [pairX,decide_eq_true_eq] at t
          rcases t with h | h
          · exact h
          · simp [pairX,h] at f
        have same : w = a.val := congrArg Fin.val hit
        exact ⟨same ▸ Bypass.raw,Or.inl same⟩
      · by_cases invalid : 14+C.gates.length ≤ w
        · have dead : val C X w=false := val_ge (n := 14) List.length_ofFn invalid
          exact False.elim (Bool.noConfusion (dead.symm.trans high))
        · let j := w-14
          have eq : w=14+j := by dsimp [j]; omega
          have valid : j<C.gates.length := by omega
          have later : 0<j := by
            by_contra! no
            have ix : w=14+0 := by omega
            exact Bool.noConfusion (zeroOn.symm.trans (ix ▸ low))
          let g := C.gates[j]
          have found : C.gates[j]?=some g := List.getElem?_eq_getElem valid
          obtain ⟨kind,⟨u,v,ins,hu,hv⟩⟩ := normal ao j g found
          have shape (s : Gate) (hs : s.inputs=[u,v]) : s=⟨s.op,[u,v]⟩ := by cases s; simpa using hs
          have gate := found.trans (congrArg some (shape g ins))
          have same := (lookup found).2
          rw [eq,gate_eq (xs := X) List.length_ofFn gate hu hv] at high
          rw [eq,gate_eq (xs := Y) List.length_ofFn gate hu hv] at low
          have exclusive : a.val ∈ (gateAt C j).inputs → b.val ∉ (gateAt C j).inputs := by
            intro readsA readsB
            rw [same,ins] at readsA readsB
            simp only [List.mem_cons,List.not_mem_nil,or_false] at readsA readsB
            have distinct : a.val ≠ b.val := fun h => different (Fin.ext h)
            have orders : (u=a.val ∧ v=b.val) ∨ (u=b.val ∧ v=a.val) := by
              rcases readsA with a1 | a2 <;> rcases readsB with b1 | b2 <;> omega
            rcases orders with ⟨huv,hvu⟩ | ⟨huv,hvu⟩ <;> rcases kind with op | op <;>
              simp [huv,hvu,op,Xa,Xb,Ya,Yb,GateOp.eval] at high low
          have split : (val C X u=true ∧ val C Y u=false) ∨ (val C X v=true ∧ val C Y v=false) := by
            have andDiff : ∀ a b c d : Bool, (a && b)=true → (c && d)=false →
                (a=true ∧ c=false) ∨ (b=true ∧ d=false) := by decide
            have orDiff : ∀ a b c d : Bool, (a || b)=true → (c || d)=false →
                (a=true ∧ c=false) ∨ (b=true ∧ d=false) := by decide
            rcases kind with op | op <;> simp only [op,GateOp.eval,List.all_cons,List.all_nil,List.any_cons,List.any_nil,
              id_eq,Bool.and_true,Bool.or_false] at high low
            · exact andDiff _ _ _ _ high low
            · exact orDiff _ _ _ _ high low
          have step {q : ℕ} (read : q ∈ (gateAt C j).inputs) (lt : q<14+j)
              (h : val C X q=true ∧ val C Y q=false) : Bypass C a.val w ∧
              (w=a.val ∨ ∃ j, PrivateReader C a.val b.val j) := by
            obtain ⟨path,orig | prev⟩ := ih q (lt.trans_eq eq.symm) h.1 h.2
            · have readsA : a.val ∈ (gateAt C j).inputs := orig ▸ read
              exact ⟨eq ▸ .extend later valid read lt path,Or.inr ⟨j,later,valid,readsA,exclusive readsA⟩⟩
            · exact ⟨eq ▸ .extend later valid read lt path,Or.inr prev⟩
          rcases split with h | h
          · exact step (by simp [same,ins]) hu h
          · exact step (by simp [same,ins]) hv h
  exact descend _ on off

theorem first_ordered (C : Circuit) (ao : IsAO2 14 C) (correct : spec C) (a b : Fin 14) (different : a≠b)
    (first : C.gates[0]?=some ⟨.or,[a.val,b.val]⟩ ∨ C.gates[0]?=some ⟨.or,[b.val,a.val]⟩) :
    Bypass C a.val C.output := (first_ordered_switch C ao correct a b different first).1

theorem internal_output {C : Circuit} (correct : spec C) : 14 ≤ C.output := by
  by_contra! h
  let i : Fin 14 := ⟨C.output,h⟩
  have yes : val C (single i) C.output=true := (singleton_raw C i i).trans (by simp)
  exact Bool.noConfusion (yes.symm.trans (singleton_off correct i))

theorem different_private_readers {C : Circuit} (ao : IsAO2 14 C) (correct : spec C) (a b : Fin 14)
    (different : a ≠ b) (first : C.gates[0]?=some ⟨.or,[a.val,b.val]⟩ ∨ C.gates[0]?=some ⟨.or,[b.val,a.val]⟩) :
    ∃ j k, j≠k ∧ PrivateReader C a.val b.val j ∧ PrivateReader C b.val a.val k := by
  have lower := internal_output correct
  obtain ⟨j,jr⟩ := (first_ordered_switch C ao correct a b different first).2.resolve_left
    (fun h => (Nat.not_lt_of_ge lower) (h ▸ a.isLt))
  obtain ⟨k,kr⟩ := (first_ordered_switch C ao correct b a different.symm first.symm).2.resolve_left
    (fun h => (Nat.not_lt_of_ge lower) (h ▸ b.isLt))
  exact ⟨j,k,fun h => (h ▸ jr.2.2.2) kr.2.2.1,jr,kr⟩

theorem first_both_bypass {C : Circuit} (ao : IsAO2 14 C) (correct : spec C)
    (distinct : ∀ j<C.size, opnd C j 0 ≠ opnd C j 1) (isOr : (gateAt C 0).op=.or) :
    Bypass C (opnd C 0 0) C.output ∧ Bypass C (opnd C 0 1) C.output ∧
    ∀ s : Fin 2, ∃ j, 0<j ∧ j<C.size ∧ opnd C 0 s ∈ (gateAt C j).inputs := by
  have inside : C.output < 14+C.gates.length := by
    by_contra! bad
    have no := val_ge (C := C) (x := List.ofFn (fun v : Fin 14 => decide (v=0 ∨ v=7))) List.length_ofFn bad
    exact Bool.noConfusion (no.symm.trans (pair_on correct))
  have lower := internal_output correct
  have positive : 0<C.gates.length := by omega
  let g := C.gates[0]
  have found : C.gates[0]? = some g := List.getElem?_eq_getElem positive
  obtain ⟨_,⟨u,v,ins,hu,hv⟩⟩ := normal ao 0 g found
  let a : Fin 14 := ⟨u,by simpa using hu⟩
  let b : Fin 14 := ⟨v,by simpa using hv⟩
  have same := (lookup found).2
  have lft : opnd C 0 0 = a.val := by simp [opnd,same,ins,a]
  have rgt : opnd C 0 1 = b.val := by simp [opnd,same,ins,b]
  have ne := distinct 0 positive
  rw [lft,rgt] at ne
  have diff : a≠b := fun h => ne (congrArg Fin.val h)
  have shape (s : Gate) (op : s.op=.or) (args : s.inputs=[u,v]) : s=⟨.or,[u,v]⟩ := by
    cases s; simp_all
  have atFirst : C.gates[0]?=some ⟨.or,[a.val,b.val]⟩ := found.trans (congrArg some (shape g (same ▸ isOr) ins))
  have pa := first_ordered C ao correct a b diff (Or.inl atFirst)
  have pb := first_ordered C ao correct b a diff.symm (Or.inr atFirst)
  refine ⟨lft ▸ pa,rgt ▸ pb,?_⟩
  intro s
  fin_cases s
  · change ∃ j, 0<j ∧ j<C.size ∧ opnd C 0 0 ∈ (gateAt C j).inputs
    rw [lft]
    exact (bypass_reader pa).resolve_left (fun eq => (Nat.not_lt_of_ge lower) (eq ▸ a.isLt))
  · change ∃ j, 0<j ∧ j<C.size ∧ opnd C 0 1 ∈ (gateAt C j).inputs
    rw [rgt]
    exact (bypass_reader pb).resolve_left (fun eq => (Nat.not_lt_of_ge lower) (eq ▸ b.isLt))

end Fano2348

#print axioms Fano2348.first_both_bypass
#print axioms Fano2348.different_private_readers
