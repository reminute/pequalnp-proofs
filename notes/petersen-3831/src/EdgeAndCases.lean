import GatePromotion
import InputRenaming
import ErasePartner

namespace Petersen3831.Promotion

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open RawPartner

def fixedAnd (i j : Fin 9) : Prop := ∀ C : Circuit, FanInTwo C →
  (∀x : Input, (C.wires (List.ofFn x)).getD 9 false = (x i && x j)) →
  circuitFun 9 C = graph → 16 ≤ C.size

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1600000 in
/-- Only two existing fixed-AND cases are needed on edges of the residual graph. -/
theorem edge_fixed (representatives : fixedAnd 0 1 ∧ fixedAnd 0 4)
    (i j : Fin 8) (edge : Partner.adjacent i j=true) : fixedAnd i.succ j.succ := by
  let maps : Fin 12 → Fin 9 → Fin 9 := ![![0,1,2,3,4,5,6,7,8],
      ![1,2,3,8,6,0,7,4,5],
      ![2,3,8,5,7,1,4,6,0],
      ![3,2,1,0,4,8,7,6,5],
      ![2,1,0,5,7,3,6,4,8],
      ![3,8,5,0,4,2,6,7,1],
      ![1,0,5,8,6,2,4,7,3],
      ![8,3,2,1,6,5,4,7,0],
      ![0,5,8,3,4,1,7,6,2],
      ![5,0,1,2,7,8,4,6,3],
      ![5,8,3,2,7,0,6,4,1],
      ![8,5,0,1,6,3,7,4,2]]
  let pair (k : Fin 12) (a b : Fin 9) := (min (maps k a) (maps k b), max (maps k a) (maps k b))
  have cert : ∀ a b : Fin 8, Partner.adjacent a b=true → ∃ k : Fin 12,
      pair k a.succ b.succ ∈ ([(0,1),(0,4)] : List (Fin 9 × Fin 9)) := by decide +kernel
  have invariance (k : Fin 12) (x : Input) : graph (x ∘ maps k) = graph x := by
    fin_cases k
    · rfl
    · change ((x 1 && x 2) || (x 2 && x 3) || (x 3 && x 8) || (x 8 && x 6) || (x 6 && x 1) || (x 1 && x 0) || (x 2 && x 7) || (x 3 && x 4) || (x 8 && x 5) || (x 0 && x 4) || (x 7 && x 5) || (x 5 && x 0)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change ((x 2 && x 3) || (x 3 && x 8) || (x 8 && x 5) || (x 5 && x 7) || (x 7 && x 2) || (x 2 && x 1) || (x 3 && x 4) || (x 8 && x 6) || (x 5 && x 0) || (x 1 && x 6) || (x 4 && x 0) || (x 0 && x 1)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change ((x 3 && x 2) || (x 2 && x 1) || (x 1 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 3 && x 8) || (x 2 && x 7) || (x 1 && x 6) || (x 0 && x 5) || (x 8 && x 6) || (x 7 && x 5) || (x 5 && x 8)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change ((x 2 && x 1) || (x 1 && x 0) || (x 0 && x 5) || (x 5 && x 7) || (x 7 && x 2) || (x 2 && x 3) || (x 1 && x 6) || (x 0 && x 4) || (x 5 && x 8) || (x 3 && x 4) || (x 6 && x 8) || (x 8 && x 3)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change ((x 3 && x 8) || (x 8 && x 5) || (x 5 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 3 && x 2) || (x 8 && x 6) || (x 5 && x 7) || (x 0 && x 1) || (x 2 && x 7) || (x 6 && x 1) || (x 1 && x 2)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change ((x 1 && x 0) || (x 0 && x 5) || (x 5 && x 8) || (x 8 && x 6) || (x 6 && x 1) || (x 1 && x 2) || (x 0 && x 4) || (x 5 && x 7) || (x 8 && x 3) || (x 2 && x 7) || (x 4 && x 3) || (x 3 && x 2)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change ((x 8 && x 3) || (x 3 && x 2) || (x 2 && x 1) || (x 1 && x 6) || (x 6 && x 8) || (x 8 && x 5) || (x 3 && x 4) || (x 2 && x 7) || (x 1 && x 0) || (x 5 && x 7) || (x 4 && x 0) || (x 0 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change ((x 0 && x 5) || (x 5 && x 8) || (x 8 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 1) || (x 5 && x 7) || (x 8 && x 6) || (x 3 && x 2) || (x 1 && x 6) || (x 7 && x 2) || (x 2 && x 1)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change ((x 5 && x 0) || (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 7) || (x 7 && x 5) || (x 5 && x 8) || (x 0 && x 4) || (x 1 && x 6) || (x 2 && x 3) || (x 8 && x 6) || (x 4 && x 3) || (x 3 && x 8)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change ((x 5 && x 8) || (x 8 && x 3) || (x 3 && x 2) || (x 2 && x 7) || (x 7 && x 5) || (x 5 && x 0) || (x 8 && x 6) || (x 3 && x 4) || (x 2 && x 1) || (x 0 && x 4) || (x 6 && x 1) || (x 1 && x 0)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change ((x 8 && x 5) || (x 5 && x 0) || (x 0 && x 1) || (x 1 && x 6) || (x 6 && x 8) || (x 8 && x 3) || (x 5 && x 7) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 7 && x 2) || (x 2 && x 3)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
  obtain ⟨k,hk⟩ := cert i j edge
  intro C fan wire comp
  let f := maps k
  let D := FanoRename.circuit f C
  have fan' : FanInTwo D := by
    intro g mem
    obtain ⟨old,hm,rfl⟩ := List.mem_map.mp mem
    simpa [FanoRename.gate] using fan old hm
  have first (x : Input) :
      (D.wires (List.ofFn x)).getD 9 false=(x (pair k i.succ j.succ).1 && x (pair k i.succ j.succ).2) := by
    have h := FanoRename.wires f C x 9
    rw [FanoRename.wire_high f (by decide : 9≤9),wire] at h
    refine h.trans ?_
    dsimp only [pair,Function.comp_apply,f]
    rcases le_total (maps k i.succ) (maps k j.succ) with le | le
    · simp [min_eq_left le,max_eq_right le]
    · simp [min_eq_right le,max_eq_left le,Bool.and_comm]
  have comp' : circuitFun 9 D = graph := by
    funext x
    exact (FanoRename.eval f C x).trans ((congrFun comp (x∘f)).trans (invariance k x))
  have result : 16≤D.size := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with h | h
    · rw [h] at first
      exact representatives.1 D fan' first comp'
    · rw [h] at first
      exact representatives.2 D fan' first comp'
  simpa only [D,FanoRename.size] using result

theorem exclude_binary_or (representatives : fixedAnd 0 1 ∧ fixedAnd 0 4)
    {C : Circuit} {k a : Nat} (fan : FanInTwo C) (small : C.size≤14)
    (uq : unique C) (hk : k<C.gates.length) (internal : 9≤a) (earlier : a<9+k)
    (op : (NestedCover.gateAt C k).op=.or) (args : (NestedCover.gateAt C k).inputs=[0,a])
    (correct : ∀x : Input,circuitFun 9 C (RawPartner.flip x)=graph x)
    (i j : Fin 8) (different : i ≠ j) (t : Bool → Bool → Bool)
    (rep : ∀ m, before C k m a = t (Partner.bit m i) (Partner.bit m j)) :
    ∀ m, before C k m a = false := by
  by_contra nonconstant
  obtain ⟨edge,D,fanD,size,first,computes⟩ := or_partner_promoted fan uq hk internal earlier op args
    correct i j different t rep nonconstant
  have bound := edge_fixed representatives i j edge D fanD first (funext computes)
  omega

/-- An enabling constant, in either reader mode, gives a two-gate padded circuit
    strictly smaller than the existing first-AND(0,1) lower bound. -/
theorem no_constant (bound : fixedAnd 0 1)
    {C : Circuit} {k a : Nat} (fan : FanInTwo C) (small : C.size≤14)
    (uq : unique C) (hk : k<C.gates.length) (positive : 0<a) (args : (NestedCover.gateAt C k).inputs=[0,a])
    (correct : ∀x : Input,circuitFun 9 C (RawPartner.flip x)=graph x)
    (mode : ((NestedCover.gateAt C k).op=.and ∧ ∀ m, before C k m a=true) ∨
      ((NestedCover.gateAt C k).op=.or ∧ ∀ m, before C k m a=false)) : False := by
  obtain ⟨short,shortFan,matchEval⟩ := ErasePartner.erase_enabled fan uq hk positive args mode
  obtain ⟨D,fanD,add,first,same⟩ := pad_first _ shortFan 0 1
  have enough := bound D fanD first (funext fun x => (same x).trans ((matchEval _).trans (correct x)))
  omega

theorem binary_or_obstruction (representatives : fixedAnd 0 1 ∧ fixedAnd 0 4)
    {C : Circuit} {k a : Nat} (fan : FanInTwo C) (small : C.size≤14)
    (uq : unique C) (hk : k<C.gates.length) (internal : 9≤a) (earlier : a<9+k)
    (op : (NestedCover.gateAt C k).op=.or) (args : (NestedCover.gateAt C k).inputs=[0,a])
    (i j : Fin 8) (different : i ≠ j) (t : Bool → Bool → Bool)
    (rep : ∀ m, before C k m a=t (Partner.bit m i) (Partner.bit m j)) :
    ∃x : Input,circuitFun 9 C (RawPartner.flip x) ≠ graph x := by
  by_contra! correct
  have constant := exclude_binary_or representatives fan small uq hk internal earlier op args correct i j different t rep
  exact no_constant representatives.1 fan small uq hk (by omega) args correct (Or.inr ⟨op,constant⟩)

end Petersen3831.Promotion

#print axioms Petersen3831.Promotion.exclude_binary_or
#print axioms Petersen3831.Promotion.binary_or_obstruction
