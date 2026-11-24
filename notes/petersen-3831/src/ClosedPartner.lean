import ConstantClosed
import L_meta_1670

namespace Petersen3831.Promotion

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open RawPartner

/-- These are the already checked Petersen representatives AND(0,1) and AND(0,4). -/
theorem checked_edges : fixedAnd 0 1 ∧ fixedAnd 0 4 :=
  ⟨checked_edge_01, PEqualNP.Outside.L_meta_1670⟩

theorem closed_or {C : Circuit} {k a : Nat} (fan : FanInTwo C) (small : C.size≤14)
    (uq : unique C) (hk : k<C.gates.length) (internal : 9≤a) (earlier : a<9+k)
    (op : (NestedCover.gateAt C k).op=.or) (args : (NestedCover.gateAt C k).inputs=[0,a])
    (i j : Fin 8) (different : i ≠ j) (t : Bool → Bool → Bool)
    (rep : ∀ m, before C k m a=t (Partner.bit m i) (Partner.bit m j)) :
    ∃x : Input,circuitFun 9 C (RawPartner.flip x) ≠ graph x :=
  binary_or_obstruction checked_edges fan small uq hk internal earlier op args i j different t rep

end Petersen3831.Promotion

#print axioms Petersen3831.Promotion.closed_or
