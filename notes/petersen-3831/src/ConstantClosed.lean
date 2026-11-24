import EdgeAndCases
import L_meta_1667

namespace Petersen3831.Promotion

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open RawPartner

theorem checked_edge_01 : fixedAnd 0 1 := PEqualNP.Outside.L_meta_1667

theorem closed_constant {C : Circuit} {k a : Nat} (fan : FanInTwo C) (small : C.size≤14)
    (uq : unique C) (hk : k<C.gates.length) (positive : 0<a) (args : (NestedCover.gateAt C k).inputs=[0,a])
    (mode : ((NestedCover.gateAt C k).op=.and ∧ ∀ m, before C k m a=true) ∨
      ((NestedCover.gateAt C k).op=.or ∧ ∀ m, before C k m a=false)) :
    ∃x : Input,circuitFun 9 C (RawPartner.flip x) ≠ graph x := by
  by_contra! correct
  exact no_constant checked_edge_01 fan small uq hk positive args correct mode

end Petersen3831.Promotion

#print axioms Petersen3831.Promotion.closed_constant
