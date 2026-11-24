import EdgePartner
import SuffixBarrier

namespace Cubic1971.TwoInputBarrier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open StarReader

theorem and_reader {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (v a b : Fin n) (ordinary : ∀ {u w}, G.Adj u w → u ∉ A)
    (girth : GirthEdgeNegatives.GirthFive G) (degree : (G.neighborSet v).ncard = 3)
    (hv : v ∉ A) (ha : a ∉ A) (hb : b ∉ A) (av : a ≠ v) (bv : b ≠ v)
    (C : Circuit) (pre post : List Gate) (r : Gate) (k : Nat)
    (layout : C.gates = pre ++ r :: post) (legal : FanInTwo C)
    (sole : ∀ g ∈ pre ++ post, ¬effective v.val g) (op : r.op = .and)
    (args : r.inputs = [v.val,k] ∨ r.inputs = [k,v.val]) (other : k ≠ v.val)
    (output : C.output ≠ v.val) (correct : circuitFun n C = graphFun G A)
    (least : ∀ s, HasCircuitSize n (graphFun G A) s → C.size ≤ s)
    (readsPair : ∀ x y : Fin n → Bool, x a = y a → x b = y b →
      (run pre (List.ofFn x)).getD k false = (run pre (List.ofFn y)).getD k false) :
    G.Adj a b ∧ (∀ x : Fin n → Bool, (run pre (List.ofFn x)).getD k false = !(x a && x b)) ∧
    ∃ g ∈ post, g.op = .not := by
  obtain ⟨edge,table⟩ := EdgePartner.forced_edge G A v a b @ordinary girth degree hv ha hb av bv
    C pre post r k true layout legal sole op args other output correct least readsPair
  have nand (x : Fin n → Bool) : (run pre (List.ofFn x)).getD k false = !(x a && x b) := by
    rw [table]
    cases x a <;> cases x b <;> rfl
  refine ⟨edge,nand,SuffixBarrier.needs_not C _ v pre post r layout legal correct least ?_ ?_⟩
  · intro x
    rcases args with h | h <;>
      simp only [gateValue,h,op,List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,
        id_eq,Bool.and_true,Bool.and_eq_true] <;> tauto
  · intro x off
    have no : ¬(x a = true ∧ x b = true) := by
      rintro ⟨one,two⟩
      have yes : graphFun G A x = true := by
        simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
        exact Or.inr ⟨a,b,edge,one,two⟩
      exact Bool.noConfusion (off.symm.trans yes)
    have on : (run pre (List.ofFn x)).getD k false = true := by
      rw [nand]
      cases pa : x a <;> cases pb : x b <;> simp_all
    rcases args with h | h <;>
      simp only [gateValue,h,op,List.map_cons,List.map_nil,GateOp.eval,List.all_cons,
        List.all_nil,id_eq,on,Bool.and_true,Bool.true_and]

end Cubic1971.TwoInputBarrier

#print axioms Cubic1971.TwoInputBarrier.and_reader
