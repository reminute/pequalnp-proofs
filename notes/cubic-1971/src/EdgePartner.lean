import NormalForm
import SmallSupport

namespace Cubic1971.EdgePartner

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open StarReader PartnerCertificate

/-- If a physical partner in a minimum circuit depends on just two other
    ordinary inputs, then they form an actual edge. The partner's truth table
    is fixed, on all rows, including rows containing other edges or marks. -/
theorem forced_edge {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (v a b : Fin n) (ordinary : ∀ {u w}, G.Adj u w → u ∉ A)
    (girth : GirthEdgeNegatives.GirthFive G) (degree : (G.neighborSet v).ncard = 3)
    (hv : v ∉ A) (ha : a ∉ A) (hb : b ∉ A) (av : a ≠ v) (bv : b ≠ v)
    (C : Circuit) (pre post : List Gate) (r : Gate) (k : Nat) (isAnd : Bool)
    (layout : C.gates = pre ++ r :: post) (legal : FanInTwo C)
    (sole : ∀ g ∈ pre ++ post, ¬effective v.val g)
    (op : r.op = if isAnd then .and else .or)
    (args : r.inputs = [v.val,k] ∨ r.inputs = [k,v.val]) (other : k ≠ v.val)
    (output : C.output ≠ v.val) (correct : circuitFun n C = graphFun G A)
    (least : ∀ s, HasCircuitSize n (graphFun G A) s → C.size ≤ s)
    (readsPair : ∀ x y : Fin n → Bool, x a = y a → x b = y b →
      (run pre (List.ofFn x)).getD k false = (run pre (List.ofFn y)).getD k false) :
    G.Adj a b ∧ ∀ x : Fin n → Bool,
      (run pre (List.ofFn x)).getD k false = if x a && x b then !isAnd else isAnd := by
  classical
  have enabled := circuit_enabled C pre post r k isAnd layout legal sole op args other output correct hv
  have onPair : SmallSupport.Supported v {a,b} (physical pre k) := by
    intro S T _ _ h
    apply readsPair
    · simpa only [bits,decide_eq_decide] using h a (by simp)
    · simpa only [bits,decide_eq_decide] using h b (by simp)
  let row (x : Fin n → Bool) : Finset (Fin n) := Finset.univ.filter (fun u => u ≠ v ∧ x u = true)
  have mem (x : Fin n → Bool) (u : Fin n) (ne : u ≠ v) : u ∈ row x ↔ x u = true := by
    simp [row,ne]
  have away (x : Fin n → Bool) : v ∉ row x := by simp [row]
  have onRow (x : Fin n → Bool) : (run pre (List.ofFn x)).getD k false = physical pre k (row x) := by
    apply readsPair
    · simp [bits,mem x a av]
    · simp [bits,mem x b bv]
  rcases SmallSupport.ordinary_pair (physical pre k) isAnd enabled @ordinary girth degree a b
      av bv ha hb onPair with allRows | ⟨edge,table⟩
  · exfalso
    apply NormalForm.not_copy legal correct least layout v
    intro x
    have bit := (onRow x).trans (allRows _ (away x))
    simp only [List.getD_eq_getElem?_getD] at bit
    rcases args with h | h <;> cases isAnd <;> simp [gateValue,h,op,GateOp.eval,bit]
  · refine ⟨edge,fun x => ?_⟩
    rw [onRow,table _ (away x)]
    simp [mem x a av,mem x b bv]

end Cubic1971.EdgePartner

#print axioms Cubic1971.EdgePartner.forced_edge
