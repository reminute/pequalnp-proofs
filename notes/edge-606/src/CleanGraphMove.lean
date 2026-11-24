import CleanSignal
import CleanOr

namespace Edge606.CleanGraphMove

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Cubic1971.StarReader

/-- Move the partner of a short-prefix sole OR to the output without changing
    the size or the edge function. -/
theorem relocate {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n)
    (C : Circuit) (pre post : List Gate) (r : Gate) (k : Nat)
    (layout : C.gates = pre ++ r :: post) (mono : Monotone2 C)
    (sole : ∀ g ∈ pre ++ post, ¬effective v.val g)
    (args : r.inputs = [v.val,k] ∨ r.inputs = [k,v.val]) (other : k ≠ v.val)
    (output : C.output ≠ v.val) (computes : circuitFun n C = GraphDensity.edgeFunction G)
    (op : r.op = .or) (girth : GirthEdgeNegatives.GirthFive G)
    (short : pre.length + 1 < G.degree v) :
    let D := CleanOr.result n pre post C.output v.val k
    Monotone2 D ∧ D.size = C.size ∧ circuitFun n D = GraphDensity.edgeFunction G ∧
      ∀ x, GraphDensity.edgeFunction G x =
        (circuitFun n (CleanOr.bypass n pre post C.output v.val) x ||
         circuitFun n (⟨pre,k⟩ : Circuit) x) := by
  have safe := CleanSignal.short_safe G v C pre post r k layout mono sole args other
    output computes op girth short
  obtain ⟨mon,sz,eq⟩ := CleanOr.relocate C mono pre post r k v layout op args safe
  refine ⟨mon,sz,eq.trans computes,fun x => ?_⟩
  exact (congrFun (eq.trans computes) x).symm.trans
    (CleanOr.result_eval n pre post C.output v.val k x)

end Edge606.CleanGraphMove

#print axioms Edge606.CleanGraphMove.relocate
