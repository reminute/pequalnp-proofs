import TwinGraph
import TwinReads

namespace Edge606.TwinReaderBarrier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity GirthEdgeNegatives

/-- A vertex of degree at least two is distinguished from every other vertex by
    a gate that reads precisely one of them. In particular they cannot have the
    same sole reader. The two endpoints need not have the same degree. -/
theorem distinct_reader {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (girth : GirthFive G) (C : Circuit) (mono : Monotone2 C)
    (computes : circuitFun n C = GraphDensity.edgeFunction G) {u v : Fin n} (uv : u ≠ v)
    (degree : 2 ≤ G.degree u ∨ 2 ≤ G.degree v) :
    ∃ j : Fin C.gates.length,
      (u.val ∈ (C.gates.get j).inputs ∧ v.val ∉ (C.gates.get j).inputs) ∨
      (v.val ∈ (C.gates.get j).inputs ∧ u.val ∉ (C.gates.get j).inputs) := by
  classical
  by_contra! no
  have paired (j : Fin C.gates.length) :
      u.val ∈ (C.gates.get j).inputs ↔ v.val ∈ (C.gates.get j).inputs := by
    have both := no j
    tauto
  obtain ⟨smallU,smallV⟩ := TwinGraph.degree_le_one_of_swap G girth uv
    (TwinReads.graph_swap G C mono computes uv paired)
  omega

end Edge606.TwinReaderBarrier

#print axioms Edge606.TwinReaderBarrier.distinct_reader
