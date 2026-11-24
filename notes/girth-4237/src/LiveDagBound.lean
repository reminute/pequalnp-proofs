import DagBound
import EffectiveReads

namespace GirthEdgeBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership GirthEdgeNegatives GirthFiveCore

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
variable {S : Finset (Sym2 (Fin n))} {C : Circuit}

/-- Each extra distinct consumer in the output cone is charged once.
    The read at the circuit output counts as a consumer. -/
theorem edges_with_live_sharing (sub : S ⊆ G.edgeFinset) (girth : GirthFive G)
    (mono : Monotone2 C) (computes : circuitFun n C = graphFun G ∅) :
    S.card ≤ C.size+1 + ∑ j : Fin C.gates.length,
      (liveReads n C j - 1) * ((sampleBlock S G (gateVal n C j.val)).rank - 1) := by
  let ρ (f : GirthWires.Signal n) := (sampleBlock S G f).rank
  have upper := live_sharing_bound ρ 1 (sample_sums S G) (raw_rank sub) C mono
  rw [computes,one_mul] at upper
  exact (output_rank sub girth).trans upper

end GirthEdgeBound

#print axioms GirthEdgeBound.edges_with_live_sharing
