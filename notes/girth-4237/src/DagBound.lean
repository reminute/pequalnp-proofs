import EdgeBound
import RankCircuitBound
import MatrixWires

namespace GirthEdgeBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership GirthEdgeNegatives GirthFiveCore

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
variable {S : Finset (Sym2 (Fin n))} {C : Circuit}

theorem sample_sums (S : Finset (Sym2 (Fin n))) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    GirthWires.Sums (fun f => (sampleBlock S G f).rank) :=
  GirthWires.matrix_sums (GirthRank.mat (edgeRows S)) (GirthRank.positive (edgeRows S))
    (GirthRank.negative (edgeRows S) G.Adj)

/-- The rank at the output bounds the edge count, while each repeated gate
    of rank at most B contributes at most B per additional read. -/
theorem dag_bound (sub : S ⊆ G.edgeFinset) (girth : GirthFive G)
    (mono : Monotone2 C) (computes : circuitFun n C = graphFun G ∅)
    {B : ℕ} (positive : 1 ≤ B)
    (shared : ∀ j : Fin C.gates.length, 1 < gateReads (n := n) C j →
      (sampleBlock S G (gateVal n C j.val)).rank ≤ B) :
    S.card ≤ B * (C.size + 1) := by
  let ρ (f : GirthWires.Signal n) := (sampleBlock S G f).rank
  have small (v : Fin n) : ρ (fun x => x v) ≤ B := (raw_rank sub v).trans positive
  have upper := signal_bound ρ B (sample_sums S G) small C mono shared
  rw [computes] at upper
  exact (output_rank sub girth).trans upper

/-- Any violation of the bound gives a gate of the original circuit, with
    at least two actual reads and rank greater than B on the chosen edges. -/
theorem large_shared_gate (sub : S ⊆ G.edgeFinset) (girth : GirthFive G)
    (mono : Monotone2 C) (computes : circuitFun n C = graphFun G ∅)
    {B : ℕ} (positive : 1 ≤ B) (excess : B * (C.size + 1) < S.card) :
    ∃ j : Fin C.gates.length, 1 < gateReads (n := n) C j ∧
      B < (sampleBlock S G (gateVal n C j.val)).rank := by
  by_contra! none
  exact (Nat.not_lt_of_ge (dag_bound sub girth mono computes positive none)) excess

theorem single_use_bound (sub : S ⊆ G.edgeFinset) (girth : GirthFive G)
    (mono : Monotone2 C) (computes : circuitFun n C = graphFun G ∅)
    (single : ∀ j : Fin C.gates.length, gateReads (n := n) C j ≤ 1) :
    S.card ≤ C.size + 1 := by
  simpa using dag_bound sub girth mono computes (B := 1) (by decide)
    (fun j shared => (Nat.not_lt_of_ge (single j) shared).elim)

/-- Charge every read beyond the first by the rank of that gate beyond one. -/
theorem edges_with_extra_reads (sub : S ⊆ G.edgeFinset) (girth : GirthFive G)
    (mono : Monotone2 C) (computes : circuitFun n C = graphFun G ∅) :
    S.card ≤ C.size+1 + ∑ j : Fin C.gates.length,
      (gateReads (n := n) C j - 1) * ((sampleBlock S G (gateVal n C j.val)).rank - 1) := by
  let ρ (f : GirthWires.Signal n) := (sampleBlock S G f).rank
  have upper := signal_with_extra_reads ρ 1 (sample_sums S G) (raw_rank sub) C mono
  rw [computes,one_mul] at upper
  exact (output_rank sub girth).trans upper

end GirthEdgeBound
