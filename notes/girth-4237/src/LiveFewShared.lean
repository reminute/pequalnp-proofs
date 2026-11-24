import FewShared
import LivePrefix

namespace GirthEdgeBound

open GirthWires GirthFiveCore GirthPotential GirthExceptions
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership GirthEdgeNegatives

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
variable {S : Finset (Sym2 (Fin n))} {C : Circuit}

/-- Count distinct multiply-consumed signals, within the output cone, whose
    rank on the chosen positive and negative inputs exceeds B. -/
noncomputable def liveHigh (S : Finset (Sym2 (Fin n))) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (B : ℕ) : Finset (Fin C.gates.length) := by
  classical
  exact Finset.univ.filter fun j => 1 < liveReads n C j ∧ B < (sampleBlock S G (gateVal n C j.val)).rank

/-- A live gate can represent later high-rank shared gates when their
    positive rows and negative columns both lie in its sampled rectangle. -/
theorem live_covered (sub : S ⊆ G.edgeFinset) (girth : GirthFive G)
    (mono : Monotone2 C) (computes : circuitFun n C = graphFun G ∅) {B k : ℕ} (one : 1 ≤ B)
    (T : Finset (Fin C.gates.length)) (few : T.card ≤ k)
    (active : ∀ t ∈ T, ReachesOutput n C (n+t.val))
    (cover : ∀ i ∈ liveHigh S G C B, ∃ t ∈ T, t.val ≤ i.val ∧
      Covers (GirthRank.positive (edgeRows S)) (GirthRank.negative (edgeRows S) G.Adj)
        (gateVal n C t.val) (gateVal n C i.val)) : S.card ≤ (2^(k+1)-1)*B*(C.size+1) := by
  classical
  let E := edgeRows S
  let pos := GirthRank.positive E
  let neg := GirthRank.negative E G.Adj
  let M := GirthRank.mat E
  have upper := cover_bound pos neg C B (fun i => 1 < liveReads n C i)
    (fun i => ReachesOutput n C (n+i.val)) (fun A inputs all => by
      have old := live_sharing_bound (weight A pos neg) B (matrix_sums A pos neg) inputs C mono
      have zero (j : Fin C.gates.length) :
          (liveReads n C j-1) * (weight A pos neg (gateVal n C j.val)-B) = 0 := by
        by_cases h : 1 < liveReads n C j
        · simp [Nat.sub_eq_zero_of_le (all j h)]
        · simp [Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h)]
      simpa only [zero, Finset.sum_const_zero,Nat.add_zero] using old)
    (fun A inputs j live => live_gate_signal_bound (weight A pos neg) B (matrix_sums A pos neg) inputs C mono j live)
    k M T few active (fun v => (raw_rank sub v).trans one) (fun i _ many => by
      by_cases small : weight M pos neg (gateVal n C i.val) ≤ B
      · exact Or.inl small
      · exact Or.inr (cover i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,many,Nat.lt_of_not_ge small⟩)))
  rw [computes,closed_budget,← Nat.mul_assoc] at upper
  exact (output_rank sub girth).trans upper

theorem live_few_shared (sub : S ⊆ G.edgeFinset) (girth : GirthFive G)
    (mono : Monotone2 C) (computes : circuitFun n C = graphFun G ∅) {B k : ℕ} (one : 1 ≤ B)
    (few : (liveHigh S G C B).card ≤ k) : S.card ≤ (2^(k+1)-1)*B*(C.size+1) := by
  apply live_covered sub girth mono computes one (liveHigh S G C B) few
  · exact fun _ hi => reaches_of_live_reads (Nat.zero_lt_one.trans (Finset.mem_filter.mp hi).2.1)
  · exact fun i hi => ⟨i,hi,le_refl _,fun _ fp => fp,fun _ fn => fn⟩

end GirthEdgeBound

#print axioms GirthEdgeBound.live_few_shared
#print axioms GirthEdgeBound.live_covered
