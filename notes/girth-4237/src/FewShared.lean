import RankExceptions
import EdgeBound

namespace GirthEdgeBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership GirthEdgeNegatives GirthFiveCore

variable {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
variable {S : Finset (Sym2 (Fin n))} {C : Circuit}

/-- Gates read at least twice whose sample-block rank exceeds the input allowance. -/
noncomputable def highSet (S : Finset (Sym2 (Fin n))) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (B : Nat) : Finset (Fin C.gates.length) := by
  classical
  exact Finset.univ.filter fun j => 1<gateReads (n:=n) C j ∧ B<(sampleBlock S G (gateVal n C j.val)).rank

@[simp] theorem mem_highSet {B : Nat} {j : Fin C.gates.length} :
    j ∈ highSet S G C B ↔ 1<gateReads (n:=n) C j ∧ B<(sampleBlock S G (gateVal n C j.val)).rank := by
  classical
  simp [highSet]

theorem few_shared (sub : S ⊆ G.edgeFinset) (girth : GirthFive G)
    (mono : Monotone2 C) (computes : circuitFun n C=graphFun G ∅)
    {B k : Nat} (positive : 1≤B) (few : (highSet S G C B).card≤k) :
    S.card ≤ (2^(k+1)-1)*B*(C.size+1) := by
  classical
  have small (j : Fin C.gates.length) (absent : j ∉ highSet S G C B) (shared : 1<gateReads (n:=n) C j) :
      (sampleBlock S G (gateVal n C j.val)).rank≤B := by
    apply Nat.le_of_not_gt
    exact fun high => absent (mem_highSet.mpr ⟨shared,high⟩)
  have upper := GirthExceptions.bounded (GirthRank.positive (edgeRows S)) (GirthRank.negative (edgeRows S) G.Adj)
    C mono B k (GirthRank.mat (edgeRows S)) (highSet S G C B) few
    (fun v => (raw_rank sub v).trans positive) small
  change (sampleBlock S G (circuitFun n C)).rank ≤ GirthExceptions.budget (B*(C.size+1)) k at upper
  rw [computes,GirthExceptions.closed_budget,← Nat.mul_assoc] at upper
  exact (output_rank sub girth).trans upper

theorem high_set_bound (sub : S ⊆ G.edgeFinset) (girth : GirthFive G)
    (mono : Monotone2 C) (computes : circuitFun n C=graphFun G ∅) {B : Nat} (positive : 1≤B) :
    S.card ≤ (2^((highSet S G C B).card+1)-1)*B*(C.size+1) :=
  few_shared sub girth mono computes positive le_rfl

theorem at_most_one_high (sub : S ⊆ G.edgeFinset) (girth : GirthFive G)
    (mono : Monotone2 C) (computes : circuitFun n C=graphFun G ∅) (one : (highSet S G C 1).card≤1) :
    S.card≤3*(C.size+1) := by
  simpa using few_shared sub girth mono computes (B:=1) (k:=1) (by decide) one

theorem at_most_two_high (sub : S ⊆ G.edgeFinset) (girth : GirthFive G)
    (mono : Monotone2 C) (computes : circuitFun n C=graphFun G ∅) (two : (highSet S G C 1).card≤2) :
    S.card≤7*(C.size+1) := by
  simpa using few_shared sub girth mono computes (B:=1) (k:=2) (by decide) two

theorem many_high_of_large (sub : S ⊆ G.edgeFinset) (girth : GirthFive G)
    (mono : Monotone2 C) (computes : circuitFun n C=graphFun G ∅)
    {B k : Nat} (positive : 1≤B) (large : (2^(k+1)-1)*B*(C.size+1)<S.card) :
    k<(highSet S G C B).card := by
  by_contra! few
  exact large.not_ge (few_shared sub girth mono computes positive few)

end GirthEdgeBound

#print axioms GirthEdgeBound.high_set_bound
