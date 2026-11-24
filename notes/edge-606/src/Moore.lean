import MooreCore
import EdgeInputs
import Mathlib.Algebra.Order.Chebyshev

namespace Edge606.Moore

open Finset SimpleGraph GirthFiveCore
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- Count a directed two-step walk by its middle vertex, allowing backtracking. -/
theorem neighbor_degree_total :
    ∑ v ∈ G.support.toFinset, ∑ w ∈ G.neighborFinset v, G.degree w =
      ∑ w ∈ G.support.toFinset, G.degree w ^ 2 := by
  classical
  have restrictNeighbors (f : V → ℕ) (v : V) :
      (∑ w ∈ G.support.toFinset, if G.Adj v w then f w else 0) =
        ∑ w ∈ G.neighborFinset v, f w := by
    rw [← sum_filter]
    have h : G.support.toFinset.filter (G.Adj v) = G.neighborFinset v := by
      ext w
      simp only [mem_filter, Set.mem_toFinset, mem_neighborFinset]
      exact ⟨And.right, fun e => ⟨⟨v, e.symm⟩, e⟩⟩
    rw [h]
  simp_rw [← restrictNeighbors (fun w => G.degree w)]
  rw [sum_comm]
  apply sum_congr rfl
  intro w _
  simp_rw [G.adj_comm _ w]
  rw [restrictNeighbors]
  simp [sq]

/-- The average-degree Moore bound, on just the nonisolated vertices. -/
theorem edge_square (girth : LongCycles G) :
    (2 * G.edgeFinset.card) ^ 2 ≤ G.support.toFinset.card ^ 2 * (G.support.toFinset.card - 1) := by
  classical
  let S := G.support.toFinset
  have total : ∑ v ∈ S, G.degree v = 2 * G.edgeFinset.card := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    exact sum_subset (subset_univ _) (fun v _ absent =>
      (G.degree_eq_zero_iff_notMem_support v).mpr (fun hv => absent (Set.mem_toFinset.mpr hv)))
  have second : ∑ v ∈ S, G.degree v ^ 2 ≤ S.card * (S.card - 1) := by
    rw [← neighbor_degree_total G]
    calc
      _ ≤ ∑ v ∈ S, (S.card - 1) := by
        apply sum_le_sum
        intro v hv
        have h := moore_sum girth v (Set.mem_toFinset.mp hv)
        change 1 + _ ≤ S.card at h
        omega
      _ = _ := by simp
  rw [← total]
  calc
    _ ≤ S.card * ∑ v ∈ S, G.degree v ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ S.card * (S.card * (S.card - 1)) := Nat.mul_le_mul_left _ second
    _ = _ := by ring

/-- An unconditional superlinear upper bound in the size of the posted circuit. -/
theorem circuit_edge_square {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (girth : LongCycles H) (C : Circuit) (mono : Monotone2 C)
    (computes : circuitFun n C = fun x => decide (∃ i j, H.Adj i j ∧ x i = true ∧ x j = true)) :
    (2 * H.edgeFinset.card) ^ 2 ≤ (C.size + 1) ^ 2 * C.size := by
  have model : circuitFun n C = graphFun H ∅ := by
    rw [computes]
    funext x
    simp [graphFun]
  have support := edge_inputs H C (mono_fan mono) model
  apply (edge_square H girth).trans
  exact Nat.mul_le_mul (Nat.pow_le_pow_left support 2) (by omega)

/-- A counterexample to a proposed coefficient r has more than 4 r² gates. -/
theorem size_of_excess {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (girth : LongCycles H) (C : Circuit) (mono : Monotone2 C)
    (computes : circuitFun n C = fun x => decide (∃ i j, H.Adj i j ∧ x i = true ∧ x j = true))
    (r : ℕ) (excess : r * (C.size + 1) < H.edgeFinset.card) : 4 * r ^ 2 < C.size := by
  have square := circuit_edge_square H girth C mono computes
  have strict : (2 * (r * (C.size + 1))) ^ 2 < (2 * H.edgeFinset.card) ^ 2 :=
    Nat.pow_lt_pow_left (by omega) (by decide)
  have h : (C.size + 1) ^ 2 * (4 * r ^ 2) < (C.size + 1) ^ 2 * C.size := by
    calc
      _ = (2 * (r * (C.size + 1))) ^ 2 := by ring
      _ < _ := strict.trans_le square
  exact Nat.lt_of_mul_lt_mul_left h

end Edge606.Moore

#print axioms Edge606.Moore.edge_square
#print axioms Edge606.Moore.circuit_edge_square
#print axioms Edge606.Moore.size_of_excess
