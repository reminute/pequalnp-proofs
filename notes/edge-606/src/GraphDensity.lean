import EdgeInputs
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace Edge606.GraphDensity

open Finset SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

abbrev edgeFunction (x : Fin n → Bool) :=
  decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)

/-- The two assignments differ only at the named vertex. A neighbor alone rejects
    whereas the two endpoints of their edge accept. -/
theorem essential_iff (v : Fin n) :
    (∃ x y : Fin n → Bool, (∀ i, i ≠ v → x i = y i) ∧ edgeFunction G x ≠ edgeFunction G y) ↔
    v ∈ G.support := by
  classical
  constructor
  · rintro ⟨x,y,agree,unequal⟩
    by_contra away
    apply unequal
    apply Bool.eq_iff_iff.mpr
    simp only [edgeFunction,decide_eq_true_eq]
    have both {i j : Fin n} (ij : G.Adj i j) : i ≠ v ∧ j ≠ v :=
      ⟨fun h => away (h ▸ ⟨j,ij⟩),fun h => away (h ▸ ⟨i,ij.symm⟩)⟩
    constructor <;> rintro ⟨i,j,ij,hi,hj⟩
    · exact ⟨i,j,ij,(agree i (both ij).1).symm.trans hi,(agree j (both ij).2).symm.trans hj⟩
    · exact ⟨i,j,ij,(agree i (both ij).1).trans hi,(agree j (both ij).2).trans hj⟩
  · rintro ⟨w,vw⟩
    let x (i : Fin n) := decide (i = w)
    let y (i : Fin n) := decide (i = v ∨ i = w)
    refine ⟨x,y,fun i hi => by simp [x,y,hi],?_⟩
    have off : edgeFunction G x = false := by simp [edgeFunction,x]
    have on : edgeFunction G y = true := by
      apply decide_eq_true
      exact ⟨v,w,vw,by simp [y],by simp [y]⟩
    simp [off,on]

theorem support_bound (C : Circuit) (fan : FanInTwo C) (computes : circuitFun n C = edgeFunction G) :
    G.support.toFinset.card ≤ C.size + 1 := by
  apply GirthFiveCore.edge_inputs G C fan
  rw [computes]
  funext x
  apply Bool.eq_iff_iff.mpr
  simp [edgeFunction,NestedCover.graphFun]

theorem degree_sum_on_support :
    ∑ v ∈ G.support.toFinset, G.degree v = 2 * G.edgeFinset.card := by
  classical
  rw [← G.sum_degrees_eq_twice_card_edges]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro v _ away
  by_contra nonzero
  exact away (Set.mem_toFinset.mpr ((G.degree_pos_iff_mem_support v).mp (Nat.pos_of_ne_zero nonzero)))

theorem bounded_degree (C : Circuit) (fan : FanInTwo C) (computes : circuitFun n C = edgeFunction G)
    (d : Nat) (degree : ∀ v ∈ G.support, G.degree v ≤ d) :
    2 * G.edgeFinset.card ≤ d * (C.size + 1) := by
  classical
  rw [← degree_sum_on_support]
  calc
    _ ≤ ∑ _v ∈ G.support.toFinset, d :=
      Finset.sum_le_sum (fun v hv => degree v (Set.mem_toFinset.mp hv))
    _ = d * G.support.toFinset.card := by simp [Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left d (support_bound G C fan computes)

theorem subforest (C : Circuit) (fan : FanInTwo C) (computes : circuitFun n C = edgeFunction G)
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (sub : F ≤ G) (forest : F.IsAcyclic) :
    F.edgeFinset.card ≤ C.size := by
  classical
  by_cases nonempty : Nonempty F.support
  · let _ := nonempty
    have edge := (forest.induce F.support).ncard_edgeSet_add_one_le_card
    rw [← Nat.card_coe_set_eq,Nat.card_eq_fintype_card,← (F.induce F.support).edgeFinset_card,
      F.card_edgeFinset_induce_support] at edge
    have active : F.support.toFinset ⊆ G.support.toFinset := by
      intro u hu
      obtain ⟨w,uw⟩ := Set.mem_toFinset.mp hu
      exact Set.mem_toFinset.mpr ⟨w,sub uw⟩
    have count := (Finset.card_le_card active).trans (support_bound G C fan computes)
    rw [Nat.card_eq_fintype_card,← Set.toFinset_card] at edge
    omega
  · have zero : F.edgeFinset = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      induction e using Sym2.inductionOn with
      | _ u v => exact nonempty ⟨⟨u,v,SimpleGraph.mem_edgeFinset.mp he⟩⟩
    simp [zero]

theorem forest (C : Circuit) (fan : FanInTwo C) (computes : circuitFun n C = edgeFunction G)
    (acyclic : G.IsAcyclic) : G.edgeFinset.card ≤ C.size :=
  subforest G C fan computes G le_rfl acyclic

/-- A cover by r forests gives the arboricity coefficient r, with no cost for
    isolated vertices and no need for the forests to be edge-disjoint. -/
theorem forest_cover (C : Circuit) (fan : FanInTwo C) (computes : circuitFun n C = edgeFunction G)
    {r : Nat} (F : Fin r → SimpleGraph (Fin n)) [∀ j, DecidableRel (F j).Adj]
    (acyclic : ∀ j, (F j).IsAcyclic) (cover : ∀ u v, G.Adj u v ↔ ∃ j, (F j).Adj u v) :
    G.edgeFinset.card ≤ r * C.size := by
  classical
  have sub (j : Fin r) : F j ≤ G := fun u v h => (cover u v).mpr ⟨j,h⟩
  have inside : G.edgeFinset ⊆ Finset.univ.biUnion (fun j => (F j).edgeFinset) := by
    intro e edge
    induction e using Sym2.inductionOn with
    | _ a b =>
      obtain ⟨j,h⟩ := (cover a b).mp (SimpleGraph.mem_edgeFinset.mp edge)
      exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,SimpleGraph.mem_edgeFinset.mpr h⟩
  calc
    _ ≤ _ := (Finset.card_le_card inside).trans Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin r, C.size := Finset.sum_le_sum fun j _ => subforest G C fan computes _ (sub j) (acyclic j)
    _ = _ := by simp

end Edge606.GraphDensity

#print axioms Edge606.GraphDensity.essential_iff
#print axioms Edge606.GraphDensity.degree_sum_on_support
#print axioms Edge606.GraphDensity.bounded_degree
#print axioms Edge606.GraphDensity.forest
#print axioms Edge606.GraphDensity.forest_cover
