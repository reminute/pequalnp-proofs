import MooreCore
import CorePeel
import EdgeInputs

namespace GirthFiveCore

open Finset SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

/-- A linear edge bound on all nonempty high-degree cores already bounds the
    entire graph. Every discarded vertex is an essential input of this circuit. -/
theorem all_edges_of_core (C : Circuit) (mono : Monotone2 C)
    (computes : circuitFun n C = graphFun G ∅) (D K : ℕ)
    (coreBound : ∀ S ⊆ G.edgeFinset,
      (∀ v, (atVertex S v).card = 0 ∨ D < (atVertex S v).card) → S.card ≤ K*(C.size+1)) :
    G.edgeFinset.card ≤ (K+D)*(C.size+1) := by
  obtain ⟨T,sub,core,cost⟩ := peel D G.edgeFinset
  rw [ends_edges] at cost
  have b := coreBound T sub core
  have a := Nat.mul_le_mul_left D (edge_inputs G C (mono_fan mono) computes)
  rw [Nat.add_mul]
  omega

/-- The local degree-squared bound follows without any assumption on clean owners. -/
theorem size_of_core (C : Circuit) (mono : Monotone2 C)
    (computes : circuitFun n C = graphFun G ∅) (girth : LongCycles G)
    (S : Finset (Sym2 (Fin n))) (inside : S ⊆ G.edgeFinset) (edgePresent : S.Nonempty)
    (D : ℕ) (high : ∀ v, (atVertex S v).card = 0 ∨ D < (atVertex S v).card) :
    (D+1)*(D+1) ≤ C.size := by
  classical
  let H := fromEdgeSet (S : Set (Sym2 (Fin n)))
  have he : H.edgeFinset = S := by
    ext e
    simp only [mem_edgeFinset,H,edgeSet_fromEdgeSet,Set.mem_sdiff,Finset.mem_coe]
    exact ⟨And.left,fun h => ⟨h,G.not_isDiag_of_mem_edgeSet (mem_edgeFinset.mp (inside h))⟩⟩
  have sub : H ≤ G := by
    intro a b hab
    exact mem_edgeFinset.mp (inside ((fromEdgeSet_adj _).mp hab).1)
  have safe : LongCycles H := by
    intro v w hw
    simpa using girth v (w.mapLe sub) (hw.mapLe sub)
  have act : H.support.Nonempty := by
    obtain ⟨e,hm⟩ := edgePresent
    induction e using Sym2.inductionOn with
    | _ a b =>
      have ha : H.Adj a b := mem_edgeFinset.mp (he ▸ hm)
      exact ⟨a,b,ha⟩
  have minimum (v) (hv : v ∈ H.support) : D+1 ≤ H.degree v := by
    have pos := (H.degree_pos_iff_mem_support v).mpr hv
    have eq : (atVertex S v).card = H.degree v := by
      rw [← H.card_incidenceFinset_eq_degree v,H.incidenceFinset_eq_filter,he]
      rfl
    rcases high v with zero | many <;> omega
  have moore := moore_min safe minimum act
  have suppSub : H.support.toFinset ⊆ G.support.toFinset := by
    intro v hv
    obtain ⟨w,hw⟩ := Set.mem_toFinset.mp hv
    exact Set.mem_toFinset.mpr ⟨w,sub hw⟩
  have cap := (card_le_card suppSub).trans (edge_inputs G C (mono_fan mono) computes)
  omega

end GirthFiveCore
