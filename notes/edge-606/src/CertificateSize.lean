import Sensitivity

namespace Edge606.Sensitivity

open Finset SimpleGraph Cubic1971.PartnerCertificate

variable {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

/-- Sizes of consistent partial assignments away from v that allow rejection
    and rule out every input on which v changes the edge function. -/
def blockingSizes (G : SimpleGraph (Fin n)) (v : Fin n) : Set Nat :=
  {m | ∃ P Z : Finset (Fin n), v ∉ P ∪ Z ∧ Disjoint P Z ∧ free G P ∧
    (P ∪ Z).card = m ∧ ¬∃ S, P ⊆ S ∧ Disjoint S Z ∧ sensitive G ∅ v S}

theorem least_blocking_size (girth : GirthEdgeNegatives.GirthFive G) (v : Fin n) :
    IsLeast (blockingSizes G v) (G.degree v) := by
  classical
  constructor
  · refine ⟨∅, G.neighborFinset v, by simp, by simp, by simp [free], by simp, ?_⟩
    rintro ⟨S,_,hz,_,_,_,w,inside,edge⟩
    exact disjoint_left.mp hz inside ((G.mem_neighborFinset _ _).mpr edge)
  · rintro m ⟨P,Z,away,apart,ind,card,blocks⟩
    by_contra! short
    exact blocks (complete_input girth P Z (fun hv => away (mem_union_left _ hv)) apart ind
      (card ▸ short))

end Edge606.Sensitivity

#print axioms Edge606.Sensitivity.least_blocking_size
