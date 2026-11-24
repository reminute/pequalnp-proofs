import TwoRoundBound
import GuardCircuit
import GuardNumericBridge
import GuardCaps

private abbrev graphDecision : DecidableRel G11Certificate.graph.Adj := inferInstance

set_option maxHeartbeats 2000000 in

theorem G11Residual.posted_no_rare_all : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x9 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x10 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         have x12 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3;         (∀ x13 ∈ x9,             have x15 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x13;             (∀ x16 ∈ x15 (0 : Fin (2 : ℕ)), ∀ x18 ∈ x15 (1 : Fin (2 : ℕ)), x1.Adj x16 x18) ∧ ((x15 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x15 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x14 x15 : Fin (11 : ℕ)), s(x14, x15) ∈ x11 → ∃ x17 ∈ x9, ∃ (x18 : Fin (2 : ℕ)) (x19 : ℕ), (x19 = x4 ∨ x19 = x5) ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x17 x18) x19 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true) → (17 : ℕ) + (x9 \ x10).card + (2 : ℕ) * x10.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x11.card → (∀ (x16 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x16 → x16.card ≤ (x9 \ x10).card) → x4 < x5 → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → ¬x12 x4 x5 → ¬x12 x5 x4 → (∃ x21 ∈ x9, x12 x4 x21 ∧ x12 x5 x21) → (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card = 0 → (22 : ℕ) ≤ x3.size := by
  intro G inst C i j hg least top
  dsimp only
  intro sides source count cover ord marked ij ji common rare
  obtain ⟨t,ht,it,jt⟩ := common
  change G = G11Certificate.graph at hg
  subst G
  have same : inst = graphDecision := Subsingleton.elim _ _
  subst inst
  have rareEmpty := Finset.card_eq_zero.mp rare
  let c := (PEqualNP.TopForm.centreless G11Certificate.graph C).card
  have positive : 0 < c := by
    by_cases member : t ∈ PEqualNP.TopForm.centreless G11Certificate.graph C
    · exact Finset.card_pos.mpr ⟨t,member⟩
    · have two := G11Structure.two_rare_of_common_top least.1 top ord.ne marked ij ji ht it jt member
      omega
  by_cases one : c = 1
  · exact G11Residual.no_rare_one least top (fun a ha => (sides a ha).1)
      source count cover ord marked ij ji ht it jt rareEmpty one
  by_cases two : c = 2
  · exact G11Residual.no_rare_two least top (fun a ha => (sides a ha).1)
      source count cover ord marked ij ji ht it jt rareEmpty two
  have many : 3 ≤ c := by omega
  exact G11GuardCircuit.no_rare_three (G11GuardFront.numeric_cap G11GuardFront.cap_verified)
    least top (fun a ha => (sides a ha).1) source count cover ord marked ij ji ht it jt rareEmpty many
