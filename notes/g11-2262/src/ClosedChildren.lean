import PostedNoRareAll
import PostedSmall
import Structure
import Mathlib.Data.Nat.BitIndices

open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

set_option linter.unusedVariables false
set_option maxHeartbeats 3500000

theorem G11Reduction.solved_small_or_zero :
let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x1 : ℕ) => (x1 / (7 : ℕ), x1 % (7 : ℕ) + (4 : ℕ))) (Nat.bitIndices (2324175737840503008 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 x5 : ℕ),   have x6 : Finset ℕ := PEqualNP.TopForm.tops x1 x2;   have x7 : Finset ℕ := PEqualNP.TopForm.centreless x1 x2;   have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;   have x9 : ℕ := (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;   have x10 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2;   have x11 : ℕ → Fin (2 : ℕ) → ℕ → Prop := fun (x11 : ℕ) (x12 : Fin (2 : ℕ)) => PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x2 (PEqualNP.TopForm.opnd x2 x11 x12);   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       PEqualNP.TopForm.junk x1 x2 = {x3, x4} →         x3 < x4 →           ¬x10 x3 x4 →             ¬x10 x4 x3 →               x5 ∈ x6 →                 x10 x3 x5 →                   x10 x4 x5 →                     x9 = (0 : ℕ) ∨ x8.card ≤ (2 : ℕ) →                       (17 : ℕ) + (x6 \ x7).card + (2 : ℕ) * x7.card + x9 ≤ x2.size + x8.card →                         (∀ (x23 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x8) x23 → x23.card ≤ (x6 \ x7).card) →                           (∀ x24 ∈ x6,                               have x26 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x2 x24;                               (∀ x27 ∈ x26 (0 : Fin (2 : ℕ)), ∀ x29 ∈ x26 (1 : Fin (2 : ℕ)), x1.Adj x27 x29) ∧ ((x26 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x26 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →                             (∀ x25 ∈ x8, ∃ x27 ∈ x6, ∃ (x28 : Fin (2 : ℕ)) (x29 : ℕ), (x29 = x3 ∨ x29 = x4) ∧ x11 x27 x28 x29 ∧ x25 ∈ PEqualNP.TopForm.gammaE x1 x2 x27 ∩ PEqualNP.TopForm.gammaE x1 x2 x29) → (22 : ℕ) ≤ x2.size := by
  intro graphArg C i j t
  dsimp only
  intro least top marked ord ij ji ht it jt small count cover sides raw
  let G := G11Certificate.graph
  have val_of_gamma {e : Nat} {u v : Fin 11} (h : s(u,v) ∈ gammaE G C e) :
      gateVal 11 C e (pairInput u v) = true := by
    obtain ⟨a,b,hpair,truth⟩ := (Finset.mem_filter.mp h).2
    rcases Sym2.eq_iff.mp hpair with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact truth
    · have flip : pairInput v u = pairInput u v := by
        funext w
        change decide (w = v ∨ w = u) = decide (w = u ∨ w = v)
        exact decide_eq_decide.mpr or_comm
      simpa only [flip] using truth
  have source : ∀ u v : Fin 11, s(u,v) ∈ Ustar G C → ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ k : Nat,
      (k=i ∨ k=j) ∧ gateVal 11 C a (pairInput u v) = true ∧ OrReaches 11 C (opnd C a b) k ∧
      gateVal 11 C k (pairInput u v) = true := by
    intro u v he
    obtain ⟨a,ha,b,k,hk,hr,hboth⟩ := raw s(u,v) he
    obtain ⟨pa,pk⟩ := Finset.mem_inter.mp hboth
    exact ⟨a,ha,b,k,hk,val_of_gamma pa,hr,val_of_gamma pk⟩
  have common : ∃ a ∈ tops G C, InCone 11 C i a ∧ InCone 11 C j a := ⟨t,ht,it,jt⟩
  rcases small with zero | few
  · exact G11Residual.posted_no_rare_all G C i j rfl least top sides source count cover ord marked ij ji common zero
  · exact G11SmallUncovered.posted_with_small_U G C i j rfl least top sides source count cover ord marked ij ji common few

theorem G11Reduction.solved_path :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 x7 : ℕ), PEqualNP.TopForm.IsAO2 x1 x4 → PEqualNP.TopForm.TopForm x2 x4 → PEqualNP.TopForm.junk x2 x4 = {x5, x6} → ¬PEqualNP.EdgeOwnership.InCone x1 x4 x5 x6 → x7 ∈ PEqualNP.TopForm.tops x2 x4 → PEqualNP.EdgeOwnership.InCone x1 x4 x5 x7 → ∃ (x14 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x7 x14) x5 := by
  intro n G inst C i j t ao tf marked incomparable top inside
  exact G11Structure.reaches_one_side ao tf marked incomparable top inside

#print axioms G11Reduction.solved_small_or_zero
#print axioms G11Reduction.solved_path
