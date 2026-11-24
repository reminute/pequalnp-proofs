import PinnedSupport

/- The originating project development is PEqualNP/MetaComplexity/Helpers/Support.lean.
   We use its joint-support invariant and its agreement theorem for the actual wire fold. -/
namespace Edge606.Support

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

abbrev Input (n : ℕ) := Fin n → Bool

/-- A coordinate is essential exactly when flipping it can change the answer. -/
def Essential {n : ℕ} (f : Input n → Bool) (i : Fin n) : Prop :=
  ∃ x, f (Function.update x i (!x i)) ≠ f x

noncomputable def essentialInputs {n : ℕ} (f : Input n → Bool) : Finset (Fin n) := by
  classical exact Finset.univ.filter (Essential f)

/-- Raw, computed, and invalid output indices all use the project's default false. -/
def wire {n : ℕ} (C : Circuit) (j : ℕ) (x : Input n) : Bool :=
  (C.wires (List.ofFn x)).getD j false

theorem contained {n : ℕ} (C : Circuit) (j : ℕ) :
    essentialInputs (wire (n:=n) C j) ⊆ (suppsFrom C.gates (inputSupps n)).getD j ∅ := by
  classical
  intro i hi
  obtain ⟨x,change⟩ := (Finset.mem_filter.mp hi).2
  by_contra missing
  apply change
  apply (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
    (agree_inputs _ _)).2.2 j
  intro t ht
  have ne : t ≠ i := fun eq => missing (eq ▸ ht)
  simp [Function.update_of_ne ne]

/-- Only *distinct* operands contribute. Constants, copies, and repeated operands
    have zero excess; a gate with d ≥ 1 distinct operands contributes d−1. -/
def excess (g : Gate) := g.inputs.toFinset.card - 1

private theorem add_gate {n t : ℕ} (L : List (Finset (Fin n))) (g : Gate)
    (bound : Cnt t L) : Cnt (t + excess g) (L ++ [gateSupp L g]) := by
  intro W
  by_cases use : L.length ∈ W
  · let prior := W.erase L.length ∪ g.inputs.toFinset
    have sub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅) ⊆
        prior.biUnion (fun j => L.getD j ∅) := by
      intro i hi
      obtain ⟨j,hj,h⟩ := Finset.mem_biUnion.mp hi
      apply Finset.mem_biUnion.mpr
      by_cases new : j=L.length
      · subst j
        rw [getD_snoc_eq] at h
        obtain ⟨a,member,dep⟩ := (mem_gateSupp L g i).mp h
        exact ⟨a,Finset.mem_union_right _ (List.mem_toFinset.mpr member),dep⟩
      · rw [getD_snoc_ne _ _ _ _ new] at h
        exact ⟨j,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨new,hj⟩),h⟩
    have card : prior.card ≤ W.card - 1 + g.inputs.toFinset.card := by
      simpa only [prior,Finset.card_erase_of_mem use] using
        (Finset.card_union_le (W.erase L.length) g.inputs.toFinset)
    have left := (Finset.card_le_card sub).trans (bound prior)
    have nonempty := Finset.card_pos.mpr ⟨_,use⟩
    unfold excess
    omega
  · have same : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅) =
        (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => use (e ▸ hj))
    rw [same]
    have old := bound W
    omega

private theorem all_gates {n : ℕ} (gs : List Gate) (t : ℕ) (L : List (Finset (Fin n)))
    (bound : Cnt t L) : Cnt (t + (gs.map excess).sum) (suppsFrom gs L) := by
  induction gs generalizing t L with
  | nil => simpa [suppsFrom] using bound
  | cons g gs ih =>
    simpa only [suppsFrom,List.foldl_cons,List.map_cons,List.sum_cons,Nat.add_assoc] using
      ih (t+excess g) (L++[gateSupp L g]) (add_gate L g bound)

/-- Joint bound for any collection of outputs, including ignored and invalid wires. -/
theorem joint {n : ℕ} (C : Circuit) (W : Finset ℕ) :
    (W.biUnion (fun j => essentialInputs (wire (n:=n) C j))).card ≤
      (C.gates.map excess).sum + W.card := by
  have sub : (W.biUnion (fun j => essentialInputs (wire (n:=n) C j))) ⊆
      W.biUnion (fun j => (suppsFrom C.gates (inputSupps n)).getD j ∅) := by
    intro i hi
    obtain ⟨j,mem,dep⟩ := Finset.mem_biUnion.mp hi
    exact Finset.mem_biUnion.mpr ⟨j,mem,contained C j dep⟩
  exact (Finset.card_le_card sub).trans (by
    simpa only [Nat.zero_add] using all_gates C.gates 0 (inputSupps n) cnt_inputs W)

theorem weighted {n : ℕ} (C : Circuit) :
    (essentialInputs (circuitFun n C)).card ≤ (C.gates.map excess).sum + 1 := by
  have same : circuitFun n C = wire (n:=n) C C.output := by funext x; rfl
  rw [same]
  simpa only [Finset.singleton_biUnion,Finset.card_singleton] using
    joint (n:=n) C {C.output}

private theorem two_cost (gs : List Gate) (two : ∀ g∈gs, g.inputs.length ≤ 2) :
    (gs.map excess).sum ≤ gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have head := (List.toFinset_card_le g.inputs).trans (two g (by simp))
    have tail := ih fun q h => two q (List.mem_cons_of_mem _ h)
    simp only [List.map_cons,List.sum_cons,List.length_cons,excess]
    omega

theorem essential_bound {n : ℕ} (C : Circuit) (two : ∀ g∈C.gates, g.inputs.length ≤ 2) :
    (essentialInputs (circuitFun n C)).card ≤ C.size+1 :=
  (weighted C).trans (Nat.add_le_add_right (two_cost C.gates two) 1)

theorem monotone_bound {n : ℕ} (C : Circuit) (mono : Monotone2 C) :
    (essentialInputs (circuitFun n C)).card ≤ C.size+1 :=
  essential_bound C (fun g hg => (mono g hg).2)

end Edge606.Support

#print axioms Edge606.Support.joint
#print axioms Edge606.Support.essential_bound
#print axioms Edge606.Support.monotone_bound
