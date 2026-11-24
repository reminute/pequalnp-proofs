import TwoRoundCovers
import TwoRoundHints

namespace G11TwoRounds

open G11Protected G11Certificate

def check : Tree → Finset (Fin 16) → Finset (Fin 16) → Bool
  | .cap k, _, hi => decide (hi ⊆ bound k)
  | .forced k, lo, _ => decide ((hint k).edges ⊆ lo)
  | .step e yes no, lo, hi => check yes (insert e lo) hi && check no lo (hi.erase e)

theorem check_sound (t : Tree) (lo hi U : Finset (Fin 16)) (K : Finset (Fin 11))
    (lower : lo ⊆ U) (upper : U ⊆ hi) (cover : covers U K) (budget : K.card ≤ U.card)
    (verified : check t lo hi = true) :
    ∃ Y : Finset (Fin 24), ∃ z ∈ Y,
      (∀ y ∈ Y, ∀ A : Finset (Fin 11), allowed U A → Hits U A → ¬ Disjoint A (negative y)) ∧
        (∀ B : Finset (Fin 11), allowed U B → Hits (captured U Y) B → ¬ Disjoint B (negative z)) := by
  induction t generalizing lo hi with
  | cap k =>
    have high : hi ⊆ bound k := of_decide_eq_true verified
    have big := cap_bound k K (fun e => (cover e).imp (fun h => high (upper h)) id)
    have sz := Finset.card_le_card (upper.trans high)
    omega
  | forced k =>
    have inside : (hint k).edges ⊆ U := (of_decide_eq_true verified : (hint k).edges ⊆ lo).trans lower
    obtain ⟨mem,first,second⟩ := hints_valid k
    exact ⟨(hint k).rows,(hint k).z,mem,fun y hy => forced_hit inside inside (first y hy),
      forced_hit inside (captured_mono inside _) second⟩
  | step e yes no yesIH noIH =>
    have both := Bool.and_eq_true_iff.mp verified
    by_cases mem : e ∈ U
    · exact yesIH _ _ (Finset.insert_subset mem lower) upper both.1
    · apply noIH lo (hi.erase e) lower _ both.2
      intro j hj
      exact Finset.mem_erase.mpr ⟨fun (eq : j=e) => mem (eq ▸ hj),upper hj⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000 in
theorem certificate_valid : check certificate ∅ Finset.univ = true := by decide

theorem two_rounds (U : Finset (Fin 16)) (K : Finset (Fin 11))
    (cover : covers U K) (budget : K.card ≤ U.card) :
    ∃ Y : Finset (Fin 24), ∃ z ∈ Y,
      (∀ y ∈ Y, ∀ A : Finset (Fin 11), allowed U A → Hits U A → ¬ Disjoint A (negative y)) ∧
        (∀ B : Finset (Fin 11), allowed U B → Hits (captured U Y) B → ¬ Disjoint B (negative z)) :=
  check_sound certificate ∅ Finset.univ U K (Finset.empty_subset _) (Finset.subset_univ _) cover
    budget certificate_valid

end G11TwoRounds
