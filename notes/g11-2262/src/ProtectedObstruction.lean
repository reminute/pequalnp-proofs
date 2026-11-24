import ProtectedCovers

namespace G11Protected

open G11Certificate

def neighbors (U : Finset (Fin 16)) (c : Fin 11) : Finset (Fin 11) :=
  Finset.univ.filter fun v => ∃ e : Fin 16, e ∉ U ∧
    ((edgeAt e).1 = c ∧ (edgeAt e).2 = v ∨ (edgeAt e).1 = v ∧ (edgeAt e).2 = c)

def allowed (U : Finset (Fin 16)) (A : Finset (Fin 11)) : Prop :=
  (∃ c : Fin 11, A ⊆ {c}) ∨ (∃ c : Fin 11, A ⊆ neighbors U c)

def obstructs (U : Finset (Fin 16)) (z : Fin 24) (B : Finset (Fin 11)) : Prop :=
  ∃ e : Fin 16, e ∈ U ∧ Disjoint (edge e) (B \ negative z)

def rowWorks (U : Finset (Fin 16)) (z : Fin 24) : Prop :=
  (∀ c : Fin 11, obstructs U z {c}) ∧ (∀ c : Fin 11, obstructs U z (neighbors U c))

instance (U : Finset (Fin 16)) (z : Fin 24) (B : Finset (Fin 11)) : Decidable (obstructs U z B) := by
  unfold obstructs; infer_instance

instance (U : Finset (Fin 16)) (z : Fin 24) : Decidable (rowWorks U z) := by
  unfold rowWorks; infer_instance

def check : Tree → Finset (Fin 16) → Finset (Fin 16) → Bool
  | .cover k, _, hi => decide (hi ⊆ upperSet k)
  | .row z, lo, _ => decide (rowWorks lo z)
  | .step e yes no, lo, hi => check yes (insert e lo) hi && check no lo (hi.erase e)

theorem neighbors_anti {S T : Finset (Fin 16)} (sub : S ⊆ T) (c : Fin 11) :
    neighbors T c ⊆ neighbors S c := by
  intro v h
  obtain ⟨e,off,adj⟩ := (Finset.mem_filter.mp h).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,e,fun h => off (sub h),adj⟩

theorem check_sound (t : Tree) (lo hi U : Finset (Fin 16)) (K : Finset (Fin 11))
    (lower : lo ⊆ U) (upper : U ⊆ hi) (cover : covers U K) (budget : K.card ≤ U.card+2)
    (verified : check t lo hi = true) :
    ∃ z : Fin 24, ∀ A : Finset (Fin 11), allowed U A →
      (∀ e ∈ U, ¬ Disjoint (edge e) A) → ¬ Disjoint A (negative z) := by
  induction t generalizing lo hi with
  | cover k =>
    have high : hi ⊆ upperSet k := of_decide_eq_true verified
    have kh := upper_bound k K (fun e => (cover e).imp (fun h => high (upper h)) id)
    have sz := Finset.card_le_card (upper.trans high)
    omega
  | row z =>
    have works : rowWorks lo z := of_decide_eq_true verified
    refine ⟨z,?_⟩
    intro A shape hits off
    have block (B : Finset (Fin 11)) (bad : obstructs lo z B) (ab : A ⊆ B) : False := by
      obtain ⟨e,he,disj⟩ := bad
      apply hits e (lower he)
      apply disj.mono_right
      intro v hv
      exact Finset.mem_sdiff.mpr ⟨ab hv,Finset.disjoint_left.mp off hv⟩
    rcases shape with ⟨c,hc⟩ | ⟨c,hc⟩
    · exact block {c} (works.1 c) hc
    · exact block (neighbors lo c) (works.2 c) (hc.trans (neighbors_anti lower c))
  | step e yes no yesIH noIH =>
    have both := Bool.and_eq_true_iff.mp verified
    by_cases mem : e ∈ U
    · exact yesIH _ _ (Finset.insert_subset mem lower) upper both.1
    · apply noIH lo (hi.erase e) lower _ both.2
      intro j hj
      exact Finset.mem_erase.mpr ⟨fun (eq : j=e) => mem (eq ▸ hj),upper hj⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 5000000 in
theorem certificate_valid : check certificate ∅ Finset.univ = true := by decide

theorem blocking_negative (U : Finset (Fin 16)) (K : Finset (Fin 11)) (cover : covers U K)
    (budget : K.card ≤ U.card+2) :
    ∃ z : Fin 24, ∀ A : Finset (Fin 11), allowed U A →
      (∀ e ∈ U, ¬ Disjoint (edge e) A) → ¬ Disjoint A (negative z) :=
  check_sound certificate ∅ Finset.univ U K (Finset.empty_subset _) (Finset.subset_univ _)
    cover budget certificate_valid

end G11Protected
