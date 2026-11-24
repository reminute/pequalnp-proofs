import G11CertData
import Mathlib.Data.Fintype.Quotient
import PEqualNP.Defs.EdgeOwnership

namespace G11Certificate

def check : Certificate → Finset (Fin 16) → Finset (Fin 16) → Bool
  | .small, _, hi => decide (hi.card < 9)
  | .found k, lo, _ => decide (needed k ⊆ lo)
  | .split e yes no, lo, hi => check yes (insert e lo) hi && check no lo (hi.erase e)

theorem check_sound (t : Certificate) (lo hi S : Finset (Fin 16))
    (lower : lo ⊆ S) (upper : S ⊆ hi) (many : 9 ≤ S.card) (checked : check t lo hi = true) :
    ∃ k : Fin 29, needed k ⊆ S := by
  induction t generalizing lo hi with
  | small =>
    have few : hi.card < 9 := of_decide_eq_true checked
    have bound := Finset.card_le_card upper
    omega
  | found k => exact ⟨k, (of_decide_eq_true checked : needed k ⊆ lo).trans lower⟩
  | split e yes no yesIH noIH =>
    have both := Bool.and_eq_true_iff.mp checked
    by_cases h : e ∈ S
    · exact yesIH _ _ (Finset.insert_subset h lower) upper both.1
    · apply noIH lo (hi.erase e) lower _ both.2
      intro j hj
      exact Finset.mem_erase.mpr ⟨fun (eq : j=e) => h (eq ▸ hj), upper hj⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem certificate_valid : check certificate ∅ Finset.univ = true := by decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem listed_witnesses :
    ∀ k : Fin 29, Function.Injective (witness k) ∧
      ∀ i j : Fin 5, i ≠ j →
        ∃ e : Fin 16, e ∈ needed k ∧ edge e ⊆ negative (witness k i) ∪ negative (witness k j) := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem independent_negatives : ∀ i : Fin 24, ∀ e : Fin 16, ¬edge e ⊆ negative i := by decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem distinct_negatives : Function.Injective negative := by decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem maximal_negatives :
    ∀ i : Fin 24, ∀ v : Fin 11, v ∉ negative i → ∃ e : Fin 16, edge e ⊆ insert v (negative i) := by decide

abbrev graph := PEqualNP.EdgeOwnership.edgeGraph 11
  [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
   (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem graph_edges : ∀ p l : Fin 11, graph.Adj p l ↔ ∃ e : Fin 16, edge e = {p,l} := by decide

theorem graph_independent (i : Fin 24) (p l : Fin 11) (hp : p ∈ negative i) (hl : l ∈ negative i) :
    ¬ graph.Adj p l := by
  intro adj
  obtain ⟨e,he⟩ := (graph_edges p l).mp adj
  apply independent_negatives i e
  rw [he]
  exact Finset.insert_subset hp (Finset.singleton_subset_iff.mpr hl)

theorem nine_edges (S : Finset (Fin 16)) (many : 9 ≤ S.card) :
    ∃ z : Fin 5 → Fin 24, Function.Injective z ∧
      ∀ i j, i ≠ j → ∃ e ∈ S, edge e ⊆ negative (z i) ∪ negative (z j) := by
  obtain ⟨k,inside⟩ := check_sound certificate ∅ Finset.univ S
    (Finset.empty_subset _) (Finset.subset_univ _) many certificate_valid
  obtain ⟨distinct,clique⟩ := listed_witnesses k
  refine ⟨witness k,distinct,?_⟩
  intro i j ne
  obtain ⟨e,inc,contained⟩ := clique i j ne
  exact ⟨e,inside inc,contained⟩

end G11Certificate
