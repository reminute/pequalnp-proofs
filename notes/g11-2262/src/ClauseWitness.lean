import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Card

namespace ClauseWitness

def accepts {V : Type*} {k : ℕ} (clauses : Fin k → Finset V) (input : Finset V) : Prop :=
  ∀ j, ∃ v ∈ input, v ∈ clauses j

theorem accepts_mono {V : Type*} {k : ℕ} {clauses : Fin k → Finset V} {x y : Finset V}
    (sub : x ⊆ y) (yes : accepts clauses x) : accepts clauses y := by
  intro j
  obtain ⟨v,hx,hc⟩ := yes j
  exact ⟨v,sub hx,hc⟩

theorem incompatibleNegatives {V : Type*} [DecidableEq V] {k : ℕ}
    (clauses : Fin k → Finset V) (negative : Fin (k+1) → Finset V)
    (off : ∀ i, ¬ accepts clauses (negative i))
    (on : ∀ i j, i ≠ j → accepts clauses (negative i ∪ negative j)) : False := by
  classical
  have missing (i : Fin (k+1)) : ∃ c, ¬ ∃ v ∈ negative i, v ∈ clauses c := by
    by_contra! all
    exact off i all
  choose color absent using missing
  have inj : Function.Injective color := by
    intro i j same
    by_contra diff
    obtain ⟨v, either, hit⟩ := on i j diff (color i)
    rcases Finset.mem_union.mp either with hi | hj
    · exact absent i ⟨v,hi,hit⟩
    · exact absent j ⟨v,hj,same ▸ hit⟩
  have h := Fintype.card_le_of_injective color inj
  simp at h
  exact (Nat.not_succ_le_self k) h

theorem certifiedEdgeObstruction {V : Type*} [DecidableEq V] {k : ℕ}
    (clauses : Fin k → Finset V) (negative : Fin (k+1) → Finset V)
    (edges : Finset (V × V)) (off : ∀ i, ¬ accepts clauses (negative i))
    (accepted : ∀ e ∈ edges, accepts clauses {e.1,e.2})
    (witness : ∀ i j, i ≠ j → ∃ e ∈ edges,
      e.1 ∈ negative i ∪ negative j ∧ e.2 ∈ negative i ∪ negative j) : False := by
  apply incompatibleNegatives clauses negative off
  intro i j diff
  obtain ⟨e,he,h1,h2⟩ := witness i j diff
  apply accepts_mono (x := {e.1,e.2}) _ (accepted e he)
  intro v hv
  rcases Finset.mem_insert.mp hv with rfl | hv
  · exact h1
  · exact Finset.mem_singleton.mp hv ▸ h2

end ClauseWitness
