import G11CertData
import ClauseWitness
import Mathlib.Data.Fin.VecNotation

namespace G11FourClauses

open Finset ClauseWitness G11Certificate

def neighbors9 : Finset (Fin 11) := {0,5,7,8}
def neighbors10 : Finset (Fin 11) := {0,2,4,6}

def exampleClauses : Fin 4 → Finset (Fin 11) :=
  ![{9,10}, insert 9 neighbors10, insert 10 neighbors9, neighbors9 ∪ neighbors10]

def hits {V : Type*} (X A : Finset V) : Prop := ∃ v ∈ X, v ∈ A

theorem hits_insert {V : Type*} [DecidableEq V] (X A : Finset V) (c : V) :
    hits X (insert c A) ↔ c ∈ X ∨ hits X A := by
  constructor
  · rintro ⟨v,hv,h⟩
    rcases mem_insert.mp h with rfl | ha
    · exact Or.inl hv
    · exact Or.inr ⟨v,hv,ha⟩
  · rintro (hc | ⟨v,hv,ha⟩)
    · exact ⟨c,hc,mem_insert_self _ _⟩
    · exact ⟨v,hv,mem_insert_of_mem ha⟩

theorem hits_union {V : Type*} [DecidableEq V] (X A B : Finset V) :
    hits X (A ∪ B) ↔ hits X A ∨ hits X B := by
  simp only [hits,mem_union]
  grind

theorem example_sound (X : Finset (Fin 11)) (yes : accepts exampleClauses X) :
    ∃ e : Fin 16, edge e ⊆ X := by
  have h0 : (9 : Fin 11) ∈ X ∨ (10 : Fin 11) ∈ X := by
    obtain ⟨v,hx,hv⟩ := yes 0
    change v ∈ ({9,10} : Finset (Fin 11)) at hv
    simp only [mem_insert,mem_singleton] at hv
    rcases hv with rfl | rfl <;> tauto
  have h1 := (hits_insert X neighbors10 9).mp (yes 1)
  have h2 := (hits_insert X neighbors9 10).mp (yes 2)
  have h3 := (hits_union X neighbors9 neighbors10).mp (yes 3)
  have alternative : ((9 : Fin 11) ∈ X ∧ hits X neighbors9) ∨
      ((10 : Fin 11) ∈ X ∧ hits X neighbors10) := by tauto
  have listed : ∀ c v : Fin 11, ((c = 9 ∧ v ∈ neighbors9) ∨ (c = 10 ∧ v ∈ neighbors10)) →
      ∃ e : Fin 16, edge e = {c,v} := by decide
  have fromStar (c v : Fin 11) (hc : c ∈ X) (hv : v ∈ X)
      (h : (c = 9 ∧ v ∈ neighbors9) ∨ (c = 10 ∧ v ∈ neighbors10)) :
      ∃ e : Fin 16, edge e ⊆ X := by
    obtain ⟨e,eqn⟩ := listed c v h
    exact ⟨e,eqn ▸ insert_subset hc (singleton_subset_iff.mpr hv)⟩
  rcases alternative with ⟨hc,v,hv,adj⟩ | ⟨hc,v,hv,adj⟩
  · exact fromStar 9 v hc hv (Or.inl ⟨rfl,adj⟩)
  · exact fromStar 10 v hc hv (Or.inr ⟨rfl,adj⟩)

def eightEdges : Finset (Fin 16) := {0,1,5,9,11,13,14,15}

theorem tight_example : eightEdges.card = 8 ∧ ∀ e ∈ eightEdges, accepts exampleClauses (edge e) := by
  unfold accepts
  decide

end G11FourClauses
