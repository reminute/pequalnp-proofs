import NoClean

namespace GirthAnchor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

def withoutClean {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    Finset (Sym2 (Fin n)) :=
  G.edgeFinset.filter fun e => ¬ ∃ u v : Fin n, e=s(u,v) ∧ ∃ j : Fin C.gates.length,
    Owns n C j u v ∧ ∀ p q : Fin n, gateVal n C j (pairInput p q)=true → G.Adj p q

def dense {n : Nat} (D : Nat) (S : Finset (Sym2 (Fin n))) : Prop :=
  ∀ v : Fin n, (S.filter (v ∈ ·)).card=0 ∨ D<(S.filter (v ∈ ·)).card

def OwnedBound (D K : Nat) : Prop :=
  ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ v, G.degree v=0 ∨ 3≤G.degree v) →
    (∀ v : Fin n, ∀ w : G.Walk v v, w.IsCycle → 5≤w.length) →
    ∀ C : Circuit, Monotone2 C → circuitFun n C=graphFun G ∅ →
    ∀ S ⊆ withoutClean G C, dense D S → S.card≤K*(C.size+1)

def PlainBound (D K : Nat) : Prop :=
  ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ v, G.degree v=0 ∨ 3≤G.degree v) →
    (∀ v : Fin n, ∀ w : G.Walk v v, w.IsCycle → 5≤w.length) →
    ∀ C : Circuit, Monotone2 C → circuitFun n C=graphFun G ∅ →
    ∀ S ⊆ G.edgeFinset, dense D S → S.card≤K*(C.size+1)

theorem all_edges {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    withoutClean G (anchored n C)=G.edgeFinset := by
  ext e
  constructor
  · exact fun h => (Finset.mem_filter.mp h).1
  · intro edge
    apply Finset.mem_filter.mpr
    refine ⟨edge,?_⟩
    rintro ⟨u,v,_,j,own,good⟩
    exact no_clean G own good

theorem plain_of_owned {D K : Nat} (h : OwnedBound D K) : PlainBound D (2*K) := by
  intro n G inst d g C mc eq S sub high
  have eq' : circuitFun n (anchored n C)=graphFun G ∅ := (funext (same_eval n C)).trans eq
  have admissible : S⊆withoutClean G (anchored n C) := by simpa [all_edges] using sub
  have size := h n G d g (anchored n C) (mono n mc) eq' S admissible high
  rw [exact_size] at size
  calc
    S.card ≤ K*(2*C.size+1+1) := size
    _ = (2*K)*(C.size+1) := by ring

theorem owned_of_plain {D K : Nat} (h : PlainBound D K) : OwnedBound D K := by
  intro n G inst d g C mc eq S sub high
  exact h n G d g C mc eq S (fun e he => (Finset.mem_filter.mp (sub he)).1) high

theorem exists_iff : (∃ D K, OwnedBound D K) ↔ ∃ D K, PlainBound D K := by
  constructor
  · rintro ⟨D,K,h⟩
    exact ⟨D,2*K,plain_of_owned h⟩
  · rintro ⟨D,K,h⟩
    exact ⟨D,K,owned_of_plain h⟩

end GirthAnchor
