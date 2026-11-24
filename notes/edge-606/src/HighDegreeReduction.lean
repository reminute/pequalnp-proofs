import HighCore
import Restriction
import GraphDensity
import Moore

namespace Edge606.HighDegree

open SimpleGraph GirthFiveCore
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open GraphDensity (edgeFunction)

/-- The quantitative edge bound for graphs with nonzero degrees above d. -/
def OnCore (d k : ℕ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ v, G.degree v = 0 ∨ d < G.degree v) → LongCycles G →
    ∀ C : Circuit, Monotone2 C → circuitFun n C = edgeFunction G →
      G.edgeFinset.card ≤ k * (C.size + 1)

def OnAll (k : ℕ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], LongCycles G →
    ∀ C : Circuit, Monotone2 C → circuitFun n C = edgeFunction G →
      G.edgeFinset.card ≤ k * (C.size + 1)

/-- Pin all discarded inputs together, without adding any gate. -/
theorem transfer {d k : ℕ} (coreBound : OnCore d k) : OnAll (k + d) := by
  intro n G inst girth C mono computes
  obtain ⟨S, degrees, cost⟩ := HighCore.positive_degree_core G d
  let H := HighCore.restrict G S
  have safe : LongCycles H := by
    intro v w hw
    have sub : H ≤ G := HighCore.restrict_le G S
    simpa using girth v (w.mapLe sub) (hw.mapLe sub)
  have eval := Restriction.computes_graph G H S C computes (fun _ _ => Iff.rfl)
  have inner := coreBound n H degrees safe (Restriction.restrict S C)
    (Restriction.monotone S C mono) eval
  rw [Restriction.size] at inner
  have support := GraphDensity.support_bound G C (mono_fan mono) computes
  rw [Nat.add_mul]
  exact cost.trans (Nat.add_le_add inner (Nat.mul_le_mul_left d support))

theorem equiv (d : ℕ) : (∃ k, OnAll k) ↔ ∃ k, OnCore d k := by
  constructor
  · rintro ⟨k, h⟩
    exact ⟨k, fun n G _ _ girth C mono comp => h n G girth C mono comp⟩
  · rintro ⟨k, h⟩
    exact ⟨k + d, transfer h⟩

end Edge606.HighDegree

#print axioms Edge606.HighDegree.transfer
#print axioms Edge606.HighDegree.equiv
