import HighDegreeReduction

namespace Edge606.HighDegree

open SimpleGraph GirthFiveCore
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open GraphDensity (edgeFunction)

/-- A violation of coefficient r+d has a spanning induced restriction that
    still violates r, and where every nonisolated vertex has degree above d. -/
theorem restrict_excess {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (girth : LongCycles G) (C : Circuit) (mono : Monotone2 C)
    (computes : circuitFun n C = edgeFunction G) (d r : ℕ)
    (bad : (r + d) * (C.size + 1) < G.edgeFinset.card) :
    ∃ S : Finset (Fin n),
      let H := HighCore.restrict G S
      let D := Restriction.restrict S C
      LongCycles H ∧ (∀ v, H.degree v = 0 ∨ d < H.degree v) ∧
        Monotone2 D ∧ D.size = C.size ∧ circuitFun n D = edgeFunction H ∧
        r * (D.size + 1) < H.edgeFinset.card ∧ 4 * r ^ 2 < D.size := by
  obtain ⟨S, degrees, cost⟩ := HighCore.positive_degree_core G d
  let H := HighCore.restrict G S
  let D := Restriction.restrict S C
  have safe : LongCycles H := by
    intro v w hw
    have sub : H ≤ G := HighCore.restrict_le G S
    simpa using girth v (w.mapLe sub) (hw.mapLe sub)
  have dm : Monotone2 D := Restriction.monotone S C mono
  have size : D.size = C.size := Restriction.size S C
  have comp : circuitFun n D = edgeFunction H :=
    Restriction.computes_graph G H S C computes (fun _ _ => Iff.rfl)
  have count := Nat.mul_le_mul_left d (GraphDensity.support_bound G C (mono_fan mono) computes)
  have coreBad : r * (D.size + 1) < H.edgeFinset.card := by
    rw [size]
    change _ ≤ H.edgeFinset.card + _ at cost
    rw [Nat.add_mul] at bad
    omega
  exact ⟨S, safe, degrees, dm, size, comp, coreBad, Moore.size_of_excess H safe D dm comp r coreBad⟩

end Edge606.HighDegree

#print axioms Edge606.HighDegree.restrict_excess
