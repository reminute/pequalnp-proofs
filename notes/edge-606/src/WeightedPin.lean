import L_meta_1708

namespace Edge606.WeightedPin

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Each gate that reads the raw input contributes once, even if it reads it twice. -/
abbrev readers {n : Nat} (C : Circuit) (v : Fin n) : Nat :=
  (Finset.univ.filter fun j : Fin C.gates.length => v.val ∈ (C.gates.get j).inputs).card

theorem readers_eq_length {n : Nat} (C : Circuit) (v : Fin n) :
    readers C v = (C.gates.filter fun g => v.val ∈ g.inputs).length := by
  let reads (g : Gate) := decide (v.val ∈ g.inputs)
  calc
    readers C v = (List.finRange C.gates.length).countP (reads ∘ C.gates.get) := by
      unfold readers
      rw [← List.toFinset_finRange, List.Nodup.card_eq_countP (List.nodup_finRange _)]
      rfl
    _ = ((List.finRange C.gates.length).map C.gates.get).countP reads := List.countP_map.symm
    _ = _ := by rw [List.map_get_finRange, List.countP_eq_length_filter]

/-- Specializing a vertex to false deletes all its incident edges and saves at
    least one gate per direct reader. This retains the quantitative estimate of
    the upstream L-meta-1708 constant-propagation proof, including for isolated vertices. -/
theorem peel {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) (C : Circuit) (mono : Monotone2 C)
    (computes : circuitFun n C = fun x : Fin n → Bool =>
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + readers C v ≤ C.size ∧
      circuitFun n D = fun x : Fin n → Bool =>
        decide (∃ a b, (G.deleteIncidenceSet v).Adj a b ∧ x a = true ∧ x b = true) := by
  classical
  have eval (x : Fin n → Bool) : C.eval (List.ofFn x) =
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) := congrFun computes x
  obtain ⟨D, dmono, saving, pin⟩ :=
    PEqualNP.Outside.L_meta_1708_aux.pinCircuit n C v false mono (by
      refine ⟨fun _ => false, ?_⟩
      rw [eval]
      simp)
  refine ⟨D, dmono, saving, ?_⟩
  funext x
  change D.eval (List.ofFn x) = _
  rw [pin, eval]
  congr 1
  apply propext
  constructor
  · rintro ⟨a, b, adj, ha, hb⟩
    have av : a ≠ v := by rintro rfl; simp at ha
    have bv : b ≠ v := by rintro rfl; simp at hb
    exact ⟨a, b, SimpleGraph.deleteIncidenceSet_adj.mpr ⟨adj, av, bv⟩,
      by simpa [Function.update_of_ne av] using ha,
      by simpa [Function.update_of_ne bv] using hb⟩
  · rintro ⟨a, b, adj, ha, hb⟩
    obtain ⟨edge, av, bv⟩ := SimpleGraph.deleteIncidenceSet_adj.mp adj
    exact ⟨a, b, edge, by simpa [Function.update_of_ne av] using ha,
      by simpa [Function.update_of_ne bv] using hb⟩

end Edge606.WeightedPin
