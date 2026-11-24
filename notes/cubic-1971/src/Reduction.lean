import Mathlib.Combinatorics.SimpleGraph.Girth
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_1971_825
    (width : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))
      (C : Circuit) (v : Fin n) (pre post : List Gate) (g : Gate) (k : ℕ),
      (∀ u w, G.Adj u w → u ∉ A) → (∀ u (p : G.Walk u u), p.IsCycle → 5 ≤ p.length) →
      (G.neighborSet v).ncard = 3 → v ∉ A → FanInTwo C → circuitFun n C = graphFun G A →
      (∀ s, HasCircuitSize n (circuitFun n C) s → C.size ≤ s) →
      (C.gates.filter fun t => (t.inputs.take (bif t.op.eval [false] then 1 else 2)).contains v.val).length ≤ 1 →
      C.gates = pre ++ g :: post → g.op = .and → (g.inputs = [v.val,k] ∨ g.inputs = [k,v.val]) →
      (∀ t ∈ post, t.op ≠ .not) → k ≠ v.val → C.output ≠ v.val →
      ∀ K : Finset (Fin n), K.card ≤ 2 → v ∉ K →
      ∃ x y, (∀ u ∈ K, x u = y u) ∧ circuitFun n (⟨pre,k⟩ : Circuit) x ≠ circuitFun n ⟨pre,k⟩ y)
    (residual : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      let f := graphFun G A
      let readers := fun v : Fin n => C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) → 7 ≤ G.egirth →
      (∀ u v, G.Adj u v → u ∉ A) →
      IsMinimalCircuit n C → circuitFun n C = f →
      (∀ v ∉ A, (readers v).length ≤ 3 ∧ ((readers v).length = 3 → ∀ g ∈ readers v, g.op = .or)) →
      (∃ v ∉ A, (readers v).length ≤ 1 ∧ ∀ (pre post : List Gate) (g : Gate) (k : ℕ),
        C.gates = pre ++ g :: post → g.op = .and → (g.inputs = [v.val,k] ∨ g.inputs = [k,v.val]) →
        (∀ t ∈ post, t.op ≠ .not) →
        let signal := circuitFun n (⟨pre,k⟩ : Circuit)
        k ≠ v.val → C.output ≠ v.val → ∀ K : Finset (Fin n), K.card ≤ 2 → v ∉ K →
          ∃ x y, (∀ u ∈ K, x u = y u) ∧ signal x ≠ signal y) →
      ∃ v ∉ A, ∃ s, s+4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) s) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       x16.length ≤ (3 : ℕ) ∧ (x16.length = (3 : ℕ) → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                     (∃ x15 ∉ x3, (List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x15) x5.gates).length ≤ (1 : ℕ)) → ∃ x16 ∉ x3, ∃ (x17 : ℕ), x17 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x18 : Fin x1 → Bool) => x4 (Function.update x18 x16 Bool.false)) x17 := by
  classical
  intro n G A f C degree girth unmarked edge description fan computes least bounds few
  have graph : graphFun G A = f := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change (decide (∃ a ∈ A, x a = true) ||
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = true ↔ f x = true
    rw [description x]
    simp only [Bool.or_eq_true,decide_eq_true_eq]
  have mini : IsMinimalCircuit n C := by
    refine ⟨fan,?_⟩
    intro D ok eqv
    exact least D.size ⟨D,ok,le_rfl,fun x => congrFun (eqv.trans computes) x⟩
  have wide : 7 ≤ G.egirth := by
    apply SimpleGraph.le_egirth.mpr
    intro v p hc
    exact_mod_cast girth v p hc
  obtain ⟨v,hv,one⟩ := few
  have minimal : ∀ s, HasCircuitSize n (circuitFun n C) s → C.size ≤ s := fun s h => least s (computes ▸ h)
  have solved := residual n G A C degree wide unmarked mini (computes.trans graph.symm) bounds
    ⟨v,hv,one,fun pre post g k layout op ins after =>
        width n G A C v pre post g k unmarked (fun u p hc => le_trans (by decide : 5 ≤ 7) (girth u p hc))
          (degree v hv) hv fan (computes.trans graph.symm) minimal one layout op ins after⟩
  rwa [graph] at solved
