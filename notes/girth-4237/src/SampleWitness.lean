import NativeWitness

namespace GirthRepresent

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership GirthFiveCore GirthEdgeBound GirthEdgeNegatives GirthExceptions

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
variable {S : Finset (Sym2 (Fin n))}

/-- Either a clique of at most two vertices, or its external neighborhood. -/
def tested (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) : Prop :=
  ∃ U : Finset (Fin n), U.card ≤ 2 ∧ G.IsClique (U : Set (Fin n)) ∧
    (x = (fun v => decide (v ∈ U)) ∨ x = (fun v => decide (v ∉ U ∧ ∃ w ∈ U, G.Adj v w)))

theorem positive_tested (sub : S ⊆ G.edgeFinset) (e : ↥(edgeRows S)) :
    tested G (GirthRank.positive (edgeRows S) e) :=
  ⟨e.val, (row_two sub e.val e.property).le,
    fun _ hu _ hv diff => row_adj sub e.val e.property _ hu _ hv diff, Or.inl rfl⟩

theorem negative_tested (sub : S ⊆ G.edgeFinset) (y : Fin n ⊕ ↥(edgeRows S)) :
    tested G (GirthRank.negative (edgeRows S) G.Adj y) := by
  cases y with
  | inl v =>
    refine ⟨{v},by simp,by simp,Or.inr ?_⟩
    funext w
    apply Bool.eq_iff_iff.mpr
    simp only [GirthRank.negative,decide_eq_true_eq]
    rfl
  | inr e =>
    refine ⟨e.val, (row_two sub e.val e.property).le,
      fun _ hu _ hv diff => row_adj sub e.val e.property _ hu _ hv diff, Or.inr ?_⟩
    funext w
    apply Bool.eq_iff_iff.mpr
    simp only [GirthRank.negative,decide_eq_true_eq]
    rfl

def testedWitness (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (m : ℕ) : Prop :=
  ∃ Q : Finset (Fin C.gates.length), Q.card = m ∧
    (∀ j ∈ Q, 1 < (readers n C j).card) ∧
    ∀ t ∈ Q, ∀ i ∈ Q, t < i → ∃ x, tested G x ∧
      gateVal n C i.val x = circuitFun n C x ∧ gateVal n C t.val x ≠ circuitFun n C x

theorem tested_of_large (sub : S ⊆ G.edgeFinset) (girth : GirthFive G)
    (mono : Monotone2 C) (computes : circuitFun n C = graphFun G ∅) (k : ℕ)
    (large : (2^(k+1)-1)*(C.size+1) < S.card) : testedWitness G C (k+1) := by
  classical
  let H := liveHigh S G C 1
  let pos := GirthRank.positive (edgeRows S)
  let neg := GirthRank.negative (edgeRows S) G.Adj
  let R (t i : Fin C.gates.length) := Covers pos neg (gateVal n C t.val) (gateVal n C i.val)
  have reflex (a) (_ : a ∈ H) : R a a := ⟨fun _ h => h, fun _ h => h⟩
  have transitive {a b c} (ab : R a b) (bc : R b c) : R a c :=
    ⟨fun i h => ab.1 i (bc.1 i h), fun j h => ab.2 j (bc.2 j h)⟩
  have noCover (T : Finset (Fin C.gates.length)) (inside : T ⊆ H) (few : T.card ≤ k)
      (rep : ∀ x ∈ H, ∃ t ∈ T, t ≤ x ∧ R t x) : False := by
    apply large.not_ge
    simpa using (live_covered sub girth mono computes (B := 1) (by decide) T few
      (fun i hi => reaches_of_live_reads (Nat.zero_lt_one.trans (Finset.mem_filter.mp (inside hi)).2.1)) rep)
  obtain ⟨Q,subset,card,sep⟩ := GirthOrdered.packing H R k reflex transitive noCover
  refine ⟨Q,card,fun j hj => two_readers (Finset.mem_filter.mp (subset hj)).2.1,?_⟩
  intro t ht i hi lt
  by_contra! all
  apply sep t ht i hi lt
  constructor
  · intro e on
    have out : circuitFun n C (pos e) = true := computes ▸ positive_on sub e
    exact (all _ (positive_tested sub e) (on.trans out.symm)).trans out
  · intro y off
    have out : circuitFun n C (neg y) = false := computes ▸ negative_off sub girth y
    have z : gateVal n C i.val (neg y) = false := by simpa using off
    have good := (all _ (negative_tested sub y) (z.trans out.symm)).trans out
    simpa using good

theorem tested_easy (k n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (girth : GirthFive G) (C : Circuit) (mono : Monotone2 C)
    (computes : circuitFun n C = graphFun G ∅) (noWitness : ¬testedWitness G C (k+1)) :
    G.edgeFinset.card ≤ (2^(k+1)-1)*(C.size+1) := by
  by_contra! large
  exact noWitness (tested_of_large (S := G.edgeFinset) (fun _ h => h) girth mono computes k large)

end GirthRepresent

#print axioms GirthRepresent.tested_easy
