import LiveFewShared
import OrderedRepresentatives

namespace GirthRepresent

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership GirthFiveCore GirthEdgeBound GirthEdgeNegatives GirthExceptions

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
variable {S : Finset (Sym2 (Fin n))}

/-- On each input where the second gate agrees with the output, so does the first. -/
def agrees (n : ℕ) (C : Circuit) (t i : Fin C.gates.length) : Prop :=
  ∀ x, gateVal n C i.val x = circuitFun n C x → gateVal n C t.val x = circuitFun n C x

theorem agrees_covers (sub : S ⊆ G.edgeFinset) (girth : GirthFive G)
    (computes : circuitFun n C = graphFun G ∅) {t i : Fin C.gates.length} (h : agrees n C t i) :
    Covers (GirthRank.positive (edgeRows S)) (GirthRank.negative (edgeRows S) G.Adj)
      (gateVal n C t.val) (gateVal n C i.val) := by
  constructor
  · intro e on
    have out : circuitFun n C _ = true := computes ▸ positive_on sub e
    exact (h _ (on.trans out.symm)).trans out
  · intro y off
    have out : circuitFun n C _ = false := computes ▸ negative_off sub girth y
    have zero : gateVal n C i.val (GirthRank.negative (edgeRows S) G.Adj y) = false := by simpa using off
    have good := (h _ (zero.trans out.symm)).trans out
    simp [good]

theorem before_output {w : ℕ} (path : ReachesOutput n C w) : w ≤ C.output := by
  induction path with
  | output => rfl
  | input _ used ih => exact (of_decide_eq_true (List.mem_filter.mp used).2 : _ < _).le.trans ih

def readers (n : ℕ) (C : Circuit) (j : Fin C.gates.length) : Finset (Fin C.gates.length) :=
  Finset.univ.filter fun k => j < k ∧ n+j.val ∈ (gateAt C k.val).inputs

/-- Two live reads require two distinct later consuming gates. The output tap
    cannot be combined with a live downstream read of the very same wire. -/
theorem two_readers {j : Fin C.gates.length} (many : 1 < liveReads n C j) :
    1 < (readers n C j).card := by
  classical
  have source (k : Fin C.gates.length) (used : n+j.val ∈ liveInputs n C k) :
      n+j.val < C.output ∧ (j < k ∧ n+j.val ∈ (gateAt C k.val).inputs) := by
    unfold liveInputs at used
    split at used
    · rename_i reachable
      obtain ⟨seen,valid⟩ := List.mem_filter.mp used
      have early : n+j.val < n+k.val := of_decide_eq_true valid
      exact ⟨early.trans_le (before_output reachable),Nat.lt_of_add_lt_add_left early,List.mem_dedup.mp seen⟩
    · simp at used
  have notOut : C.output ≠ n+j.val := by
    intro eq
    have z (k : Fin C.gates.length) : (liveInputs n C k).count (n+j.val) = 0 :=
      List.count_eq_zero_of_not_mem fun mem => (source k mem).1.ne eq.symm
    simp [liveReads,readCount,eq,z] at many
  have one (k : Fin C.gates.length) : (liveInputs n C k).count (n+j.val) ≤
      if j < k ∧ n+j.val ∈ (gateAt C k.val).inputs then 1 else 0 := by
    by_cases u : n+j.val ∈ liveInputs n C k
    · rw [ite_eq_left (source k u).2]
      apply List.nodup_iff_count_le_one.mp
      unfold liveInputs
      split
      · exact (List.nodup_dedup _).filter _
      · exact List.nodup_nil
    · simp [List.count_eq_zero_of_not_mem u]
  rw [liveReads,readCount,ite_eq_right notOut,Nat.zero_add] at many
  rw [readers,Finset.card_filter]
  exact many.trans_le (Finset.sum_le_sum fun k _ => one k)

/-- A large graph-to-circuit ratio forces an ordered set of multiply read
    gates. Every later gate agrees with the output on some input where the
    earlier gate disagrees. -/
def witness (n : ℕ) (C : Circuit) (m : ℕ) : Prop :=
  ∃ Q : Finset (Fin C.gates.length), Q.card = m ∧
    (∀ j ∈ Q, 1 < (readers n C j).card) ∧
    ∀ t ∈ Q, ∀ i ∈ Q, t < i → ∃ x,
      gateVal n C i.val x = circuitFun n C x ∧ gateVal n C t.val x ≠ circuitFun n C x

theorem witness_of_large (sub : S ⊆ G.edgeFinset) (girth : GirthFive G)
    (mono : Monotone2 C) (computes : circuitFun n C = graphFun G ∅) (k : ℕ)
    (large : (2^(k+1)-1)*(C.size+1) < S.card) : witness n C (k+1) := by
  classical
  let H := liveHigh S G C 1
  let R := agrees n C
  have reflex (a) (_ : a ∈ H) : R a a := fun _ same => same
  have transitive {a b c} (ab : R a b) (bc : R b c) : R a c := fun x right => ab x (bc x right)
  have noCover (T : Finset (Fin C.gates.length)) (inside : T ⊆ H) (few : T.card ≤ k)
      (rep : ∀ x ∈ H, ∃ t ∈ T, t ≤ x ∧ R t x) : False := by
    apply large.not_ge
    have bound := live_covered sub girth mono computes (B := 1) (by decide) T few
      (fun i hi => reaches_of_live_reads (Nat.zero_lt_one.trans (Finset.mem_filter.mp (inside hi)).2.1))
      (fun i hi => by
        obtain ⟨t,tm,early,good⟩ := rep i hi
        exact ⟨t,tm,early,agrees_covers sub girth computes good⟩)
    simpa using bound
  obtain ⟨Q,subset,card,sep⟩ := GirthOrdered.packing H R k reflex transitive noCover
  refine ⟨Q,card,fun i hi => two_readers (Finset.mem_filter.mp (subset hi)).2.1,?_⟩
  intro t ht i hi lt
  by_contra! all
  exact (sep t ht i hi lt) (fun x correct => all x correct)

theorem easy (k n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (girth : GirthFive G) (C : Circuit) (mono : Monotone2 C)
    (computes : circuitFun n C = graphFun G ∅) (noWitness : ¬witness n C (k+1)) :
    G.edgeFinset.card ≤ (2^(k+1)-1)*(C.size+1) := by
  by_contra! large
  exact noWitness (witness_of_large (S := G.edgeFinset) (fun _ h => h) girth mono computes k large)

end GirthRepresent

#print axioms GirthRepresent.easy
