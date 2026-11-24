import Cell

/-!
The restriction of a positive literal partition to edge rows and outer-neighborhood
columns is the graph transfer used in PEqualNP PR #10101:
https://github.com/open-goat/pequalnp-proofs/pull/10101 .
The proof below reuses the local independence result through `Cell.cell`.
-/

namespace Rect4123.GraphTransfer

open PEqualNP.MetaComplexity GirthEdgeNegatives

variable {n k : ℕ}

abbrev Spec (H : SimpleGraph (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, f x = true ↔ ∃ a b, H.Adj a b ∧ x a = true ∧ x b = true

theorem raise_preserves (H : SimpleGraph (Fin n)) (f : (Fin n → Bool) → Bool)
    (spec : Spec H f) (v : Fin n) (x : Fin n → Bool) (on : f x = true) :
    f (Function.update x v true) = true := by
  obtain ⟨a,b,ab,ha,hb⟩ := (spec x).mp on
  have stays (i : Fin n) (hi : x i=true) : Function.update x v true i=true := by
    by_cases eq : i=v
    · simp [eq]
    · simpa [Function.update_of_ne eq] using hi
  exact (spec _).mpr ⟨a,b,ab,stays a ha,stays b hb⟩

abbrev Rectangles (H : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ (R S : Fin k → Fin n → Fin n → Prop) (label : Fin k → Fin n),
    ∀ a b c d, H.Adj a b → c=d ∨ H.Adj c d →
      (∃! j, R j a b ∧ S j c d) ∧
      ∀ j, R j a b → S j c d →
        (label j = a ∨ label j = b) ∧
        ¬ ((H.Adj c (label j) ∨ H.Adj d (label j)) ∧ label j ≠ c ∧ label j ≠ d)

theorem of_positive_girth (H : SimpleGraph (Fin n)) (fallback : Fin n)
    (f : (Fin n → Bool) → Bool) (girth : GirthFive H) (spec : Spec H f)
    {A B : Fin k → (Fin n → Bool) → Bool} {pos : Fin k → ℕ}
    (part : IsLiteralPartition n f k A B pos (fun _ => true)) : Rectangles H k := by
  classical
  let row (a b z : Fin n) := decide (z=a ∨ z=b)
  let forbidden (c d z : Fin n) := (H.Adj c z ∨ H.Adj d z) ∧ z≠c ∧ z≠d
  let col (c d z : Fin n) := decide (forbidden c d z)
  let label (j : Fin k) : Fin n := if bound : pos j<n then ⟨pos j,bound⟩ else fallback
  obtain ⟨_,_,lit,cover⟩ := part
  refine ⟨fun j a b => A j (row a b) = true, fun j c d => B j (col c d)=true, label, ?_⟩
  intro a b c d ab shape
  have on : f (row a b)=true := (spec _).mpr ⟨a,b,ab,by simp [row],by simp [row]⟩
  have off : f (col c d)=false := by
    apply Bool.eq_false_iff.mpr
    intro active
    obtain ⟨u,v,uv,hu,hv⟩ := (spec _).mp active
    obtain ⟨z,hz,legal⟩ := Cell.cell H girth uv shape
    rcases hz with rfl | rfl
    · exact legal (of_decide_eq_true hu)
    · exact legal (of_decide_eq_true hv)
  refine ⟨cover _ _ on off, ?_⟩
  intro j rowHit colHit
  obtain ⟨i,pi,inside,outside⟩ := lit j _ _ rowHit colHit
  have ident : label j = i := by
    have bound : pos j<n := pi ▸ i.isLt
    apply Fin.ext
    simpa [label,bound] using pi
  rw [ident]
  exact ⟨of_decide_eq_true inside, fun h => outside (decide_eq_true h)⟩

/-- Positive partitions give the rectangle conclusion on the actual deleted graph
in the desk statement. The circuit-size assumption is used to obtain a partition. -/
theorem of_positive (G H : SimpleGraph (Fin n)) (v : Fin n) (f : (Fin n → Bool) → Bool)
    (girth : ∀ u (p : G.Walk u u), p.IsCycle → 7 ≤ p.length)
    (deleted : H = G.deleteEdges (G.incidenceSet v)) (spec : Spec H f)
    {A B : Fin k → (Fin n → Bool) → Bool} {pos : Fin k → ℕ}
    (part : IsLiteralPartition n f k A B pos (fun _ => true)) : Rectangles H k := by
  have sub : H ≤ G := deleted ▸ SimpleGraph.deleteEdges_le _
  exact of_positive_girth H v f (Cell.girth_of_subgraph sub girth) spec part

end Rect4123.GraphTransfer

#print axioms Rect4123.GraphTransfer.of_positive
#print axioms Rect4123.GraphTransfer.raise_preserves
