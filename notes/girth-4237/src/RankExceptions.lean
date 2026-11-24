import RankPartition
import MatrixWires
import GatePrefixRank

namespace GirthExceptions

open GirthWires GirthPartition GirthPotential GirthFiveCore
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

def budget (a : ℕ) : ℕ → ℕ
  | 0 => a
  | k+1 => budget a k + budget a k + a

theorem base_le (a k : ℕ) : a ≤ budget a k := by
  cases k <;> simp [budget]

theorem closed_budget (a k : ℕ) : budget a k = (2^(k+1)-1)*a := by
  induction k with
  | zero => simp [budget]
  | succ k ih =>
    have pos : 0 < 2^(k+1) := by positivity
    have step : 2^(k+1+1)-1 = (2^(k+1)-1) + (2^(k+1)-1) + 1 := by
      rw [pow_succ (2 : ℕ) (k+1)]
      omega
    simp only [budget,ih,step,Nat.add_mul,one_mul]

variable {I J : Type} [Fintype I] [Fintype J] {n : ℕ}

/-- The rectangle where f separates a positive and a negative sample is
    contained in the corresponding rectangle of h. -/
def Covers {X : Type} (pos : I → X) (neg : J → X) (h f : X → Bool) : Prop :=
  (∀ i, f (pos i) = true → h (pos i) = true) ∧
  (∀ j, !(f (neg j)) = true → !(h (neg j)) = true)

theorem covered_le {X : Type} {pos : I → X} {neg : J → X} {h f : X → Bool}
    (cover : Covers pos neg h f) (A : Matrix I J ℝ) :
    weight A pos neg f ≤ weight A pos neg h := block_mono A cover.1 cover.2

/-- Only a bounded number of earlier representatives is needed when the
    other exceptional gates' crossing rectangles are contained in theirs. -/
theorem cover_bound (pos : I → (Fin n → Bool)) (neg : J → (Fin n → Bool))
    (C : Circuit) (B : ℕ) (shared eligible : Fin C.gates.length → Prop)
    (outBound : ∀ A : Matrix I J ℝ, (∀ v : Fin n, weight A pos neg (fun x => x v) ≤ B) →
      (∀ i, shared i → weight A pos neg (gateVal n C i.val) ≤ B) →
      weight A pos neg (circuitFun n C) ≤ B*(C.size+1))
    (earlierBound : ∀ A : Matrix I J ℝ, (∀ v : Fin n, weight A pos neg (fun x => x v) ≤ B) →
      ∀ j, eligible j →
      (∀ i : Fin C.gates.length, i.val < j.val → shared i → weight A pos neg (gateVal n C i.val) ≤ B) →
      weight A pos neg (gateVal n C j.val) ≤ B*(C.size+1))
    (k : ℕ) (M : Matrix I J ℝ)
    (T : Finset (Fin C.gates.length)) (card : T.card ≤ k)
    (admissible : ∀ i ∈ T, eligible i)
    (raw : ∀ v : Fin n, weight M pos neg (fun x => x v) ≤ B)
    (small : ∀ i : Fin C.gates.length, i ∉ T → shared i →
      weight M pos neg (gateVal n C i.val) ≤ B ∨
      ∃ t ∈ T, t.val ≤ i.val ∧ Covers pos neg (gateVal n C t.val) (gateVal n C i.val)) :
    weight M pos neg (circuitFun n C) ≤ budget (B*(C.size+1)) k := by
  classical
  have empty (A : Matrix I J ℝ) (k : ℕ)
      (inputs : ∀ v : Fin n, weight A pos neg (fun x => x v) ≤ B)
      (all : ∀ i : Fin C.gates.length, shared i →
        weight A pos neg (gateVal n C i.val) ≤ B) :
      weight A pos neg (circuitFun n C) ≤ budget (B*(C.size+1)) k :=
    (outBound A inputs all).trans (base_le _ _)
  induction k generalizing M T with
  | zero =>
    have eq : T = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero card)
    apply empty M 0 raw
    simpa [eq] using small
  | succ k ih =>
    by_cases nonempty : T.Nonempty
    · let j := T.min' nonempty
      let h := gateVal n C j.val
      have jm : j ∈ T := T.min'_mem nonempty
      have reduced : (T.erase j).card ≤ k := by
        rw [Finset.card_erase_of_mem jm]
        omega
      have gateCap : weight M pos neg h ≤ B*(C.size+1) := by
        apply earlierBound M raw j (admissible j jm)
        intro i before reads
        have notIn : i ∉ T := fun im => (Nat.not_lt_of_ge (T.min'_le i im)) before
        rcases small i notIn reads with low | ⟨t,tm,ti,_⟩
        · exact low
        · exact (Nat.not_lt_of_ge (Nat.le_trans (T.min'_le t tm) ti) before).elim
      have child (A : Matrix I J ℝ)
          (restricted : ∀ f, weight A pos neg f ≤ weight M pos neg f)
          (zero : weight A pos neg h = 0) :
          weight A pos neg (circuitFun n C) ≤ budget (B*(C.size+1)) k := by
        apply ih A (T.erase j) reduced (fun i hi => admissible i (Finset.mem_of_mem_erase hi))
          (fun v => (restricted _).trans (raw v))
        intro i outside reads
        by_cases same : i = j
        · subst i
          exact Or.inl (zero.le.trans (Nat.zero_le _))
        · rcases small i (fun im => outside (Finset.mem_erase.mpr ⟨same,im⟩)) reads with
              low | ⟨t,tm,ti,included⟩
          · exact Or.inl ((restricted _).trans low)
          · by_cases chosen : t = j
            · subst t
              exact Or.inl ((covered_le included A).trans (zero.le.trans (Nat.zero_le _)))
            · exact Or.inr ⟨t, Finset.mem_erase.mpr ⟨chosen,tm⟩, ti, included⟩
      have left := child (rowOff M pos h) (weight_le M pos neg _ _) (rowOff_zero M pos neg h)
      have right := child (bothOn M pos neg h) (weight_le M pos neg _ _) (bothOn_zero M pos neg h)
      exact (split_weight M pos neg _ h).trans (Nat.add_le_add (Nat.add_le_add left right) gateCap)
    · have eq := Finset.not_nonempty_iff_eq_empty.mp nonempty
      apply empty M (k+1) raw
      simpa [eq] using small

theorem partition_bound (pos : I → (Fin n → Bool)) (neg : J → (Fin n → Bool))
    (C : Circuit) (B : ℕ) (shared eligible : Fin C.gates.length → Prop)
    (outBound : ∀ A : Matrix I J ℝ, (∀ v : Fin n, weight A pos neg (fun x => x v) ≤ B) →
      (∀ i, shared i → weight A pos neg (gateVal n C i.val) ≤ B) →
      weight A pos neg (circuitFun n C) ≤ B*(C.size+1))
    (earlierBound : ∀ A : Matrix I J ℝ, (∀ v : Fin n, weight A pos neg (fun x => x v) ≤ B) →
      ∀ j, eligible j →
      (∀ i : Fin C.gates.length, i.val < j.val → shared i → weight A pos neg (gateVal n C i.val) ≤ B) →
      weight A pos neg (gateVal n C j.val) ≤ B*(C.size+1))
    (k : ℕ) (M : Matrix I J ℝ)
    (T : Finset (Fin C.gates.length)) (card : T.card ≤ k)
    (admissible : ∀ i ∈ T, eligible i)
    (raw : ∀ v : Fin n, weight M pos neg (fun x => x v) ≤ B)
    (small : ∀ i : Fin C.gates.length, i ∉ T → shared i →
      weight M pos neg (gateVal n C i.val) ≤ B) :
    weight M pos neg (circuitFun n C) ≤ budget (B*(C.size+1)) k :=
  cover_bound pos neg C B shared eligible outBound earlierBound k M T card admissible raw
    (fun i hi active => Or.inl (small i hi active))

theorem bounded (pos : I → (Fin n → Bool)) (neg : J → (Fin n → Bool))
    (C : Circuit) (mono : Monotone2 C) (B k : ℕ) (M : Matrix I J ℝ)
    (T : Finset (Fin C.gates.length)) (card : T.card ≤ k)
    (raw : ∀ v : Fin n, weight M pos neg (fun x => x v) ≤ B)
    (small : ∀ i : Fin C.gates.length, i ∉ T → 1 < gateReads (n := n) C i →
      weight M pos neg (gateVal n C i.val) ≤ B) :
    weight M pos neg (circuitFun n C) ≤ budget (B*(C.size+1)) k :=
  partition_bound pos neg C B (fun i => 1 < gateReads (n := n) C i) (fun _ => True)
    (fun A inputs => signal_bound _ B (matrix_sums A pos neg) inputs C mono)
    (fun A inputs j _ => gate_signal_bound _ B (matrix_sums A pos neg) inputs C mono j)
    k M T card (fun _ _ => True.intro) raw small

end GirthExceptions
