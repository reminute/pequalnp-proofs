import GuardFront
import GuardClauses

namespace G11GuardFront

open G11Certificate G11Protected

abbrev fires (A B X : Finset (Fin 11)) : Prop := ¬Disjoint X A ∧ ¬Disjoint X B

abbrev edgeGuard (A B : Finset (Fin 11)) (e : Fin 16) : Prop :=
  ∃ v ∈ edge e, ∀ z : Fin 24, fires A B (negative z) → v ∉ negative z

private theorem neg_bound : ∀ i : Fin 64, negatives[i.val]! < 2^24 := by decide
private theorem vertex_correct : ∀ (v : Fin 11) (z : Fin 24),
    vertexNeg[v.val]!.testBit z.val = true ↔ v ∈ negative z := by decide
private theorem star_correct : ∀ (v : Fin 11) (e : Fin 16),
    stars[v.val]!.testBit e.val = true ↔ v ∈ edge e := by decide

private theorem profile_neg (i j : Fin 64) (z : Fin 24) :
    (profile i j).neg.testBit z = true ↔ fires (support i) (support j) (negative z) := by
  simp only [profile, Nat.testBit_and, Bool.and_eq_true, neg_correct, fires]

private theorem profile_pos (i j : Fin 64) (e : Fin 16) :
    (profile i j).pos.testBit e = true ↔ fires (support i) (support j) (edge e) := by
  simp only [profile, Nat.testBit_and, Bool.and_eq_true, pos_correct, fires]

private theorem zero_of_disjoint (a b : Nat) (h : ∀ n : Nat, a.testBit n = true →
    b.testBit n = true → False) : a &&& b = 0 := by
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_and, Nat.zero_testBit]
  cases ha : a.testBit n <;> cases hb : b.testBit n <;> simp_all

private theorem neg_index {i j : Fin 64} {n : Nat} (h : (profile i j).neg.testBit n = true) : n < 24 := by
  by_contra! hn
  have lt : (profile i j).neg < 2^n :=
    lt_of_le_of_lt Nat.and_le_left ((neg_bound i).trans_le (Nat.pow_le_pow_right (by decide) hn))
  simp [Nat.testBit_lt_two_pow lt] at h

private theorem guard_step (n k : Nat) (xs : List Nat) (start : Nat)
    (h : start.testBit k = true ∨ ∃ v ∈ xs, n &&& vertexNeg[v]! = 0 ∧ stars[v]!.testBit k = true) :
    (xs.foldl (fun m v => if n &&& vertexNeg[v]! = 0 then m ||| stars[v]! else m) start).testBit k = true := by
  induction xs generalizing start with
  | nil => simpa using h
  | cons v tail ih =>
    apply ih
    rcases h with hs | ⟨w,hw,zero,yes⟩
    · left
      by_cases hv : n &&& vertexNeg[v]! = 0 <;> simp [hv, Nat.testBit_or, hs]
    · rcases List.mem_cons.mp hw with eq | remaining
      · subst w
        left
        simp [zero, Nat.testBit_or, yes]
      · exact Or.inr ⟨w,remaining,zero,yes⟩

private theorem profile_guard (i j : Fin 64) (e : Fin 16)
    (on : fires (support i) (support j) (edge e)) (guard : edgeGuard (support i) (support j) e) :
    (profile i j).guard.testBit e = true := by
  obtain ⟨v,hv,safe⟩ := guard
  have zero : (profile i j).neg &&& vertexNeg[v.val]! = 0 := by
    apply zero_of_disjoint
    intro n hn hb
    let z : Fin 24 := ⟨n,neg_index hn⟩
    exact safe z ((profile_neg i j z).mp hn) ((vertex_correct v z).mp hb)
  change ((profile i j).pos &&& guarded (profile i j).neg).testBit e = true
  rw [Nat.testBit_and, Bool.and_eq_true]
  exact ⟨(profile_pos i j e).mpr on,
    guard_step _ _ _ 0 (Or.inr ⟨v.val,List.mem_range.mpr v.isLt,zero,(star_correct v e).mpr hv⟩)⟩

private theorem bits_mono {a b : Nat} (sub : subBits a b = true) {n : Nat}
    (h : a.testBit n = true) : b.testBit n = true := by
  have eq : a &&& b = a := by simpa [subBits] using sub
  have h' := congrArg (fun v : Nat => v.testBit n) eq
  simpa [Nat.testBit_and, h] using h'

private theorem admissible_of_semantics (i j : Fin 64)
    (ab : ¬ support i ⊆ support j) (ba : ¬ support j ⊆ support i)
    (dirty : ∃ z : Fin 24, fires (support i) (support j) (negative z)) :
    admissible i j = true := by
  obtain ⟨z,hz⟩ := dirty
  have ne : (profile i j).neg ≠ 0 := by
    intro h
    have yes := (profile_neg i j z).mpr hz
    simp [h] at yes
  have h1 := mt (incl_correct i j).mp ab
  have h2 := mt (incl_correct j i).mp ba
  change negatives[i.val]! &&& negatives[j.val]! ≠ 0 at ne
  rw [Nat.and_comm] at h2
  simp [admissible, ne, h1, h2]

theorem numeric_cap
    (verified : ∀ i j : Fin 574, capOK (major i) (major j) = true)
    (U : Finset (Fin 16)) (A B C D : Finset (Fin 11))
    (aAllowed : allowed U A) (bAllowed : allowed U B) (cAllowed : allowed U C) (dAllowed : allowed U D)
    (aNe : A.Nonempty) (bNe : B.Nonempty) (cNe : C.Nonempty) (dNe : D.Nonempty)
    (ab : ¬ A ⊆ B) (ba : ¬ B ⊆ A) (cd : ¬ C ⊆ D) (dc : ¬ D ⊆ C)
    (firstDirty : ∃ z : Fin 24, fires A B (negative z))
    (secondDirty : ∃ z : Fin 24, fires C D (negative z))
    (compatible : ∀ z : Fin 24, ¬(fires A B (negative z) ∧ fires C D (negative z)))
    (supplied : ∀ e ∈ U,
      (fires A B (edge e) ∧ fires C D (edge e)) ∨
      (fires A B (edge e) ∧ edgeGuard A B e) ∨ (fires C D (edge e) ∧ edgeGuard C D e)) :
    U.card ≤ 4 ∨ ∀ e ∈ U, (18453 : Nat).testBit e.val = true := by
  obtain ⟨a,rfl,ka⟩ := clause_rep aAllowed aNe
  obtain ⟨b,rfl,kb⟩ := clause_rep bAllowed bNe
  obtain ⟨c,rfl,kc⟩ := clause_rep cAllowed cNe
  obtain ⟨d,rfl,kd⟩ := clause_rep dAllowed dNe
  let p := major (majorIndex a b)
  let q := major (majorIndex c d)
  have hp := majorizes a b (admissible_of_semantics a b ab ba firstDirty)
  have hq := majorizes c d (admissible_of_semantics c d cd dc secondDirty)
  change dominates (profile a b) p = true at hp
  change dominates (profile c d) q = true at hq
  simp only [dominates, Bool.and_eq_true] at hp hq
  have compatible' : p.neg &&& q.neg = 0 := by
    apply zero_of_disjoint
    intro n hn hm
    have na := bits_mono hp.1.1.2 hn
    have nc := bits_mono hq.1.1.2 hm
    let z : Fin 24 := ⟨n,neg_index na⟩
    exact compatible z ⟨(profile_neg a b z).mp na,(profile_neg c d z).mp nc⟩
  have inside (e : Fin 16) (he : e ∈ U) : (upper p q).testBit e = true := by
    have keep1 : (profile a b).kept.testBit e = true := by
      simp only [profile, Nat.testBit_and, ka e he, kb e he, Bool.and_self]
    have keep2 : (profile c d).kept.testBit e = true := by
      simp only [profile, Nat.testBit_and, kc e he, kd e he, Bool.and_self]
    simp only [upper, Nat.testBit_and, Nat.testBit_or, Bool.and_eq_true, Bool.or_eq_true]
    refine ⟨⟨?_,bits_mono hp.2 keep1⟩,bits_mono hq.2 keep2⟩
    rcases supplied e he with ⟨left,right⟩ | ⟨on,guard⟩ | ⟨on,guard⟩
    · exact Or.inl (Or.inl ⟨bits_mono hp.1.1.1 ((profile_pos a b e).mpr left),
                            bits_mono hq.1.1.1 ((profile_pos c d e).mpr right)⟩)
    · exact Or.inl (Or.inr (bits_mono hp.1.2 (profile_guard a b e on guard)))
    · exact Or.inr (bits_mono hq.1.2 (profile_guard c d e on guard))
  have bound : capOK p q = true := verified _ _
  simp [capOK, compatible'] at bound
  rcases bound with eq | small
  · exact Or.inr (fun e he => eq ▸ inside e he)
  · left
    have incl : U.image Fin.val ⊆ (upper p q).bitIndices.toFinset := by
      intro n hn
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hn
      exact List.mem_toFinset.mpr (Nat.mem_bitIndices.mpr (inside e he))
    have sz := Finset.card_le_card incl
    rw [Finset.card_image_of_injective _ Fin.val_injective] at sz
    exact sz.trans ((List.toFinset_card_le _).trans small)

end G11GuardFront
