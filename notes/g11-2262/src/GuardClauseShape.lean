import GuardClauseBase

namespace G11GuardFront

private theorem vertex_width : ∀ i : Fin 64, vertices[i.val]! < 2^11 := by decide

theorem incl_correct (i j : Fin 64) : vertices[i.val]! &&& vertices[j.val]! = vertices[i.val]! ↔
    support i ⊆ support j := by
  constructor
  · intro h v hv
    have ha : vertices[i.val]!.testBit v.val = true := (Finset.mem_filter.mp hv).2
    have eq := congrArg (fun m : Nat => m.testBit v.val) h
    simp only [Nat.testBit_and,ha,Bool.true_and] at eq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq⟩
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_and]
    cases ha : vertices[i.val]!.testBit k with
    | false => simp
    | true =>
      have lt : k < 11 := by
        by_contra! large
        have hf := Nat.ge_two_pow_of_testBit ha
        have hg : 2^11 ≤ 2^k := Nat.pow_le_pow_right (by decide) large
        exact (Nat.not_lt_of_ge (hg.trans hf)) (vertex_width i)
      let v : Fin 11 := ⟨k, lt⟩
      have hi : v ∈ support i := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩
      exact (Finset.mem_filter.mp (h hi)).2

end G11GuardFront
