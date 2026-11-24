import SuffixBarrier

namespace Cubic1971.RejectWitness

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity StarReader

private theorem retains (gs : List Gate) (w : List Bool) (i : Nat) (valid : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w ++ [gateValue g w])).getD i false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ valid]

/-- A minimum circuit cannot use a raw-input AND with a positive suffix unless
    some rejected assignment keeps the raw operand on and disables its partner. -/
theorem and_witness (n : Nat) (C : Circuit) (v : Fin n) (pre post : List Gate)
    (r : Gate) (k : Nat) (layout : C.gates = pre ++ r :: post) (legal : FanInTwo C)
    (least : ∀ s, HasCircuitSize n (circuitFun n C) s → C.size ≤ s)
    (op : r.op = .and) (inputs : r.inputs = [v.val,k] ∨ r.inputs = [k,v.val])
    (suffix : ∀ g ∈ post, g.op ≠ .not) :
    ∃ x : Fin n → Bool, circuitFun n C x = false ∧ x v = true ∧
      circuitFun n (⟨pre,k⟩ : Circuit) x = false := by
  classical
  by_contra absent
  have conjunction (w : List Bool) :
      gateValue r w = (w.getD v.val false && w.getD k false) := by
    rcases inputs with h | h <;>
      simp only [gateValue, op, h, List.map_cons, List.map_nil, GateOp.eval,
        List.all_cons, List.all_nil, id_eq, Bool.and_true]
    exact Bool.and_comm ..
  apply Exists.elim (SuffixBarrier.needs_not C _ v pre post r layout legal rfl least ?_ ?_)
    (fun g h => suffix g h.1 h.2)
  · intro x
    dsimp only
    rw [conjunction, Bool.and_eq_true]
    exact And.left
  · intro x off
    dsimp only
    rw [conjunction]
    have raw : (run pre (List.ofFn x)).getD v.val false = x v := by
      rw [retains _ _ _ (by simp)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left v.isLt, Option.getD_some]
    rw [raw]
    cases xv : x v with
    | false => rfl
    | true =>
      cases h : (run pre (List.ofFn x)).getD k false with
      | false => exact False.elim (absent ⟨x,off,xv,h⟩)
      | true => rfl

end Cubic1971.RejectWitness

#print axioms Cubic1971.RejectWitness.and_witness
