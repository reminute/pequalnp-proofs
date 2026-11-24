import PEqualNP.Defs
import Mathlib.Tactic

namespace FanoRename

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

variable {n : ℕ}

def wire (p : Fin n → Fin n) (i : ℕ) := if h : i<n then (p ⟨i,h⟩).val else i
def gate (p : Fin n → Fin n) (g : Gate) : Gate := ⟨g.op,g.inputs.map (wire p)⟩
def circuit (p : Fin n → Fin n) (C : Circuit) : Circuit := ⟨C.gates.map (gate p),wire p C.output⟩

theorem wire_raw (p : Fin n → Fin n) (i : Fin n) : wire p i.val = (p i).val := by
  simp [wire,i.isLt]

theorem wire_high (p : Fin n → Fin n) {i : ℕ} (h : n ≤ i) : wire p i = i := by
  simp [wire,Nat.not_lt.mpr h]

theorem wire_lt (p : Fin n → Fin n) {N i : ℕ} (h : n≤N) : wire p i < N ↔ i < N := by
  by_cases lo : i<n
  · simp [wire,lo,lt_of_lt_of_le (p ⟨i,lo⟩).isLt h,lt_of_lt_of_le lo h]
  · rw [wire_high p (Nat.le_of_not_gt lo)]

theorem undo (e : Fin n ≃ Fin n) (i : ℕ) : wire e.symm (wire e i) = i := by
  by_cases lo : i<n
  · change wire e.symm (wire e (⟨i,lo⟩ : Fin n).val) = _
    rw [wire_raw,wire_raw,Equiv.symm_apply_apply]
  · simp [wire,lo]

theorem size (p : Fin n → Fin n) (C : Circuit) : (circuit p C).size = C.size := by
  simp [circuit,Circuit.size]

theorem at_gate (p : Fin n → Fin n) (C : Circuit) (j : ℕ) :
    gateAt (circuit p C) j = gate p (gateAt C j) := by
  simp only [gateAt,circuit,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases C.gates[j]? <;> rfl

theorem ao (p : Fin n → Fin n) {C : Circuit} (h : IsAO2 n C) : IsAO2 n (circuit p C) := by
  refine ⟨?_,?_,?_⟩
  · intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact h.1 a ha
  · intro j hj i input
    rw [at_gate] at input
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp input
    apply (wire_lt p (by omega)).2
    apply h.2.1 j _ a ha
    simpa [circuit] using hj
  · intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    simpa [gate] using h.2.2 a ha

theorem operand (p : Fin n → Fin n) {C : Circuit} (h : IsAO2 n C) {j : ℕ}
    (valid : j<C.size) (b : Fin 2) : opnd (circuit p C) j b = wire p (opnd C j b) := by
  have member : gateAt C j ∈ C.gates := by
    simp [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (show j<C.gates.length from valid)]
  have bound : b.val < (gateAt C j).inputs.length := by rw [h.2.2 _ member]; exact b.isLt
  simp [opnd,at_gate,gate,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem bound]

theorem distinct (e : Fin n ≃ Fin n) {C : Circuit} (h : IsAO2 n C)
    (old : ∀ j<C.size, opnd C j 0 ≠ opnd C j 1) :
    ∀ j<(circuit e C).size, opnd (circuit e C) j 0 ≠ opnd (circuit e C) j 1 := by
  intro j valid eq
  rw [size] at valid
  rw [operand e h valid,operand e h valid] at eq
  exact old j valid (by simpa only [undo] using congrArg (wire e.symm) eq)

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem evaluate_fold (p : Fin n → Fin n) (gs : List Gate) (u v : List Bool)
    (len : u.length = v.length) (enough : n≤u.length)
    (agree : ∀ w, v.getD (wire p w) false = u.getD w false) : ∀ w,
    ((gs.map (gate p)).foldl step v).getD (wire p w) false =
    (gs.foldl step u).getD w false := by
  induction gs generalizing u v with
  | nil => exact agree
  | cons g gs ih =>
    have values : ((gate p g).inputs.map fun i => v.getD i false) =
        g.inputs.map fun i => u.getD i false := by
      simp only [gate,List.map_map,Function.comp_def]
      apply List.map_congr_left
      exact fun i _ => agree i
    apply ih
    · simp [step,len]
    · simp [step]; omega
    · intro i
      by_cases earlier : i<u.length
      · have right : wire p i < v.length := len ▸ (wire_lt p enough).2 earlier
        simpa [step,List.getD_eq_getElem?_getD,List.getElem?_append_left right,
          List.getElem?_append_left earlier] using agree i
      · have high : n ≤ i := by omega
        rw [wire_high p high]
        simp only [step,values]
        change (v ++ [_]).getD i false = (u ++ [_]).getD i false
        rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),len]
        rfl

theorem wires (p : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool) (w : ℕ) :
    ((circuit p C).wires (List.ofFn x)).getD (wire p w) false =
    (C.wires (List.ofFn (x ∘ p))).getD w false := by
  apply evaluate_fold p C.gates (List.ofFn (x ∘ p)) (List.ofFn x)
  · simp
  · simp
  · intro i
    by_cases hi : i<n
    · simp [wire,hi,List.getD_eq_getElem?_getD,(p ⟨i,hi⟩).isLt,Function.comp_def]
    · simp [wire,hi,List.getD_eq_getElem?_getD]

theorem eval (p : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool) :
    (circuit p C).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ p)) := wires p C x C.output

end FanoRename

#print axioms FanoRename.eval
#print axioms FanoRename.distinct
