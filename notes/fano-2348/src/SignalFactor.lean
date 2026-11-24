import FactorWitness
import OwnershipBase

namespace FanoFactor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_1490

def signal (C : Circuit) (w : ℕ) (x : Input) := val C (List.ofFn x) w

theorem equation {C : Circuit} {k a b : ℕ} {op : GateOp}
    (hg : C.gates[k]? = some ⟨op,[a,b]⟩) (ha : a < 14+k) (hb : b < 14+k) (x : Input) :
    signal C (14+k) x = op.eval [signal C a x, signal C b x] := by
  have valid : k < C.gates.length := by
    by_contra! off
    simp [List.getElem?_eq_none off] at hg
  have eq : gateAt C k = ⟨op,[a,b]⟩ := by simp [gateAt,List.getD_eq_getElem?_getD,hg]
  rw [signal,val_gate List.length_ofFn valid,eq]
  simp [ha,hb,signal]

theorem increasing_signal (C : Circuit)
    (normal : ∀ k g, C.gates[k]? = some g → (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : Nat, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+k ∧ b < 14+k) (w : ℕ) :
    Increasing (signal C w) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w < 14
    · have eq (z : Input) : signal C w z = z ⟨w,raw⟩ := by
        rw [signal,val_input List.length_ofFn raw]
        rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using raw)]
        simp only [Option.getD_some,List.getElem_ofFn]
      intro x y sub old
      exact (eq y).trans (sub _ ((eq x).symm.trans old))
    let k := w-14
    have index : w = 14+k := by dsimp [k]; omega
    by_cases valid : k < C.gates.length
    · have atK : C.gates[k]? = some C.gates[k] := List.getElem?_eq_getElem valid
      obtain ⟨kind,a,b,inputs,_,ha,hb⟩ := normal k _ atK
      have gate : C.gates[k]? = some ⟨C.gates[k].op,[a,b]⟩ := by rw [←inputs]; exact atK
      have ma := ih a (ha.trans_le index.ge)
      have mb := ih b (hb.trans_le index.ge)
      intro x y sub
      rw [index,equation gate ha hb x,equation gate ha hb y]
      rcases kind with con | dis
      · simp only [con,GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true,Bool.and_eq_true_iff]
        exact fun ⟨u,v⟩ => ⟨ma x y sub u, mb x y sub v⟩
      · simp only [dis,GateOp.eval,List.any_cons,List.any_nil,id_eq,Bool.or_false,Bool.or_eq_true_iff]
        exact Or.imp (ma x y sub) (mb x y sub)
    · intro x y sub
      have off : 14+C.gates.length ≤ w := by omega
      change val C (List.ofFn x) w = true → val C (List.ofFn y) w = true
      rw [val_ge (x := List.ofFn x) List.length_ofFn off]
      simp

theorem sound_and {C : Circuit} (spec : ∀ x : Input, C.eval (List.ofFn x) = true ↔ incidence x = true)
    {k a b : ℕ} (out : C.output = 14+k) (hg : C.gates[k]? = some ⟨.and,[a,b]⟩)
    (ha : a < 14+k) (hb : b < 14+k) :
    ∀ x, signal C a x = true → signal C b x = true → incidence x = true := by
  intro x left right
  apply (spec x).mp
  change signal C C.output x = true
  rw [out,equation hg ha hb x]
  simp [GateOp.eval,left,right]

end FanoFactor
