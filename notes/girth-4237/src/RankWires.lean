import OwnershipBase

namespace GirthWires

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_1490

abbrev Signal (n : Nat) := (Fin n → Bool) → Bool

def signal (n : Nat) (C : Circuit) (w : Nat) : Signal n := fun x => val C (List.ofFn x) w

def readSignal (n : Nat) (C : Circuit) (j w : Nat) : Signal n :=
  if w<n+j then signal n C w else fun _ => false

structure Sums {X : Type} (ρ : (X → Bool) → Nat) : Prop where
  const : ∀ b : Bool, ρ (fun _ => b)=0
  conj : ∀ f g : X → Bool, ρ (fun x => f x && g x) ≤ ρ f + ρ g
  disj : ∀ f g : X → Bool, ρ (fun x => f x || g x) ≤ ρ f + ρ g

def charge (n : Nat) (ρ : Signal n → Nat) (C : Circuit) (j w : Nat) : Nat :=
  if w<n+j then ρ (signal n C w) else 0

theorem input_signal {n : Nat} (C : Circuit) (i : Fin n) : signal n C i.val = fun x => x i := by
  funext x
  rw [signal,val_input List.length_ofFn i.isLt]
  simp [List.getD_eq_getElem?_getD]

theorem gate_signal {n : Nat} (C : Circuit) (g : Nat) : signal n C (n+g) = gateVal n C g := rfl

theorem invalid_signal {n : Nat} (C : Circuit) {w : Nat} (bad : n+C.gates.length≤w) :
    signal n C w = fun _ => false := funext fun _ => val_ge List.length_ofFn bad

theorem output_signal {n : Nat} (C : Circuit) : circuitFun n C = signal n C C.output := rfl

theorem evaluated_gate {n : Nat} (C : Circuit) {j : Nat} (valid : j<C.gates.length) :
    gateVal n C j = fun x =>
      (gateAt C j).op.eval (((gateAt C j).inputs.map (readSignal n C j)).map (fun f => f x)) := by
  funext x
  change val C (List.ofFn x) (n+j) = _
  rw [val_gate List.length_ofFn valid,List.map_map]
  apply congrArg _
  apply List.map_congr_left
  intro w _
  by_cases earlier : w<n+j <;> simp only [readSignal, earlier,ite_true,ite_false,Function.comp_apply,signal]

theorem list_bound {X : Type} {ρ : (X → Bool) → Nat} (r : Sums ρ) (op : GateOp)
    (kind : op=GateOp.and ∨ op=GateOp.or) (fs : List (X → Bool)) :
    ρ (fun x => op.eval (fs.map (fun f => f x))) ≤ (fs.map ρ).sum := by
  induction fs with
  | nil =>
    rcases kind with rfl | rfl <;> exact (r.const _).le
  | cons f fs ih =>
    rcases kind with rfl | rfl
    · exact (r.conj f (fun x => GateOp.and.eval (fs.map (fun g => g x)))).trans (Nat.add_le_add_left ih _)
    · exact (r.disj f (fun x => GateOp.or.eval (fs.map (fun g => g x)))).trans (Nat.add_le_add_left ih _)

theorem gate_bound {n : Nat} {ρ : Signal n → Nat} (r : Sums ρ) {C : Circuit} (mc : Monotone2 C)
    (j : Fin C.gates.length) :
    ρ (gateVal n C j.val) ≤ ((gateAt C j.val).inputs.map (charge n ρ C j.val)).sum := by
  have kind : (gateAt C j.val).op=GateOp.and ∨ (gateAt C j.val).op=GateOp.or :=
    (mc _ (gateAt_mem j.isLt)).1
  have h := list_bound r _ kind ((gateAt C j.val).inputs.map (readSignal n C j.val))
  rw [evaluated_gate C j.isLt]
  apply h.trans_eq
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro w _
  by_cases earlier : w<n+j.val <;>
    simp only [Function.comp_apply,charge,readSignal,earlier,ite_true,ite_false,r.const]

theorem charge_le {n : Nat} (ρ : Signal n → Nat) (C : Circuit) (j w : Nat) :
    charge n ρ C j w ≤ ρ (signal n C w) := by
  unfold charge
  split <;> omega

theorem gate_bound_total {n : Nat} {ρ : Signal n → Nat} (r : Sums ρ) {C : Circuit} (mc : Monotone2 C)
    (j : Fin C.gates.length) :
    ρ (signal n C (n+j.val)) ≤ ((gateAt C j.val).inputs.map (fun w => ρ (signal n C w))).sum := by
  apply (gate_bound r mc j).trans
  generalize (gateAt C j.val).inputs = ws
  induction ws with
  | nil => rfl
  | cons w ws ih => exact Nat.add_le_add (charge_le ρ C j.val w) ih

theorem output_charge {n : Nat} {ρ : Signal n → Nat} (r : Sums ρ) (C : Circuit) :
    ρ (circuitFun n C)=charge n ρ C C.gates.length C.output := by
  rw [output_signal]
  unfold charge
  split
  · rfl
  · rename_i h
    rw [invalid_signal C (Nat.le_of_not_gt h),r.const]

end GirthWires

