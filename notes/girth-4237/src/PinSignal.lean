import RankWires

namespace GirthPin

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_1490 GirthWires

/-- Empty AND and empty OR are the constant true and false gates in the circuit model. -/
def constGate (b : Bool) : Gate := ⟨if b then .and else .or,[]⟩

/-- Pin gate number j, retaining the original indices and designated output. -/
def force (_n : Nat) (C : Circuit) (j : Nat) (b : Bool) : Circuit :=
  {C with gates := C.gates.set j (constGate b)}

@[simp] theorem force_length (n : Nat) (C : Circuit) (j : Nat) (b : Bool) :
    (force n C j b).gates.length=C.gates.length := List.length_set

@[simp] theorem force_size (n : Nat) (C : Circuit) (j : Nat) (b : Bool) :
    (force n C j b).size=C.size := force_length n C j b

@[simp] theorem force_output (n : Nat) (C : Circuit) (j : Nat) (b : Bool) :
    (force n C j b).output=C.output := rfl

theorem force_invalid (n : Nat) (C : Circuit) (j : Nat) (b : Bool) (bad : C.gates.length≤j) :
    force n C j b=C := by simp [force,List.set_eq_of_length_le bad]

theorem at_pin (n : Nat) (C : Circuit) (j : Nat) (b : Bool) (valid : j<C.gates.length) :
    gateAt (force n C j b) j=constGate b := by
  simp only [gateAt,force,List.getD_eq_getElem?_getD,List.getElem?_set_self valid,Option.getD_some]

theorem off_pin (n : Nat) (C : Circuit) (j : Nat) (b : Bool) (k : Nat) (diff : k≠j) :
    gateAt (force n C j b) k=gateAt C k := by
  simp only [gateAt,force,List.getD_eq_getElem?_getD,List.getElem?_set_ne diff.symm]

theorem force_inputs (n : Nat) (C : Circuit) (j : Nat) (b : Bool) (k : Nat) (valid : k<C.gates.length) :
    (gateAt (force n C j b) k).inputs=if k=j then [] else (gateAt C k).inputs := by
  by_cases eq : k=j
  · subst k
    simp [at_pin n C j b valid,constGate]
  · simp [eq,off_pin n C j b k eq]

theorem pin_eval (n : Nat) (C : Circuit) (j : Nat) (b : Bool) (valid : j<C.gates.length)
    (x : Fin n → Bool) : gateVal n (force n C j b) j x=b := by
  change val (force n C j b) (List.ofFn x) (n+j)=b
  rw [val_gate List.length_ofFn (by simpa using valid),at_pin n C j b valid]
  cases b <;> rfl

theorem pinned_signal (n : Nat) (C : Circuit) (j : Nat) (b : Bool) (valid : j<C.gates.length) :
    signal n (force n C j b) (n+j)=fun _ => b := funext (pin_eval n C j b valid)

theorem force_mono (n : Nat) (C : Circuit) (j : Nat) (b : Bool) (mc : Monotone2 C) : Monotone2 (force n C j b) := by
  intro g mem
  obtain ⟨k,hk,eq⟩ := List.mem_iff_getElem.mp mem
  have valid : k<C.gates.length := by simpa using hk
  have same : gateAt (force n C j b) k=g := (gateAt_eq hk).trans eq
  by_cases cut : k=j
  · subst k
    rw [at_pin n C j b valid] at same
    rw [← same]
    cases b <;> simp [constGate]
  · rw [off_pin n C j b k cut] at same
    exact same ▸ mc _ (gateAt_mem valid)

/-- Compare every wire by following only operands available when that gate ran. -/
private theorem relate {n : Nat} (x : Fin n → Bool) (C D : Circuit) (j : Nat)
    (R : Bool → Bool → Prop) (reflR : ∀ t, R t t)
    (length : D.gates.length=C.gates.length)
    (pin : j<C.gates.length → R (gateVal n C j x) (gateVal n D j x))
    (same : ∀ k, k≠j → gateAt D k=gateAt C k)
    (op : ∀ k<C.gates.length, k≠j → ∀ f g : Nat → Bool,
      (∀ u ∈ (gateAt C k).inputs, R (f u) (g u)) →
      R ((gateAt C k).op.eval ((gateAt C k).inputs.map f)) ((gateAt C k).op.eval ((gateAt C k).inputs.map g)))
    (w : Nat) : R (signal n C w x) (signal n D w x) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    change R (val C (List.ofFn x) w) (val D (List.ofFn x) w)
    by_cases raw : w<n
    · rw [val_input List.length_ofFn raw,val_input List.length_ofFn raw]
      exact reflR _
    by_cases bad : n+C.gates.length≤w
    · rw [val_ge List.length_ofFn bad,val_ge List.length_ofFn (by omega)]
      exact reflR _
    let k := w-n
    have eq : w=n+k := by dsimp [k]; omega
    have valid : k<C.gates.length := by omega
    rw [eq]
    by_cases which : k=j
    · exact which ▸ pin (which ▸ valid)
    rw [val_gate List.length_ofFn valid,val_gate List.length_ofFn (by omega),same k which]
    apply op k valid which
    intro u _
    by_cases available : u<n+k
    · simp only [available,ite_true]
      exact ih u (by omega)
    · simp only [available,ite_false]
      exact reflR _

/-- Pinning a gate to its value on this input preserves every wire on that input. -/
theorem pin_correct {n : Nat} (C : Circuit) (j : Nat) (b : Bool) (x : Fin n → Bool)
    (sameValue : gateVal n C j x=b) (w : Nat) : signal n C w x=signal n (force n C j b) w x := by
  apply relate x C (force n C j b) j Eq (fun _ => rfl) (force_length ..)
  · intro valid
    exact sameValue.trans (pin_eval n C j b valid x).symm
  · exact off_pin n C j b
  · intro k _ _ f g sameReads
    exact congrArg _ (List.map_congr_left sameReads)

/-- On a monotone circuit, a wire true with the gate pinned low is true with it pinned high. -/
theorem pin_monotone {n : Nat} (C : Circuit) (mc : Monotone2 C) (j w : Nat) (x : Fin n → Bool) :
    signal n (force n C j false) w x=true → signal n (force n C j true) w x=true := by
  apply relate x (force n C j false) (force n C j true) j (fun a b => a=true → b=true) (fun _ h => h)
  · simp
  · intro valid
    have v : j<C.gates.length := by simpa using valid
    rw [pin_eval n C j false v,pin_eval n C j true v]
    simp
  · exact fun k diff => (off_pin n C j true k diff).trans (off_pin n C j false k diff).symm
  · intro k valid _ f g h
    rcases (force_mono n C j false mc _ (gateAt_mem valid)).1 with prod | plus
    · rw [prod]
      simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
      exact fun a u hu => h u hu (a u hu)
    · rw [plus]
      simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
      rintro ⟨u,hu,on⟩
      exact ⟨u,hu,h u hu on⟩

theorem shannon_wire {n : Nat} (C : Circuit) (mc : Monotone2 C) (j w : Nat) (x : Fin n → Bool) :
    signal n C w x = (signal n (force n C j false) w x ||
      (gateVal n C j x && signal n (force n C j true) w x)) := by
  cases atJ : gateVal n C j x with
  | false => simpa using pin_correct C j false x atJ w
  | true =>
    rw [pin_correct C j true x atJ w,Bool.true_and]
    cases low : signal n (force n C j false) w x with
    | false => simp
    | true => simp [pin_monotone C mc j w x low]

theorem shannon_output {n : Nat} (C : Circuit) (mc : Monotone2 C) (j : Nat) (x : Fin n → Bool) :
    circuitFun n C x = (circuitFun n (force n C j false) x ||
      (gateVal n C j x && circuitFun n (force n C j true) x)) :=
  shannon_wire C mc j C.output x

theorem shannon_fun {n : Nat} (C : Circuit) (mc : Monotone2 C) (j : Nat) :
    circuitFun n C = fun x => circuitFun n (force n C j false) x ||
      (gateVal n C j x && circuitFun n (force n C j true) x) := funext (shannon_output C mc j)

end GirthPin

#print axioms GirthPin.shannon_wire
#print axioms GirthPin.shannon_fun
