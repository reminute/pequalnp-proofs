import RawPartner

namespace Petersen3831.ErasePartner

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CircuitMoves RawPartner

private def value (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)
private def step (w : List Bool) (g : Gate) := w ++ [value w g]

private theorem fold_length (gs : List Gate) (x : List Bool) : (gs.foldl step x).length=x.length+gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons,ih]; simp [step]; omega

private def redirect (r i : ℕ) := if i=r then 0 else if r < i then i-1 else i
private def rename (r : ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map (redirect r)⟩

private def aligned (r : ℕ) (original short : List Bool) : Prop :=
  r≤short.length ∧ original.length=short.length+1 ∧
    ∀ i, original.getD i false=short.getD (redirect r i) false

private theorem initial (w : List Bool) (z : Bool) (copied : z=w.getD 0 false) :
    aligned w.length (w++[z]) w := by
  refine ⟨le_rfl,by simp,fun i => ?_⟩
  rcases lt_trichotomy i w.length with low | rfl | high
  · simp [redirect,low.ne,show ¬w.length < i by omega,List.getD_eq_getElem?_getD,List.getElem?_append_left low]
  · simpa [redirect,List.getD_eq_getElem?_getD] using copied
  · have outside' : w.length ≤ i-1 := by omega
    simp [redirect,high,high.ne',List.getD_eq_getElem?_getD,List.getElem?_eq_none outside']

private theorem extend {r : ℕ} (pos : 0<r) {original short : List Bool} (agree : aligned r original short) (g : Gate) :
    aligned r (step original g) (step short (rename r g)) := by
  obtain ⟨earlier,len,wire⟩ := agree
  have gate : value original g=value short (rename r g) := by
    simp only [value,rename,List.map_map]
    apply congrArg g.op.eval
    exact List.map_congr_left (fun i _ => wire i)
  refine ⟨by simp [step]; omega,by simp [step,len],fun i => ?_⟩
  by_cases valid : i<original.length
  · have below : redirect r i<short.length := by unfold redirect; split_ifs <;> omega
    simpa [step,List.getD_eq_getElem?_getD,List.getElem?_append_left valid,List.getElem?_append_left below] using wire i
  · have above : r < i := by omega
    have renamed : redirect r i=i-1 := by simp [redirect,above.ne',above]
    simp only [step,renamed,gate]
    rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega)]
    exact congrArg (fun j => [value short (rename r g)].getD j false) (by omega)

private theorem fold_aligned {r : ℕ} (pos : 0<r) (rest : List Gate) {original short : List Bool}
    (agree : aligned r original short) : aligned r (rest.foldl step original) ((rest.map (rename r)).foldl step short) := by
  induction rest generalizing original short with
  | nil => exact agree
  | cons g gs ih => exact ih (extend pos agree g)

private theorem cut {C : Circuit} {k : ℕ} (hk : k<C.gates.length) :
    C.gates=C.gates.take k ++ gateAt C k::C.gates.drop (k+1) := by
  have atK : gateAt C k=C.gates[k] := by simp [gateAt,List.getD_eq_getElem?_getD,hk]
  rw [atK,←List.drop_eq_getElem_cons hk,List.take_append_drop]

/-- Redirect a gate that copies input zero, removing it without assumptions on
    downstream operations or on the validity of downstream wire operands. -/
theorem erase_copy {C : Circuit} {k : ℕ} (hk : k<C.gates.length) (x : Input)
    (copies : (gateAt C k).op.eval ((gateAt C k).inputs.map (prefixWire C k x))=prefixWire C k x 0) :
    circuitFun 9 (eraseGate 9 C k 0) x=circuitFun 9 C x := by
  let w := (C.gates.take k).foldl step (List.ofFn x)
  have len : w.length=9+k := by simp [w,fold_length,List.length_take_of_le hk.le]
  have init := initial w (value w (gateAt C k)) copies
  rw [len] at init
  have matched := (fold_aligned (by omega) (C.gates.drop (k+1)) init).2.2 C.output
  change (((eraseGate 9 C k 0).gates.foldl step (List.ofFn x)).getD (eraseGate 9 C k 0).output false)=
    (C.gates.foldl step (List.ofFn x)).getD C.output false
  conv_rhs => rw [cut hk,List.foldl_append,List.foldl_cons]
  simp only [eraseGate,ite_eq_left hk,List.foldl_append]
  exact matched.symm

theorem erase_size {C : Circuit} {k : ℕ} (hk : k<C.gates.length) : (eraseGate 9 C k 0).size+1=C.size := by
  simp [Circuit.size,eraseGate,hk,List.length_take_of_le hk.le]
  omega

theorem erase_fanin {C : Circuit} {k : ℕ} (hk : k<C.gates.length) (fan : FanInTwo C) : FanInTwo (eraseGate 9 C k 0) := by
  intro g member
  simp only [eraseGate,ite_eq_left hk,List.mem_append,List.mem_map] at member
  rcases member with pre | ⟨old,post,rfl⟩
  · exact fan _ (List.mem_of_mem_take pre)
  · simpa only [List.length_map] using fan old (List.mem_of_mem_drop post)

/-- Constancy is required only for the prefix run in which x₀ is false. The
    unique-reader property transfers it to both choices of x₀. -/
theorem erase_enabled {C : Circuit} {k a : ℕ} (fan : FanInTwo C) (uq : unique C)
    (hk : k<C.gates.length) (positive : 0<a) (args : (gateAt C k).inputs=[0,a])
    (mode : ((gateAt C k).op=.and ∧ ∀ m, before C k m a=true) ∨
      ((gateAt C k).op=.or ∧ ∀ m, before C k m a=false)) :
    let D := eraseGate 9 C k 0
    D.size+1=C.size ∧ FanInTwo D ∧ ∀ x : Input, circuitFun 9 D x=circuitFun 9 C x := by
  refine ⟨erase_size hk,erase_fanin hk fan,fun x => erase_copy hk x ?_⟩
  have bit := prefix_as_before uq hk (by simp [args]) positive x
  rcases mode with ⟨op,constant⟩ | ⟨op,constant⟩ <;>
    simp only [args,List.map_cons,List.map_nil,op,GateOp.eval,List.all_cons,List.all_nil,List.any_cons,List.any_nil,
      id_eq,bit,constant,Bool.or_false,Bool.and_true]

end Petersen3831.ErasePartner

#print axioms Petersen3831.ErasePartner.erase_enabled
