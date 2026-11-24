import Cofactor

namespace Petersen3831.Cofactor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_2305 RawPartner

def consumers (j : Nat) (gs : List Gate) : Nat :=
  (gs.filter (fun g => g.inputs.contains j)).length

private theorem charge (gs : List Gate) (j : Nat) (b : Bool)
    (valid : ∀ g ∈ gs, NOk g) (a : List Stat × List Gate) (fixed : ConstAt a j b) :
    (elim 8 gs a).2.length + consumers j gs ≤ a.2.length + gs.length := by
  induction gs generalizing a with
  | nil => simp [elim, consumers]
  | cons g gs ih =>
    have next := ih (fun g' mem => valid g' (List.mem_cons_of_mem _ mem))
      (elimStep 8 a g) (const_step 8 a g j b fixed)
    change (elim 8 gs (elimStep 8 a g)).2.length + consumers j (g :: gs) ≤ _
    cases hit : g.inputs.contains j
    · have step := step_len_le 8 a g
      simp only [consumers, List.filter_cons, hit, Bool.false_eq_true, ↓reduceIte, List.length_cons] at next ⊢
      omega
    · have step := step_len_const 8 a g (valid g (by simp)) j b fixed
        (List.contains_iff_mem.mp hit)
      simp only [consumers, List.filter_cons, hit, ↓reduceIte, List.length_cons] at next ⊢
      omega

private theorem normalized (C : Circuit) (fan : FanInTwo C) (gs : List Gate)
    (members : ∀ g ∈ gs, g ∈ C.gates) : ∀ h ∈ gs.map normGate, NOk h := by
  intro h mem
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp mem
  exact normGate_nok _ (fan _ (members _ hg))

/-- Every normalized direct user of the pinned primary input costs a gate. -/
theorem pin_consumers (C : Circuit) (fan : FanInTwo C)
    (spec : ∀ x : Input, circuitFun 9 C (RawPartner.flip x) = graph x) :
    12 + consumers 0 (C.gates.map normGate) ≤ C.size := by
  have fixed : ConstAt (start true) 0 true := by simp [ConstAt,start]
  have h := charge _ 0 true (normalized C fan C.gates (fun _ m => m)) (start true) fixed
  have lo := (size_window C fan spec).1
  change 12 ≤ (elim 8 (C.gates.map normGate) (start true)).2.length at lo
  rw [show (start true).2.length = 0 from rfl,Nat.zero_add,List.length_map] at h
  change 12 + _ ≤ C.gates.length
  omega

/-- A reader whose operand zero is the pinned true input and whose operation is OR
    produces a constant. Each normalized later reader of that constant also vanishes. -/
theorem or_consumers {C : Circuit} {k : Nat} (fan : FanInTwo C)
    (spec : ∀ x : Input, circuitFun 9 C (RawPartner.flip x) = graph x)
    (hk : k < C.gates.length) (op : (gateAt C k).op = .or)
    (raw : 0 ∈ (gateAt C k).inputs) :
    13 + consumers (9+k) ((C.gates.drop (k+1)).map normGate) ≤ C.size := by
  let pre := C.gates.take k
  let post := C.gates.drop (k+1)
  let g := gateAt C k
  have atK : g = C.gates[k] := by simp [g,gateAt,List.getD_eq_getElem?_getD,hk]
  have cut : C.gates=pre ++ g :: post := by
    dsimp [pre,post]
    rw [atK,← List.drop_eq_getElem_cons hk,List.take_append_drop]
  have preLength : pre.length=k := List.length_take_of_le hk.le
  have ng : normGate g = g := by
    have eq : g.op=.or := op
    simp [normGate,eq]
  have gm : g∈C.gates := by rw [cut]; simp
  have gn : NOk g := ng ▸ normGate_nok g (fan g gm)
  have postOK := normalized C fan post (fun _ mem => List.mem_of_mem_drop mem)
  let a := elim 8 (pre.map normGate) (start true)
  let mid := elimStep 8 a g
  have fixed : ConstAt a 0 true := elim_const 8 _ 0 true _ (by simp [ConstAt,start])
  have alen : a.1.length=9+k := by
    rw [show a = elim 8 (pre.map normGate) (start true) from rfl,elim_status_length]
    simp [start,preLength]
  have one : mid.2.length=a.2.length := step_len_const 8 a g gn 0 true fixed raw
  have result : ConstAt mid (9+k) true := by
    rw [← alen]
    refine ⟨by simp [mid,elimStep], ?_⟩
    change (a.1 ++ [_]).getD a.1.length (Sum.inl false) = _
    rw [getD_snoc_eq, show g.op=GateOp.or from op]
    exact force_or _ _ (by simpa using gn.1.2) (List.mem_map.mpr ⟨0, raw, fixed.2⟩)
  have endState : compiled C true=elim 8 (post.map normGate) mid := by
    simp only [compiled,cut,List.map_append,List.map_cons,ng,elim,List.foldl_append,List.foldl_cons]
    rfl
  have later := charge (post.map normGate) (9+k) true postOK mid result
  have early : a.2.length ≤ pre.length := by
    simpa [a,start] using (elim_len 8 (pre.map normGate) (start true))
  have lower := (size_window C fan spec).1
  rw [endState] at lower
  rw [one,List.length_map] at later
  have total : C.size=pre.length+post.length+1 := by simp [Circuit.size,cut]; omega
  change 13 + consumers (9+k) (post.map normGate) ≤ C.size
  omega

theorem after_erasure {C : Circuit} {k a : ℕ} (fan : FanInTwo C) (uq : unique C)
    (hk : k<C.gates.length) (positive : 0<a) (args : (gateAt C k).inputs=[0,a])
    (mode : ((gateAt C k).op=.and ∧ ∀ m, before C k m a=true) ∨
      ((gateAt C k).op=.or ∧ ∀ m, before C k m a=false))
    (size : C.size ≤ 14) (spec : ∀ x : Input, circuitFun 9 C (RawPartner.flip x) = graph x) :
    let D := PEqualNP.CircuitMoves.eraseGate 9 C k 0
    12 ≤ (compiled D true).2.length ∧ D.size - (compiled D true).2.length ≤ 1 ∧
      consumers 0 (D.gates.map normGate) ≤ 1 := by
  let D := PEqualNP.CircuitMoves.eraseGate 9 C k 0
  obtain ⟨sz, fd, eq⟩ := ErasePartner.erase_enabled fan uq hk positive args mode
  have sd (x : Input) : circuitFun 9 D (RawPartner.flip x) = graph x :=
    (eq _).trans (spec x)
  have lo := (size_window D fd sd).1
  have bound := pin_consumers D fd sd
  change D.size+1=C.size at sz
  change 12 ≤ (compiled D true).2.length ∧ D.size - (compiled D true).2.length ≤ 1 ∧
    consumers 0 (D.gates.map normGate) ≤ 1
  exact ⟨lo,by omega,by omega⟩

end Petersen3831.Cofactor

#print axioms Petersen3831.Cofactor.survivors
#print axioms Petersen3831.Cofactor.or_consumers
#print axioms Petersen3831.Cofactor.after_erasure
