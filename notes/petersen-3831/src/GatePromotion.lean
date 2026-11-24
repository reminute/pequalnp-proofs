import InternalPartner

namespace Petersen3831.Promotion

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open RawPartner

private def val (u : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => u.getD i false)
private def step (u : List Bool) (g : Gate) := u ++ [val u g]
private def rename (f : Nat → Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map f⟩

private theorem fold_len (gs : List Gate) (u : List Bool) : (gs.foldl step u).length=u.length+gs.length := by
  induction gs generalizing u with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons,ih,step]; omega

private theorem retained (gs : List Gate) (u : List Bool) {i : Nat} (h : i<u.length) :
    (gs.foldl step u).getD i false=u.getD i false := by
  induction gs generalizing u with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih (step u g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ h

/-- While traversing a list of original gates, ready wires agree through f and
    unavailable wires are translated by the current displacement. -/
private def matched (f : Nat → Nat) (d : Nat) (u v : List Bool) : Prop :=
  v.length=u.length+d ∧ (∀ i, i<u.length → f i<v.length) ∧
  (∀ i, u.length ≤ i → f i=i+d) ∧ ∀ i, u.getD i false=v.getD (f i) false

private theorem fold_matched (f : Nat → Nat) (d : Nat) (gs : List Gate) {u v : List Bool}
    (h : matched f d u v) : matched f d (gs.foldl step u) ((gs.map (rename f)).foldl step v) := by
  induction gs generalizing u v with
  | nil => exact h
  | cons g gs ih =>
    obtain ⟨len,small,big,eq⟩ := h
    have node : val u g=val v (rename f g) := by
      apply congrArg g.op.eval
      simp only [rename,List.map_map]
      exact List.map_congr_left (fun w _ => eq w)
    apply ih
    refine ⟨by simp [step,len]; omega,?_,?_,?_⟩
    · intro i hi
      simp only [step,List.length_append,List.length_singleton] at hi ⊢
      by_cases old : i<u.length
      · exact Nat.lt_succ_of_lt (small i old)
      · rw [big i (by omega)]; omega
    · intro i hi
      apply big
      simp [step] at hi
      omega
    · intro i
      by_cases old : i<u.length
      · simpa only [step,List.getD_append _ _ _ _ old,List.getD_append _ _ _ _ (small i old)] using eq i
      · rw [big i (by omega)]
        simp only [step,List.getD_append_right u _ _ i (by omega),
          List.getD_append_right v _ _ (i+d) (by omega),node,len]
        rw [show i+d-(u.length+d)=i-u.length by omega]

private def up (i : Nat) : Nat := if i=0 then 10 else if i<9 then i else i+2
private def down (a i : Nat) : Nat := if i=a then 9 else if a < i then i+1 else up i
private def seed (x : Input) (i j : Fin 9) := List.ofFn x ++ [x i && x j,!x 0]

private theorem start (x : Input) (i j : Fin 9) :
    matched up 2 (List.ofFn (flip x)) (seed x i j) := by
  refine ⟨by simp [seed],?_,?_,?_⟩
  · intro a ha
    simp [up,seed] at *
    split_ifs <;> omega
  · intro a ha
    simp only [List.length_ofFn] at ha
    simp [up,show a≠0 by omega,show ¬a<9 by omega]
  · intro a
    by_cases zero : a=0
    · subst a
      rfl
    by_cases raw : a<9
    · interval_cases a <;> rfl
    · have far : (seed x i j).length ≤ a+2 := by simp [seed]; omega
      simp [up,zero,raw,List.getD_eq_getElem?_getD,List.getElem?_eq_none far]

private theorem remove (u v : List Bool) (z : Bool) (h : matched up 2 u v)
    (enough : 9≤u.length) (copies : v.getD 9 false=z) :
    matched (down u.length) 1 (u++[z]) v := by
  obtain ⟨len,small,_,eq⟩ := h
  refine ⟨by simp; omega,?_,?_,?_⟩
  · intro i hi
    simp at hi
    rcases lt_or_ge i u.length with old | new
    · simpa [down,old.ne,not_lt.mpr old.le] using small i old
    · have same : i=u.length := by omega
      simp [down,same,len]; omega
  · intro i hi
    simp at hi
    have high : u.length < i := by omega
    simp [down,high,high.ne']
  · intro i
    rcases lt_trichotomy i u.length with old | rfl | later
    · simpa only [List.getD_append _ _ _ _ old,down,ite_eq_right old.ne,
        ite_eq_right (not_lt.mpr old.le)] using eq i
    · simpa [down,List.getD_append_right] using copies.symm
    · have bad' : v.length ≤ i+1 := by omega
      simp [down,later.ne',later,List.getD_eq_getElem?_getD,List.getElem?_eq_none bad']

private theorem program (C : Circuit) {p : Nat} (valid : p<C.gates.length) :
    C.gates = C.gates.take p ++ gateAt C p :: C.gates.drop (p+1) := by
  have atp : gateAt C p=C.gates[p] := by simp [gateAt,List.getD_eq_getElem?_getD,valid]
  rw [atp,←List.drop_eq_getElem_cons valid,List.take_append_drop]

private theorem rawValue (x : Input) (i : Fin 9) : (List.ofFn x).getD i.val false=x i := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some]

private theorem first_value (x : Input) (i j : Fin 9) :
    val (List.ofFn x) ⟨.and,[i.val,j.val]⟩ = (x i && x j) := by
  simp only [val,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id_eq,
    Bool.and_true,rawValue]

private theorem special (x : Input) (i j : Fin 9) :
    step (step (List.ofFn x) ⟨.and,[i.val,j.val]⟩) ⟨.not,[0]⟩ = seed x i j := by
  simp only [step,first_value]
  rfl

/-- Recompute an existing raw conjunction as gate 0 and introduce the required
    input negation as gate 1. Deleting the old conjunction increases size by one
    overall. The two index maps preserve forward and out-of-range reads. -/
theorem promote (C : Circuit) (fan : FanInTwo C) (i j : Fin 9) (p : Nat) (valid : p<C.gates.length)
    (edge : ∀ x : Input, val ((C.gates.take p).foldl step (List.ofFn (flip x))) (gateAt C p)=
      (x i && x j)) :
    ∃ D : Circuit, FanInTwo D ∧ D.size=C.size+1 ∧
      (∀x : Input, (D.wires (List.ofFn x)).getD 9 false=(x i && x j)) ∧
      ∀x : Input, circuitFun 9 D x=circuitFun 9 C (flip x) := by
  let t := 9+p
  let pre := C.gates.take p
  let post := C.gates.drop (p+1)
  let g : Gate := ⟨.and,[i.val,j.val]⟩
  let h : Gate := ⟨.not,[0]⟩
  let rest := (pre.map (rename up)) ++ (post.map (rename (down t)))
  let D : Circuit := ⟨g :: h :: rest,down t C.output⟩
  refine ⟨D,?_,?_,?_,?_⟩
  · intro a member
    simp only [D,rest,List.mem_cons,List.mem_append,List.mem_map] at member
    rcases member with rfl | rfl | ⟨old,mem,rfl⟩ | ⟨old,mem,rfl⟩
    · exact ⟨by simp [g],by simp [g]⟩
    · exact ⟨by simp [h],by decide⟩
    · simpa [rename] using fan old (List.mem_of_mem_take mem)
    · simpa [rename] using fan old (List.mem_of_mem_drop mem)
  · simp [D,Circuit.size,rest,pre,post]
    omega
  · intro x
    change ((h::rest).foldl step (step (List.ofFn x) g)).getD 9 false=_
    rw [retained _ _ (by simp [g,step])]
    simp only [step,g,first_value]
    rfl
  · intro x
    let u := pre.foldl step (List.ofFn (flip x))
    let v := (pre.map (rename up)).foldl step (seed x i j)
    have um : u.length=t := by simp [u,t,pre,fold_len,List.length_take_of_le valid.le]
    have vm : v.getD 9 false=(x i && x j) := by
      rw [show v.getD 9 false=(seed x i j).getD 9 false from retained _ _ (by simp [seed])]
      rfl
    have start' : matched up 2 u v := fold_matched up 2 pre (start x i j)
    have removed := remove u v (val u (gateAt C p)) start' (by rw [um]; omega) (vm.trans (edge x).symm)
    rw [um] at removed
    have finish := (fold_matched _ _ post removed).2.2.2 C.output
    change ((g::h::rest).foldl step (List.ofFn x)).getD (down t C.output) false =
      (C.gates.foldl step (List.ofFn (flip x))).getD C.output false
    conv_rhs => rw [program C valid,List.foldl_append,List.foldl_cons]
    simp only [List.foldl_cons,rest,List.foldl_append]
    rw [show step (step (List.ofFn x) g) h=seed x i j from special x i j]
    exact finish.symm

private theorem value_before_later (C : Circuit) (x : Input) {p k : Nat}
    (early : p<k) (valid : k<C.gates.length) :
    prefixWire C k x (9+p) = val ((C.gates.take p).foldl step (List.ofFn x)) (gateAt C p) := by
  let w := (C.gates.take p).foldl step (List.ofFn x)
  have hp : p<C.gates.length := by omega
  have len : w.length=9+p := by simp [w,fold_len,List.length_take_of_le hp.le]
  have split : C.gates.take k = C.gates.take p ++ [gateAt C p] ++ (C.gates.drop (p+1)).take (k-(p+1)) := by
    calc
      _ = C.gates.take (p+1) ++ (C.gates.drop (p+1)).take (k-(p+1)) := by
        rw [← List.take_add,show p+1+(k-(p+1))=k by omega]
      _ = _ := by rw [List.take_succ_eq_append_getElem hp]; simp [gateAt,List.getD_eq_getElem?_getD,hp]
  change ((C.gates.take k).foldl step (List.ofFn x)).getD (9+p) false=_
  rw [split,List.foldl_append,List.foldl_append]
  change ((_ : List Gate).foldl step (step w (gateAt C p))).getD (9+p) false=val w (gateAt C p)
  rw [retained _ _ (by simp [step,len])]
  simp only [step,List.getD_append_right w _ false (9+p) (by omega),len,Nat.sub_self]
  rfl

private theorem encoded_bit (x : Input) (i : Fin 8) :
    Partner.bit (encode x) i=x i.succ := by
  have h := congrFun (row_encode x) i.succ
  simpa [row,Partner.bit] using h

/-- A nonconstant OR partner determined by two raw variables yields an actual
    circuit computing the original graph with the corresponding AND as gate 0. -/
theorem or_partner_promoted {C : Circuit} {k a : Nat} (fan : FanInTwo C)
    (uq : unique C) (hk : k<C.gates.length) (internal : 9≤a) (earlier : a<9+k)
    (op : (gateAt C k).op=.or) (args : (gateAt C k).inputs=[0,a])
    (correct : ∀x : Input,circuitFun 9 C (RawPartner.flip x)=graph x)
    (i j : Fin 8) (different : i ≠ j) (t : Bool → Bool → Bool)
    (rep : ∀ m, before C k m a = t (Partner.bit m i) (Partner.bit m j))
    (nonconstant : ¬∀ m, before C k m a = false) :
    Partner.adjacent i j=true ∧ ∃ D : Circuit, FanInTwo D ∧ D.size=C.size+1 ∧
      (∀x : Input,(D.wires (List.ofFn x)).getD 9 false=(x i.succ && x j.succ)) ∧
      ∀x : Input,circuitFun 9 D x=graph x := by
  obtain const | ⟨adj,table⟩ := Partner.circuit_two_coordinates uq hk (by omega) args correct false op i j different t rep
  · exact (nonconstant const).elim
  let p := a-9
  have pa : 9+p=a := by dsimp [p]; omega
  have pk : p<k := by omega
  obtain ⟨D,fd,sz,first,eval⟩ := promote C fan i.succ j.succ p (by omega) (fun x => by
    rw [← value_before_later C (RawPartner.flip x) pk hk,pa,prefix_as_before uq hk (by simp [args]) (by omega),table]
    simp [encoded_bit,RawPartner.flip])
  exact ⟨adj,D,fd,sz,first,fun x => (eval x).trans (correct x)⟩

/-- Two prefix gates turn a nine-input tail into a raw-AND-first circuit on the
    original inputs, optionally leaving the new AND unused. -/
theorem pad_first (C : Circuit) (fan : FanInTwo C) (i j : Fin 9) :
    ∃ D : Circuit, FanInTwo D ∧ D.size=C.size+2 ∧
      (∀x : Input,(D.wires (List.ofFn x)).getD 9 false=(x i && x j)) ∧
      ∀x : Input,circuitFun 9 D x=circuitFun 9 C (RawPartner.flip x) := by
  let g : Gate := ⟨.and,[i.val,j.val]⟩
  let h : Gate := ⟨.not,[0]⟩
  let rest := C.gates.map (rename up)
  let D : Circuit := ⟨g::h::rest,up C.output⟩
  refine ⟨D,?_,?_,?_,?_⟩
  · intro a member
    simp only [D,rest,List.mem_cons,List.mem_map] at member
    rcases member with rfl | rfl | ⟨old,hem,rfl⟩
    · exact ⟨by simp [g],by simp [g]⟩
    · exact ⟨by simp [h],by decide⟩
    · simpa [rename] using fan old hem
  · simp [D,rest,Circuit.size]
  · intro x
    change ((h::rest).foldl step (step (List.ofFn x) g)).getD 9 false=_
    rw [retained _ _ (by simp [g,step])]
    simp only [step,g,first_value]
    rfl
  · intro x
    change ((g::h::rest).foldl step (List.ofFn x)).getD (up C.output) false=_
    rw [List.foldl_cons,List.foldl_cons,show step (step (List.ofFn x) g) h=seed x i j from special x i j]
    exact ((fold_matched up 2 C.gates (start x i j)).2.2.2 C.output).symm

end Petersen3831.Promotion

#print axioms Petersen3831.Promotion.or_partner_promoted
#print axioms Petersen3831.Promotion.pad_first
