import PEqualNP.Defs

namespace Petersen3831.RawPartner

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

abbrev Input := Fin 9 → Bool

def graph (x : Input) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
  x 6 && x 8 || x 8 && x 5

def flip (x : Input) (i : Fin 9) := if i=0 then !x 0 else x i

def row (m : Nat) (b : Bool) (i : Fin 9) : Bool := if i=0 then b else m.testBit i.val

def sensitive (m : Nat) : Prop := graph (row m false) ≠ graph (row m true)
instance (m : Nat) : Decidable (sensitive m) := inferInstanceAs (Decidable (_ ≠ _))

private theorem flip_row (m : Nat) (b : Bool) : flip (row m b)=row m (!b) := by
  funext i
  by_cases hi : i=0 <;> simp [flip,row,hi]

private def value (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)
private def step (w : List Bool) (g : Gate) := w ++ [value w g]

/-- Physical value of the partner immediately before instruction k, with x₀ off.
    This definition also assigns the circuit default false to an invalid read. -/
def before (C : Circuit) (k m a : Nat) : Bool :=
  ((C.gates.take k).foldl step (List.ofFn (row m false))).getD a false

private def agree (u v : List Bool) : Prop :=
  u.length=v.length ∧ ∀i, i≠0 → u.getD i false=v.getD i false

private theorem step_agree {u v : List Bool} (same : agree u v) (g : Gate)
    (eq : value u g=value v g) : agree (step u g) (step v g) := by
  obtain ⟨len,read⟩ := same
  refine ⟨by simp [step,len],fun i ne => ?_⟩
  by_cases old : i<u.length
  · have old' : i<v.length := len ▸ old
    simpa [step,List.getD_eq_getElem?_getD,List.getElem?_append_left old,
      List.getElem?_append_left old'] using read i ne
  · unfold step
    rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),eq,len]

private theorem fold_agree (gs : List Gate) {u v : List Bool} (same : agree u v)
    (none : ∀ g∈gs, 0∉g.inputs) : agree (gs.foldl step u) (gs.foldl step v) := by
  induction gs generalizing u v with
  | nil => exact same
  | cons g gs ih =>
    apply ih (step_agree same g ?_) (fun h hm => none h (List.mem_cons_of_mem _ hm))
    unfold value
    apply congrArg g.op.eval
    apply List.map_congr_left
    exact fun i member => same.2 i (fun eq => none g (by simp) (eq ▸ member))

private theorem raw_agree (m : ℕ) : agree (List.ofFn (row m false)) (List.ofFn (row m true)) := by
  refine ⟨by simp,fun i ne => ?_⟩
  by_cases h : i<9
  · have lo (b : Bool) : i<(List.ofFn (row m b)).length := by simpa using h
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (lo _),Option.getD_some,List.getElem_ofFn]
    simp [row,Fin.ext_iff,ne]
  · have off (b : Bool) : (List.ofFn (row m b)).length ≤ i := by simp; omega
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_none (off _)]

private theorem keep_old (gs : List Gate) (w : List Bool) {i : ℕ} (hi : i<w.length) :
    (gs.foldl step w).getD i false=w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih _ (by simp [step]; omega)]
    simp [step,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

private theorem skip {gs : List Gate} (none : (gs.filter fun g => g.inputs.contains 0).length=0) :
    ∀ g∈gs, 0∉g.inputs := by
  intro g member zero
  have hits : g∈gs.filter (fun h => h.inputs.contains 0) := List.mem_filter.mpr ⟨member,List.contains_iff_mem.mpr zero⟩
  rw [List.length_eq_zero_iff.mp none] at hits
  exact List.not_mem_nil hits

def unique (C : Circuit) : Prop := (C.gates.filter fun g => g.inputs.contains 0).length=1

private theorem regions {C : Circuit} {k : ℕ} (hk : k<C.gates.length) (uq : unique C)
    (reads : 0∈(gateAt C k).inputs) :
    C.gates=C.gates.take k ++ gateAt C k::C.gates.drop (k+1) ∧
    (∀ g∈C.gates.take k, 0∉g.inputs) ∧ (∀ g∈C.gates.drop (k+1), 0∉g.inputs) := by
  have atK : gateAt C k=C.gates[k] := by simp [gateAt,List.getD_eq_getElem?_getD,hk]
  have cut : C.gates=C.gates.take k ++ gateAt C k::C.gates.drop (k+1) := by
    rw [atK,←List.drop_eq_getElem_cons hk,List.take_append_drop]
  unfold unique at uq
  have included : (fun g : Gate => g.inputs.contains 0) (gateAt C k) = true := List.contains_iff_mem.mpr reads
  rw [cut,List.filter_append,List.filter_cons_of_pos (p:=fun g : Gate => g.inputs.contains 0) included] at uq
  simp only [List.length_append,List.length_cons] at uq
  exact ⟨cut,skip (by omega),skip (by omega)⟩

theorem reader_index {C : Circuit} {k j : ℕ} (uq : unique C) (hk : k<C.gates.length)
    (readK : 0∈(gateAt C k).inputs) (hj : j<C.gates.length) (readJ : 0∈(gateAt C j).inputs) : j=k := by
  obtain ⟨_,preUnused,postUnused⟩ := regions hk uq readK
  have gate : gateAt C j=C.gates[j] := by simp [gateAt,List.getD_eq_getElem?_getD,hj]
  rw [gate] at readJ
  rcases lt_trichotomy j k with early | eq | late
  · have inside : j<(C.gates.take k).length := by simpa only [List.length_take_of_le hk.le] using early
    have member := List.getElem_mem (l:=C.gates.take k) inside
    simp only [List.getElem_take] at member
    exact (preUnused _ member readJ).elim
  · exact eq
  · have inside : j-(k+1)<(C.gates.drop (k+1)).length := by simp; omega
    have member := List.getElem_mem (l:=C.gates.drop (k+1)) inside
    have found : C.gates[j]∈C.gates.drop (k+1) := by
      simpa only [List.getElem_drop,show k+1+(j-(k+1))=j by omega] using member
    exact (postUnused _ found readJ).elim

/-- If the partner blocks the unique reader, every output other than raw x₀
    agrees between the two runs. All other operations remain unrestricted. -/
theorem masked {C : Circuit} {k a m : ℕ} (uq : unique C) (hk : k<C.gates.length)
    (positive : 0<a) (args : (gateAt C k).inputs=[0,a]) (out : C.output≠0)
    (block : ((gateAt C k).op=.and ∧ before C k m a=false) ∨
      ((gateAt C k).op=.or ∧ before C k m a=true)) :
    circuitFun 9 C (row m false)=circuitFun 9 C (row m true) := by
  obtain ⟨cut,preUnused,postUnused⟩ := regions hk uq (by simp [args])
  let u := (C.gates.take k).foldl step (List.ofFn (row m false))
  let v := (C.gates.take k).foldl step (List.ofFn (row m true))
  have same : agree u v := fold_agree _ (raw_agree m) preUnused
  have partner := same.2 a (by omega)
  have equal : value u (gateAt C k)=value v (gateAt C k) := by
    rcases block with ⟨op,x⟩ | ⟨op,x⟩ <;> change u.getD a false=_ at x <;>
      simp only [value,op,args,List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,
        List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false,←partner,x] <;> simp
  have result := (fold_agree _ (step_agree same (gateAt C k) equal) postUnused).2 C.output out
  change (C.gates.foldl step (List.ofFn (row m false))).getD C.output false =
    (C.gates.foldl step (List.ofFn (row m true))).getD C.output false
  rw [cut,List.foldl_append,List.foldl_cons,List.foldl_append,List.foldl_cons]
  exact result

theorem output_not_zero {C : Circuit} (correct : ∀x : Input,circuitFun 9 C (flip x)=graph x) : C.output≠0 := by
  intro out
  have h := correct (row 0 false)
  rw [flip_row] at h
  change (C.gates.foldl step (List.ofFn (row 0 true))).getD C.output false=graph (row 0 false) at h
  rw [out,keep_old _ _ (by simp)] at h
  exact Bool.noConfusion (show true=false from h)

/-- A correct circuit must pass the toggle at every sensitive mask. This
    statement applies to an internal partner as well as to a raw coordinate. -/
theorem passes {C : Circuit} {k a m : ℕ} (uq : unique C) (hk : k<C.gates.length)
    (positive : 0<a) (args : (gateAt C k).inputs=[0,a]) (s : sensitive m)
    (correct : ∀x : Input,circuitFun 9 C (flip x)=graph x) :
    ((gateAt C k).op=.and → before C k m a=true) ∧ ((gateAt C k).op=.or → before C k m a=false) := by
  have left := correct (row m false)
  have right := correct (row m true)
  rw [flip_row] at left right
  have change : circuitFun 9 C (row m false)≠circuitFun 9 C (row m true) :=
    fun eq => s (left.symm.trans (eq.symm.trans right))
  have no := fun block => change (masked uq hk positive args (output_not_zero correct) block)
  constructor <;> intro op <;> cases v : before C k m a <;> try rfl
  · exact (no (Or.inl ⟨op,v⟩)).elim
  · exact (no (Or.inr ⟨op,v⟩)).elim

private theorem raw_before (C : Circuit) (k m : ℕ) (a : Fin 9) (positive : 0<a.val) :
    before C k m a.val=m.testBit a.val := by
  unfold before
  have bound : a.val<(List.ofFn (row m false)).length := by simp
  rw [keep_old _ _ bound]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem bound,Option.getD_some,List.getElem_ofFn]
  simp [row,Fin.ext_iff,show a.val≠0 by omega]

def masks : List (ℕ × ℕ) := [(0,0),(16,2),(2,20),(2,10),(2,16),(2,32),(2,80),(2,130),(2,258)]

theorem masks_valid : ∀ a : Fin 9, 0<a.val →
    let p := masks.getD a.val (0,0)
    sensitive p.1 ∧ sensitive p.2 ∧ p.1.testBit a.val=false ∧ p.2.testBit a.val=true := by decide +kernel

theorem raw_partner (C : Circuit) (k a : ℕ) (uq : unique C) (hk : k<C.gates.length)
    (positive : 0<a) (raw : a<9) (op : (gateAt C k).op=.and ∨ (gateAt C k).op=.or)
    (args : (gateAt C k).inputs=[0,a]) : ∃x : Input, circuitFun 9 C (flip x)≠graph x := by
  by_contra! correct
  let i : Fin 9 := ⟨a,raw⟩
  let p := masks.getD a (0,0)
  obtain ⟨lo,hi,l,r⟩ := masks_valid i positive
  rcases op with op | op
  · have hit := (passes uq hk positive args lo correct).1 op
    rw [raw_before C k p.1 i positive] at hit
    exact Bool.noConfusion (l.symm.trans hit)
  · have hit := (passes uq hk positive args hi correct).2 op
    rw [raw_before C k p.2 i positive] at hit
    exact Bool.noConfusion (r.symm.trans hit)

def encode (x : Input) : ℕ := (BitVec.ofBoolListLE (List.ofFn x)).toNat

theorem row_encode (x : Input) : row (encode x) (x 0)=x := by
  funext i
  by_cases zero : i=0
  · simp [row,zero]
  · simp only [row,ite_eq_right zero]
    change (BitVec.ofBoolListLE (List.ofFn x)).getLsbD i.val=x i
    rw [BitVec.getLsbD_ofBoolListLE]
    have bound : i.val<(List.ofFn x).length := by simp
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem bound,Option.getD_some,List.getElem_ofFn]

def prefixWire (C : Circuit) (k : ℕ) (x : Input) (a : ℕ) :=
  ((C.gates.take k).foldl step (List.ofFn x)).getD a false

/-- Before the unique reader, any wire other than raw 0 is independent of x₀. -/
theorem prefix_as_before {C : Circuit} {k a : ℕ} (uq : unique C) (hk : k<C.gates.length)
    (read : 0∈(gateAt C k).inputs) (positive : 0<a) (x : Input) :
    prefixWire C k x a=before C k (encode x) a := by
  have restore := row_encode x
  have preUnused := (regions hk uq read).2.1
  conv_lhs => rw [←restore]
  cases x 0
  · rfl
  · exact ((fold_agree _ (raw_agree (encode x)) preUnused).2 a (by omega)).symm

end Petersen3831.RawPartner

#print axioms Petersen3831.RawPartner.masked
#print axioms Petersen3831.RawPartner.passes
#print axioms Petersen3831.RawPartner.raw_partner
