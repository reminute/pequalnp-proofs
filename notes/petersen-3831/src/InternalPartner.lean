import Mathlib.Tactic
import SensitiveRows
import RawPartner

namespace Petersen3831.Partner

/-- Local coordinate 0 means original vertex 1, and local coordinate 7 means vertex 8. -/
def bit (m : Nat) (i : Fin 8) : Bool := m.testBit (i.val+1)

def adjacent (i j : Fin 8) : Bool :=
  edges.contains ((1 <<< (i.val+1)) ||| (1 <<< (j.val+1)))

private def rows : List Nat :=
  [2,10,16,18,20,32,34,36,40,42,48,50,52,80,84,96,100,104,112,116,130,
    138,144,146,208,258,272,274,276,386,400,402]

set_option maxRecDepth 8000 in
private theorem rows_ok : ∀ m ∈ rows, sensitive m = true := by decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
/-- On an edge the only missing projection is 11. On a nonedge all four projections occur. -/
theorem projections :
    ∀ (i j : Fin 8), i ≠ j → ∀ (a b : Bool),
      rows.any (fun m => bit m i == a && bit m j == b) = (!(a && b) || !adjacent i j) := by
  decide

/-- A signal depending on at most one raw coordinate is constant if it has its
    gate's enabling value on every sensitive row. -/
theorem unary_constant (f : Nat → Bool) (v : Bool)
    (enabled : ∀ m, sensitive m = true → f m = v) (i : Fin 8) (t : Bool → Bool)
    (rep : ∀ m, f m = t (bit m i)) : ∀ m, f m = v := by
  obtain ⟨w,_,index,lo,hi,off,on⟩ := both_values i
  have a := enabled _ lo
  have b := enabled _ hi
  rw [rep,bit,← index,off] at a
  rw [rep,bit,← index,on] at b
  intro m
  rw [rep]
  cases bit m i <;> assumption

/-- If a nonconstant partner has only two raw coordinates, they form a residual
    edge. The only exceptional value of its truth table is the input 11. -/
private theorem two_samples (f : Nat → Bool) (v : Bool)
    (enabled : ∀ m ∈ rows, f m = v) (i j : Fin 8) (different : i ≠ j)
    (t : Bool → Bool → Bool) (rep : ∀ m, f m = t (bit m i) (bit m j)) :
    (∀ m, f m = v) ∨
      adjacent i j = true ∧ ∀ m, f m = (if bit m i && bit m j then !v else v) := by
  have seen (a b : Bool) (h : (!(a && b) || !adjacent i j) = true) : t a b = v := by
    obtain ⟨m,mem,yes⟩ := List.any_eq_true.mp ((projections i j different a b).trans h)
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp yes
    have eq := enabled m mem
    simpa only [rep,eq_of_beq ha,eq_of_beq hb] using eq
  have a := seen false false rfl
  have b := seen false true rfl
  have c := seen true false rfl
  by_cases d : t true true = v
  · left
    intro m
    rw [rep]
    cases bit m i <;> cases bit m j <;> assumption
  · have adj : adjacent i j = true := by
      cases e : adjacent i j with
      | true => rfl
      | false => exact (d (seen true true (by simp [e]))).elim
    have exceptional : t true true = !v := by cases eq : t true true <;> cases v <;> simp_all
    refine Or.inr ⟨adj,?_⟩
    intro m
    rw [rep]
    cases bit m i <;> cases bit m j <;> assumption

theorem two_coordinates (f : Nat → Bool) (v : Bool)
    (enabled : ∀ m, sensitive m = true → f m = v) (i j : Fin 8) (different : i ≠ j)
    (t : Bool → Bool → Bool) (rep : ∀ m, f m = t (bit m i) (bit m j)) :
    (∀ m, f m = v) ∨
      adjacent i j = true ∧ ∀ m, f m = (if bit m i && bit m j then !v else v) :=
  two_samples f v (fun m hm => enabled m (rows_ok m hm)) i j different t rep

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private theorem correct_rows : ∀ m ∈ rows, RawPartner.sensitive m := by decide

/-- For the actual physical partner just before the unique gate, two coordinates
    force either the enabling constant or an edge AND (OR reader) / NAND (AND reader). -/
theorem circuit_two_coordinates {C : Circuit} {k a : Nat} (uq : RawPartner.unique C)
    (hk : k < C.gates.length) (positive : 0 < a) (args : (gateAt C k).inputs = [0,a])
    (correct : ∀x : RawPartner.Input, circuitFun 9 C (RawPartner.flip x) = RawPartner.graph x)
    (v : Bool) (op : (gateAt C k).op = if v then .and else .or)
    (i j : Fin 8) (different : i ≠ j) (t : Bool → Bool → Bool)
    (rep : ∀ m, RawPartner.before C k m a = t (bit m i) (bit m j)) :
    (∀ m, RawPartner.before C k m a = v) ∨
      adjacent i j = true ∧ ∀ m, RawPartner.before C k m a = (if bit m i && bit m j then !v else v) := by
  apply two_samples _ v _ i j different t rep
  intro m mem
  have hit := RawPartner.passes uq hk positive args (correct_rows _ mem) correct
  cases v with
  | true => exact hit.1 op
  | false => exact hit.2 op

/-- Inclusion of the eight raw vertices other than 0. -/
def extendsMask (m n : Nat) : Prop := ∀ i : Fin 8, bit m i=true → bit n i=true
instance (m n : Nat) : Decidable (extendsMask m n) := inferInstanceAs (Decidable (∀ _ : Fin 8, _))

private def neighborsOn (m : Nat) : Bool := m.testBit 1 || m.testBit 4 || m.testBit 5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
/-- Mask 200 is the unique independent set that is contained in no sensitive row. -/
private theorem extremal_masks :
    (∀ m : Fin 256, target (2*m.val)=false → 2*m.val=200 ∨ ∃ s ∈ rows, extendsMask (2*m.val) s) ∧
    (∀ m : Fin 256, neighborsOn (2*m.val)=true → ∃ s ∈ rows, extendsMask s (2*m.val)) ∧
    target 200=false ∧ ∀ s ∈ rows, ¬extendsMask 200 s := by decide

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def ordered (u v : List Bool) : Prop := u.length=v.length ∧
  ∀ i, u.getD i false=true → v.getD i false=true

private theorem ordered_step {u v : List Bool} (uv : ordered u v) (g : Gate)
    (pos : g.op=.and ∨ g.op=.or) : ordered (step u g) (step v g) := by
  obtain ⟨len,reads⟩ := uv
  have gate : g.op.eval (g.inputs.map fun i => u.getD i false)=true →
      g.op.eval (g.inputs.map fun i => v.getD i false)=true := by
    rcases pos with h | h
    · simp only [h,GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
      exact fun on i hi => reads i (on i hi)
    · simp only [h,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
      rintro ⟨i,hi,on⟩
      exact ⟨i,hi,reads i on⟩
  refine ⟨by simp [step,len],fun i => ?_⟩
  by_cases early : i<u.length
  · have earlier : i<v.length := len ▸ early
    simpa only [step,List.getD_append _ _ _ _ early,List.getD_append _ _ _ _ earlier] using reads i
  · simp only [step,List.getD_append_right _ _ _ i (Nat.le_of_not_lt early),
      List.getD_append_right _ _ _ i (show v.length ≤ i by omega),len]
    by_cases eq : i=v.length
    · simpa [eq,List.getD_eq_getElem?_getD] using gate
    · have large : 1 ≤ i-v.length := by omega
      rcases hnum : i-v.length with _|d
      · omega
      · simp [List.getD_eq_getElem?_getD]

private theorem ordered_fold (gs : List Gate) (pos : ∀ g ∈ gs, g.op=.and ∨ g.op=.or)
    {u v : List Bool} (uv : ordered u v) : ordered (gs.foldl step u) (gs.foldl step v) := by
  induction gs generalizing u v with
  | nil => exact uv
  | cons g gs ih =>
    exact ih (fun t ht => pos t (List.mem_cons_of_mem _ ht)) (ordered_step uv g (pos g List.mem_cons_self))

theorem before_monotone {C : Circuit} {k a : Nat}
    (pos : ∀ g ∈ C.gates.take k, g.op=.and ∨ g.op=.or) {m n : Nat} (incl : extendsMask m n) :
    RawPartner.before C k m a=true → RawPartner.before C k n a=true := by
  apply (ordered_fold (C.gates.take k) pos (u:=List.ofFn (RawPartner.row m false))
    (v:=List.ofFn (RawPartner.row n false)) ?_).2 a
  refine ⟨by simp,fun i => ?_⟩
  by_cases h : i<9
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left h,Option.getD_some,
      RawPartner.row,Fin.ext_iff]
    by_cases zero : i=0
    · simp [zero]
    · have ip : 0 < i := by omega
      have hi : i-1<8 := by omega
      simpa [bit,show i-1+1=i by omega,zero] using incl ⟨i-1,hi⟩
  · simp [List.getD_eq_getElem?_getD,h]

/-- OR readers with a monotone prelude can enable their partner away from graph
    edges only on the single independent assignment {3,6,7}. AND readers must
    pass every assignment containing at least one of vertices 1, 4, and 5. -/
theorem monotone_partners {C : Circuit} {k a : Nat} (uq : RawPartner.unique C)
    (hk : k < C.gates.length) (positive : 0 < a) (args : (gateAt C k).inputs = [0,a])
    (correct : ∀x : RawPartner.Input, circuitFun 9 C (RawPartner.flip x) = RawPartner.graph x)
    (preMono : ∀ g ∈ C.gates.take k, g.op=.and ∨ g.op=.or) (m : Fin 256) :
    ((gateAt C k).op=.or → RawPartner.before C k (2*m.val) a=true →
      target (2*m.val)=true ∨ 2*m.val=200) ∧
    ((gateAt C k).op=.and → ((2*m.val).testBit 1 || (2*m.val).testBit 4 || (2*m.val).testBit 5)=true →
      RawPartner.before C k (2*m.val) a=true) := by
  constructor
  · intro reader on
    cases b : target (2*m.val) with
    | true => exact Or.inl rfl
    | false =>
      obtain exc | ⟨s,mem,le⟩ := extremal_masks.1 m b
      · exact Or.inr exc
      · have off := (RawPartner.passes uq hk positive args (correct_rows s mem) correct).2 reader
        exact (Bool.noConfusion (off.symm.trans (before_monotone preMono le on)))
  · intro reader on
    obtain ⟨s,mem,le⟩ := extremal_masks.2.1 m on
    exact before_monotone preMono le ((RawPartner.passes uq hk positive args (correct_rows s mem) correct).1 reader)

/-- A nonconstant two-coordinate partner for an AND reader must spend a NOT
    strictly before the reader. No restriction on the remainder of the circuit is needed. -/
theorem prior_not_of_binary_and {C : Circuit} {k a : Nat} (fan : FanInTwo C)
    (uq : RawPartner.unique C) (hk : k<C.gates.length) (positive : 0<a)
    (op : (gateAt C k).op=.and) (args : (gateAt C k).inputs=[0,a])
    (correct : ∀ x : RawPartner.Input, circuitFun 9 C (RawPartner.flip x) = RawPartner.graph x)
    (i j : Fin 8) (different : i ≠ j) (t : Bool → Bool → Bool)
    (rep : ∀ m, RawPartner.before C k m a = t (bit m i) (bit m j))
    (nonconstant : ¬∀ m, RawPartner.before C k m a = true) :
    ∃ g ∈ C.gates.take k, g.op=.not := by
  obtain c | ⟨_,truth⟩ := circuit_two_coordinates uq hk positive args correct true op i j different t rep
  · exact (nonconstant c).elim
  by_contra! no
  have pos : ∀ g ∈ C.gates.take k, g.op=.and ∨ g.op=.or := by
    intro g mem
    rcases (fan g (List.mem_of_mem_take mem)).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (no g mem h).elim
  have top : ∀ v : Fin 8, bit 510 v=true := by decide
  have bottom : ∀ v : Fin 8, bit 0 v=false := by decide
  have le : extendsMask 0 510 := fun v _ => top v
  have on : RawPartner.before C k 0 a=true := by simp [truth,bottom]
  have off : RawPartner.before C k 510 a=false := by simp [truth,top]
  exact Bool.noConfusion (off.symm.trans (before_monotone pos le on))

end Petersen3831.Partner

#print axioms Petersen3831.Partner.unary_constant
#print axioms Petersen3831.Partner.two_coordinates
#print axioms Petersen3831.Partner.circuit_two_coordinates
#print axioms Petersen3831.Partner.monotone_partners
#print axioms Petersen3831.Partner.prior_not_of_binary_and
