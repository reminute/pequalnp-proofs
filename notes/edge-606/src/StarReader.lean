import PEqualNP.Defs
import NeighborCube

namespace Cubic1971.StarReader

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Cubic1971.NeighborCube

def effective (v : ℕ) (g : Gate) : Prop :=
  v ∈ g.inputs.take (if g.op.eval [false] then 1 else 2)

/-- The Boolean filter used verbatim in the posted reader-count hypothesis. -/
def readBit (v : ℕ) (g : Gate) : Bool :=
  (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v

theorem readBit_iff (v : ℕ) (g : Gate) : readBit v g = true ↔ effective v g := by
  cases h : g.op.eval [false] <;> simp [readBit, effective, h]

theorem sole_of_count {v : ℕ} {C : Circuit} {pre post : List Gate} {r : Gate}
    (layout : C.gates = pre ++ r :: post) (reader : effective v r)
    (cap : (C.gates.filter (readBit v)).length ≤ 1) : ∀ g ∈ pre ++ post, ¬ effective v g := by
  have yes := (readBit_iff v r).mpr reader
  rw [layout, List.filter_append, List.filter_cons_of_pos yes] at cap
  simp only [List.length_append, List.length_cons] at cap
  have a : pre.filter (readBit v) = [] := List.length_eq_zero_iff.mp (by omega)
  have b : post.filter (readBit v) = [] := List.length_eq_zero_iff.mp (by omega)
  intro g mem eg
  have good := (readBit_iff v g).mpr eg
  rcases List.mem_append.mp mem with h | h
  · exact List.not_mem_nil (a ▸ List.mem_filter.mpr ⟨h,good⟩)
  · exact List.not_mem_nil (b ▸ List.mem_filter.mpr ⟨h,good⟩)

def gateValue (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)

def run (gs : List Gate) (w : List Bool) :=
  gs.foldl (fun a g => a ++ [gateValue g a]) w

private def Agree (v : ℕ) (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, i ≠ v → a.getD i false = b.getD i false

private theorem gate_agrees {v : ℕ} {g : Gate} {a b : List Bool}
    (agree : Agree v a b) (op : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (len : g.inputs.length ≤ 2) (none : ¬ effective v g) :
    gateValue g a = gateValue g b := by
  obtain ⟨o,is⟩ := g
  change o = .and ∨ o = .or ∨ o = .not at op
  change is.length ≤ 2 at len
  rcases is with _ | ⟨i, _ | ⟨j, _ | ⟨k, ks⟩⟩⟩
  · rfl
  · rcases op with rfl | rfl | rfl <;>
      simp [effective, GateOp.eval] at none <;>
      simp only [gateValue, List.map_cons, List.map_nil, agree.2 i (Ne.symm none)]
  · rcases op with rfl | rfl | rfl
    · simp [effective, GateOp.eval] at none
      simp only [gateValue, List.map_cons, List.map_nil, agree.2 i (Ne.symm none.1),
        agree.2 j (Ne.symm none.2)]
    · simp [effective, GateOp.eval] at none
      simp only [gateValue, List.map_cons, List.map_nil, agree.2 i (Ne.symm none.1),
        agree.2 j (Ne.symm none.2)]
    · simp [effective, GateOp.eval] at none
      change (!(a.getD i false)) = (!(b.getD i false))
      rw [agree.2 i (Ne.symm none)]
  · simp at len

private theorem append_agrees {v : ℕ} {a b : List Bool} (same : Agree v a b) (bit : Bool) :
    Agree v (a++[bit]) (b++[bit]) := by
  refine ⟨by simp [same.1], ?_⟩
  intro i ne
  by_cases lower : i < a.length
  · rw [List.getD_append _ _ _ _ lower, List.getD_append _ _ _ _ (same.1 ▸ lower)]
    exact same.2 i ne
  · rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by simpa [← same.1] using Nat.le_of_not_gt lower), same.1]

private theorem run_agrees {v : ℕ} (gs : List Gate) {a b : List Bool} (same : Agree v a b)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (none : ∀ g ∈ gs, ¬ effective v g) : Agree v (run gs a) (run gs b) := by
  induction gs generalizing a b with
  | nil => exact same
  | cons g gs ih =>
    have ok := legal g (by simp)
    have eqv := gate_agrees same ok.1 ok.2 (none g (by simp))
    change Agree v (run gs (a++[gateValue g a])) (run gs (b++[gateValue g b]))
    rw [eqv]
    apply ih (append_agrees same _)
    · exact fun h mem => legal h (List.mem_cons_of_mem _ mem)
    · exact fun h mem => none h (List.mem_cons_of_mem _ mem)

private theorem retains (gs : List Gate) (a : List Bool) (i : ℕ) (lo : i < a.length) :
    (run gs a).getD i false = a.getD i false := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (a++[gateValue g a])).getD i false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ lo]

def starInput {n : ℕ} (v : Fin n) (leaves : Fin 3 → Fin n) (s : Bits) (x : Bool) :
    Fin n → Bool := fun w => if w=v then x else
      decide (∃ i : Fin 3, leaves i = w ∧ s i = true)

def partner {n : ℕ} (v : Fin n) (leaves : Fin 3 → Fin n) (pre : List Gate) (k : ℕ)
    (s : Bits) : Bool := (run pre (List.ofFn (starInput v leaves s false))).getD k false

private theorem initial_agree {n : ℕ} (v : Fin n) (x y : Fin n → Bool)
    (h : ∀ i, i ≠ v → x i = y i) : Agree v.val (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i ne
  by_cases lo : i<n
  · have different : (⟨i,lo⟩ : Fin n) ≠ v := fun eq => ne (congrArg Fin.val eq)
    simpa [List.getD_eq_getElem?_getD, lo] using h ⟨i,lo⟩ different
  · simp [List.getD_eq_getElem?_getD, lo]

theorem output_ne_of_star {n : ℕ} (C : Circuit) (v : Fin n) (leaves : Fin 3 → Fin n)
    (star : ∀ s x, C.eval (List.ofFn (starInput v leaves s x)) = (x && anyNeighbor s)) :
    C.output ≠ v.val := by
  intro atRaw
  have off := star blank true
  change (run C.gates (List.ofFn (starInput v leaves blank true))).getD C.output false = false at off
  rw [atRaw, retains _ _ _ (by simp)] at off
  simp [List.getD_eq_getElem?_getD, starInput] at off

/-- The posted bound of at most one reader provides an actual gate position; both
surrounding lists are free of effective reads of the centre. -/
theorem split_reader {n : ℕ} (C : Circuit) (v : Fin n) (leaves : Fin 3 → Fin n)
    (legal : FanInTwo C) (cap : (C.gates.filter (readBit v.val)).length ≤ 1)
    (star : ∀ s x, C.eval (List.ofFn (starInput v leaves s x)) = (x && anyNeighbor s)) :
    ∃ pre r post, C.gates = pre ++ r :: post ∧ effective v.val r ∧
      ∀ g ∈ pre ++ post, ¬ effective v.val g := by
  have reader : ∃ r ∈ C.gates, effective v.val r := by
    by_contra! none
    let s : Bits := fun _ => true
    have inits := initial_agree v (starInput v leaves s true) (starInput v leaves s false)
      (fun i h => by simp [starInput, h])
    have same := (run_agrees C.gates inits legal none).2 C.output (output_ne_of_star C v leaves star)
    change C.eval (List.ofFn (starInput v leaves s true)) =
      C.eval (List.ofFn (starInput v leaves s false)) at same
    simp [star, s, anyNeighbor] at same
  obtain ⟨r,mem,read⟩ := reader
  obtain ⟨pre,post,layout⟩ := List.append_of_mem mem
  exact ⟨pre,r,post,layout,read,sole_of_count layout read cap⟩

theorem reader_factor {n : ℕ} (C : Circuit) (v : Fin n)
    (pre post : List Gate) (r : Gate) (k : ℕ) (isAnd : Bool)
    (layout : C.gates = pre ++ r :: post) (legal : FanInTwo C)
    (sole : ∀ g ∈ pre ++ post, ¬ effective v.val g)
    (readerOp : r.op = if isAnd then .and else .or)
    (inputs : r.inputs=[v.val,k] ∨ r.inputs=[k,v.val]) (other : k ≠ v.val)
    (output : C.output ≠ v.val)
    (row : Bool → Fin n → Bool) (unchanged : ∀ x i, i≠v → row x i = row false i)
    (center : ∀ x, row x v=x) (x : Bool) :
    let w := run pre (List.ofFn (row false))
    let bit := if isAnd then x && w.getD k false else x || w.getD k false
    C.eval (List.ofFn (row x)) = (run post (w++[bit])).getD C.output false := by
  let before (x : Bool) := run pre (List.ofFn (row x))
  have init := initial_agree v (row x) (row false) (unchanged x)
  have inPre : ∀ g ∈ pre, g ∈ C.gates := fun g h => layout ▸ List.mem_append_left _ h
  have inPost : ∀ g ∈ post, g ∈ C.gates := fun g h => layout ▸ List.mem_append_right _ (List.mem_cons_of_mem _ h)
  have same : Agree v.val (before x) (before false) :=
    run_agrees pre init (fun g h => legal g (inPre g h)) (fun g h => sole g (List.mem_append_left _ h))
  have raw : (before x).getD v.val false = x := by
    rw [show before x = run pre (List.ofFn (row x)) from rfl,
      retains _ _ _ (by simp)]
    simpa [List.getD_eq_getElem?_getD, v.isLt] using center x
  let bit := if isAnd then x && (before false).getD k false else x || (before false).getD k false
  have eqv : gateValue r (before x) = bit := by
    have pk : (before x).getD k false = (before false).getD k false := same.2 _ other
    rcases inputs with h | h <;> simp only [gateValue, h, List.map_cons, List.map_nil, raw, pk] <;>
      cases isAnd <;> simp [readerOp, GateOp.eval, bit, Bool.and_comm, Bool.or_comm]
  have passed := run_agrees post (append_agrees same bit)
    (fun g h => legal g (inPost g h)) (fun g h => sole g (List.mem_append_right _ h))
  have reflected : C.eval (List.ofFn (row x)) =
      (run post (before x ++ [bit])).getD C.output false := by
    unfold Circuit.eval Circuit.wires
    rw [layout, List.foldl_append]
    change (run post (before x ++ [gateValue r (before x)])).getD C.output false = _
    rw [eqv]
  exact reflected.trans (passed.2 _ output)

/-- The circuit is sampled on the star with raw centre v and three leaves. The only
effective reader of v is the displayed binary gate. Its other wire may be internal. -/
theorem classified_reader {n : ℕ} (C : Circuit) (v : Fin n) (leaves : Fin 3 → Fin n)
    (pre post : List Gate) (r : Gate) (k : ℕ) (isAnd : Bool)
    (layout : C.gates = pre ++ r :: post) (legal : FanInTwo C)
    (sole : ∀ g ∈ pre ++ post, ¬ effective v.val g)
    (readerOp : r.op = if isAnd then .and else .or)
    (inputs : r.inputs=[v.val,k] ∨ r.inputs=[k,v.val]) (other : k ≠ v.val)
    (output : C.output ≠ v.val)
    (star : ∀ s x, C.eval (List.ofFn (starInput v leaves s x)) = (x && anyNeighbor s)) :
    (∀ s, partner v leaves pre k s = isAnd) ∨
    (∀ s, partner v leaves pre k s = if isAnd then anyNeighbor s else !(anyNeighbor s)) := by
  let before (s : Bits) (x : Bool) := run pre (List.ofFn (starInput v leaves s x))
  let suffix (s : Bits) (bit : Bool) := (run post (before s false ++ [bit])).getD C.output false
  apply classified _ suffix isAnd
  intro s x
  let row := fun (x : Bool) => starInput v leaves s x
  have result := reader_factor C v pre post r k isAnd layout legal sole readerOp inputs other output
    row (fun x i h => by simp [row, starInput, h]) (fun x => by simp [row, starInput]) x
  exact result.symm.trans (star s x)

/-- If the two cofactors at one fixed raw row differ, the other input of the
unique binary reader takes its enabling value on that row. -/
theorem gatedPartner {n : ℕ} (C : Circuit) (v : Fin n)
    (pre post : List Gate) (r : Gate) (k : ℕ) (isAnd : Bool)
    (layout : C.gates = pre ++ r :: post) (legal : FanInTwo C)
    (sole : ∀ g ∈ pre ++ post, ¬ effective v.val g)
    (readerOp : r.op = if isAnd then .and else .or)
    (inputs : r.inputs=[v.val,k] ∨ r.inputs=[k,v.val]) (other : k ≠ v.val)
    (output : C.output ≠ v.val) (x : Fin n → Bool)
    (flip : C.eval (List.ofFn (Function.update x v false)) ≠
      C.eval (List.ofFn (Function.update x v true))) :
    (run pre (List.ofFn (Function.update x v false))).getD k false = isAnd := by
  let row := fun (b : Bool) => Function.update x v b
  have cut := reader_factor C v pre post r k isAnd layout legal sole readerOp inputs other output
    row (fun b i h => by simp [row, Function.update_of_ne h]) (fun _ => by simp [row])
  change C.eval (List.ofFn (row false)) ≠ C.eval (List.ofFn (row true)) at flip
  rw [cut false, cut true] at flip
  let w := run pre (List.ofFn (row false))
  change w.getD k false = isAnd
  change (run post (w ++ [if isAnd then false && w.getD k false else false || w.getD k false])).getD C.output false ≠
    (run post (w ++ [if isAnd then true && w.getD k false else true || w.getD k false])).getD C.output false at flip
  cases isAnd <;> cases h : w.getD k false <;> simp_all

end Cubic1971.StarReader

#print axioms Cubic1971.StarReader.classified_reader
#print axioms Cubic1971.StarReader.gatedPartner
#print axioms Cubic1971.StarReader.split_reader
