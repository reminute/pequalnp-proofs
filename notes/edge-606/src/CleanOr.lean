import MinimalPartner

namespace Edge606.CleanOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1708_aux Cubic1971.StarReader
open MinimalPartner

/-- Drop the gate at the split and redirect its former wire to the raw input v.
    Prefix gates stay untouched, so forward references in the prefix still default to false. -/
def bypass (n : Nat) (pre post : List Gate) (out v : Nat) : Circuit :=
  let a := n + pre.length
  ⟨pre ++ post.map (relabel a v), redirect a v out⟩

/-- A wire not yet computed at the split is false there. It must remain false
    even if its original numeric index exists when the final OR is evaluated. -/
def partnerWire (n : Nat) (pre : List Gate) (B : Circuit) (k : Nat) : Nat :=
  if k < n + pre.length then k else n + B.size

def addOr (n : Nat) (B : Circuit) (q : Nat) : Circuit :=
  ⟨B.gates ++ [⟨.or,[B.output,q]⟩], n + B.size⟩

def result (n : Nat) (pre post : List Gate) (out v k : Nat) : Circuit :=
  let B := bypass n pre post out v
  addOr n B (partnerWire n pre B k)

theorem bypass_mono {n : Nat} (C : Circuit) (mono : Monotone2 C)
    {pre post : List Gate} {r : Gate} (layout : C.gates = pre ++ r :: post) (v : Fin n) :
    Monotone2 (bypass n pre post C.output v.val) := by
  intro g mem
  rcases List.mem_append.mp mem with a | b
  · exact mono _ (layout ▸ List.mem_append_left _ a)
  · obtain ⟨h,hm,rfl⟩ := List.mem_map.mp b
    simpa [relabel] using mono h (layout ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hm))

theorem bypass_size (n : Nat) (C : Circuit) {pre post : List Gate} {r : Gate}
    (layout : C.gates = pre ++ r :: post) (v : Nat) :
    (bypass n pre post C.output v).size + 1 = C.size := by
  simp [bypass,Circuit.size,layout,Nat.add_assoc]

private theorem bypass_off {n : Nat} (C : Circuit) {pre post : List Gate} {r : Gate}
    {k : Nat} (v : Fin n) (layout : C.gates = pre ++ r :: post)
    (op : r.op = .or) (args : r.inputs = [v.val,k] ∨ r.inputs = [k,v.val])
    (x : Fin n → Bool) (off : circuitFun n (⟨pre,k⟩ : Circuit) x = false) :
    circuitFun n (bypass n pre post C.output v.val) x = circuitFun n C x := by
  let w := run pre (List.ofFn x)
  have count : w.length = n + pre.length := by
    change (wiresFrom pre (List.ofFn x)).length = _
    simp [length_wiresFrom]
  change w.getD k false = false at off
  have eq : gateValue r w = w.getD v.val false := by
    rcases args with a | a <;>
      simp only [gateValue,op,a,List.map_cons,List.map_nil,GateOp.eval,List.any_cons,
        List.any_nil,id_eq,off,Bool.false_or,Bool.or_false]
  have matched := after_copy w v.val (gateValue r w) eq
  rw [count] at matched
  have followed := (carry_copy (show v.val < n + pre.length by have := v.isLt; omega)
    post matched).2.2 C.output
  change (run (pre ++ post.map _) (List.ofFn x)).getD _ false =
    (run C.gates (List.ofFn x)).getD C.output false
  rw [layout]
  simpa only [bypass,w,run,List.foldl_append,List.foldl_cons] using followed.symm

theorem preserved_partner (n : Nat) (pre post : List Gate) (out v k : Nat)
    (x : Fin n → Bool) :
    let B := bypass n pre post out v
    (B.wires (List.ofFn x)).getD (partnerWire n pre B k) false =
      circuitFun n (⟨pre,k⟩ : Circuit) x := by
  let B := bypass n pre post out v
  change (B.wires (List.ofFn x)).getD (partnerWire n pre B k) false =
    (wiresFrom pre (List.ofFn x)).getD k false
  by_cases earlier : k < n + pre.length
  · simp only [partnerWire,earlier,↓reduceIte]
    change (wiresFrom (pre ++ post.map _) _).getD _ false = _
    rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix
      (post.map (relabel (n + pre.length) v)) (wiresFrom pre (List.ofFn x))
    rw [ht,List.getD_append _ _ _ _ (by simpa [length_wiresFrom] using earlier)]
  · simp only [partnerWire,earlier,↓reduceIte]
    have len : (B.wires (List.ofFn x)).length = n + B.size := by
      change (wiresFrom B.gates (List.ofFn x)).length = n + B.gates.length
      simp [length_wiresFrom]
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by
      simp [length_wiresFrom]; omega)]

private theorem eval_addOr {n : Nat} (B : Circuit) (q : Nat) (x : Fin n → Bool) :
    circuitFun n (addOr n B q) x =
      (circuitFun n B x || (B.wires (List.ofFn x)).getD q false) := by
  let w := B.wires (List.ofFn x)
  have len : w.length = n + B.size := by
    change (wiresFrom B.gates (List.ofFn x)).length = n + B.gates.length
    simp [length_wiresFrom]
  change (wiresFrom (B.gates ++ [_]) (List.ofFn x)).getD (n+B.size) false = _
  rw [wiresFrom_append]
  change (w ++ [gateValue ⟨.or,[B.output,q]⟩ w]).getD (n+B.size) false =
    (w.getD B.output false || w.getD q false)
  rw [← len, getD_snoc_eq]
  simp [gateValue,GateOp.eval]

/-- The relocated circuit computes the disjunction of the shortened circuit
    and the partner as it was evaluated at the original split. -/
theorem result_eval (n : Nat) (pre post : List Gate) (out v k : Nat) (x : Fin n → Bool) :
    circuitFun n (result n pre post out v k) x =
      (circuitFun n (bypass n pre post out v) x || circuitFun n (⟨pre,k⟩ : Circuit) x) := by
  simp only [result,eval_addOr,preserved_partner]

/-- Move the physical partner to a final OR at the same total gate count. -/
theorem relocate {n : Nat} (C : Circuit) (mono : Monotone2 C) (pre post : List Gate)
    (r : Gate) (k : Nat) (v : Fin n) (layout : C.gates = pre ++ r :: post)
    (op : r.op = .or) (args : r.inputs = [v.val,k] ∨ r.inputs = [k,v.val])
    (safe : ∀ x, circuitFun n (⟨pre,k⟩ : Circuit) x = true → circuitFun n C x = true) :
    let D := result n pre post C.output v.val k
    Monotone2 D ∧ D.size = C.size ∧ circuitFun n D = circuitFun n C := by
  let B := bypass n pre post C.output v.val
  let q := partnerWire n pre B k
  change Monotone2 (addOr n B q) ∧ (addOr n B q).size = C.size ∧
    circuitFun n (addOr n B q) = circuitFun n C
  refine ⟨?_,?_,?_⟩
  · intro g mem
    change g ∈ B.gates ++ [_] at mem
    rcases List.mem_append.mp mem with old | last
    · exact bypass_mono C mono layout v g old
    · obtain rfl := List.mem_singleton.mp last
      exact ⟨Or.inr rfl,le_rfl⟩
  · simp [addOr,B,bypass,Circuit.size,layout]
  · funext x
    change circuitFun n (result n pre post C.output v.val k) x = _
    rw [result_eval]
    cases h : circuitFun n (⟨pre,k⟩ : Circuit) x with
    | false => simpa only [Bool.or_false] using bypass_off C v layout op args x h
    | true => simp [safe x h]

end Edge606.CleanOr
