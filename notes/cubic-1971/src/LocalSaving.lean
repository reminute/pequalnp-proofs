import StarReader

namespace Cubic1971.LocalSaving

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Cubic1971.StarReader

def block (v base k h : ℕ) (p q : Gate) : List Gate :=
  [p, q, ⟨.and, [v,k]⟩, ⟨.or, [h,base+2]⟩]

private theorem run_append (gs hs : List Gate) (a : List Bool) :
    run (gs++hs) a = run hs (run gs a) := List.foldl_append

private theorem run_length (gs : List Gate) (a : List Bool) :
    (run gs a).length = a.length + gs.length := by
  induction gs generalizing a with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (a++[gateValue g a])).length = _
    rw [ih]
    simp; omega

private theorem retain_raw (gs : List Gate) (a : List Bool) (j : ℕ) (old : j<a.length) :
    (run gs a).getD j false = a.getD j false := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (a++[gateValue g a])).getD j false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ old]

private theorem ext_old {a b : List Bool} {v : ℕ}
    (sameLength : a.length = b.length) (same : ∀ j, j≠v → a.getD j false = b.getD j false)
    (bit : Bool) : ∀ j, j≠v → (a++[bit]).getD j false = (b++[bit]).getD j false := by
  intro j ne
  by_cases lower : j<a.length
  · rw [List.getD_append _ _ _ _ lower, List.getD_append _ _ _ _ (sameLength ▸ lower), same j ne]
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), sameLength]

private theorem prefix_agrees {v : ℕ} (gs : List Gate) (avoid : ∀ g ∈ gs, v ∉ g.inputs)
    (a b : List Bool) (lengths : a.length = b.length)
    (same : ∀ j, j≠v → a.getD j false = b.getD j false) :
    ∀ j, j≠v → (run gs a).getD j false = (run gs b).getD j false := by
  induction gs generalizing a b with
  | nil => exact same
  | cons g gs ih =>
    have eqv : gateValue g a = gateValue g b := congrArg g.op.eval
      (List.map_congr_left fun j hj => same j (fun e => avoid g (by simp) (e ▸ hj)))
    change ∀ j, j≠v → (run gs (a++[gateValue g a])).getD j false = (run gs (b++[gateValue g b])).getD j false
    rw [eqv]
    exact ih (fun h hh => avoid h (List.mem_cons_of_mem _ hh)) _ _ (by simp [lengths]) (ext_old lengths same _)

private theorem unchanged {n : ℕ} (v : Fin n) (x : Fin n → Bool) (gs : List Gate)
    (avoid : ∀ g ∈ gs, v.val ∉ g.inputs) (j : ℕ) (ne : j≠v.val) :
    (run gs (List.ofFn x)).getD j false = (run gs (List.ofFn (Function.update x v false))).getD j false := by
  apply prefix_agrees gs avoid _ _ (by simp) _ j ne
  intro i different
  by_cases small : i<n
  · have hne : (⟨i,small⟩ : Fin n) ≠ v := fun eq => different (congrArg Fin.val eq)
    simp [List.getD_eq_getElem?_getD,small,Function.update_of_ne hne]
  · simp [List.getD_eq_getElem?_getD,small]

/-- The two private gates p and q may do any computation. Their outputs and the
following AND can all be discarded once the centre is pinned to zero. -/
private theorem collapse (v k h : ℕ) (p q : Gate) (a : List Bool)
    (old : v < a.length) (hold : h < a.length) (off : a.getD v false = false) :
    run (block v a.length k h p q) a =
      a ++ [gateValue p a, gateValue q (a++[gateValue p a]), false, a.getD h false] := by
  let t := [gateValue p a, gateValue q (a++[gateValue p a])]
  have eqA : gateValue ⟨.and,[v,k]⟩ (a++t) = false := by
    simp only [gateValue, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
      List.getD_append _ _ _ _ old, off, id_eq, Bool.false_and]
  have eqO : gateValue ⟨.or,[h,a.length+2]⟩ (a++(t++[false])) = a.getD h false := by
    simp only [gateValue, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
      List.getD_append _ _ _ _ hold]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [t]
  change (((a++[_])++[_])++[_])++[_] = _
  simp only [List.append_assoc, List.singleton_append] at *
  simp only [t, List.cons_append, List.nil_append] at eqA eqO
  rw [eqA]
  simp only [List.cons_append,List.nil_append]
  rw [eqO]

theorem terminal_four {n : ℕ} (C : Circuit) (v : Fin n) (pre : List Gate) (p q : Gate) (k h : ℕ)
    (layout : C.gates = pre ++ block v.val (n+pre.length) k h p q)
    (output : C.output=n+pre.length+3) (legal : FanInTwo C)
    (avoid : ∀ g ∈ pre, v.val ∉ g.inputs) (hvalid : h<n+pre.length) (distinct : h≠v.val) :
    ∃ s, s+4 ≤ C.size ∧ HasCircuitSize n (fun x => circuitFun n C (Function.update x v false)) s := by
  refine ⟨pre.length, by simp [Circuit.size,layout,block], ⟨⟨pre,h⟩,?_,by simp [Circuit.size],?_⟩⟩
  · exact fun g hg => legal g (layout ▸ List.mem_append_left _ hg)
  · intro x
    let a := run pre (List.ofFn (Function.update x v false))
    have alen : a.length = n+pre.length := by simp [a,run_length]
    have off : a.getD v.val false = false := by
      rw [show a=run pre (List.ofFn (Function.update x v false)) from rfl,retain_raw _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD]
    change (run pre (List.ofFn x)).getD h false = (run C.gates (List.ofFn (Function.update x v false))).getD C.output false
    rw [unchanged v x pre avoid h distinct,layout,run_append,output]
    change a.getD h false = (run (block _ _ _ _ _ _) a).getD _ false
    rw [← alen,collapse _ _ _ _ _ _ (by omega) (by omega) off,List.getD_append_right _ _ _ _ (by omega)]
    simp

def mayRead (v base i : ℕ) : Prop := i ≠ v ∧ (i < base ∨ base+3 ≤ i)

/-- The fourth block output aliases h. Higher surviving wires move down four. -/
def redirect (base h i : ℕ) : ℕ :=
  if i<base then i else if i<base+4 then h else i-4

def renameGate (base h : ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map (redirect base h)⟩

private def Rel (v base h : ℕ) (a b : List Bool) : Prop :=
  base ≤ b.length ∧ a.length=b.length+4 ∧
  ∀ i, mayRead v base i → a.getD i false = b.getD (redirect base h i) false

private theorem rel_next {v base h : ℕ} {a b : List Bool} (valid : h < base)
    (rel : Rel v base h a b) (z : Bool) : Rel v base h (a++[z]) (b++[z]) := by
  obtain ⟨lo,delta,same⟩ := rel
  refine ⟨by simp; omega,by simp; omega,?_⟩
  intro i protect
  by_cases has : i < a.length
  · have mapped : redirect base h i < b.length := by
      unfold redirect
      split
      · omega
      · split <;> omega
    rw [List.getD_append _ _ _ _ has,List.getD_append _ _ _ _ mapped]
    exact same i protect
  · have shifted : redirect base h i = i-4 := by simp [redirect,show ¬i<base by omega,show ¬i<base+4 by omega]
    rw [shifted,List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
    rw [show i-a.length=i-4-b.length by omega]

private theorem rel_run {v base h : ℕ} (gs : List Gate) {a b : List Bool} (valid : h<base)
    (avoid : ∀ g ∈ gs, ∀ i ∈ g.inputs, mayRead v base i) (rel : Rel v base h a b) :
    Rel v base h (run gs a) (run (gs.map (renameGate base h)) b) := by
  induction gs generalizing a b with
  | nil => exact rel
  | cons g gs ih =>
    have vals : gateValue g a = gateValue (renameGate base h g) b := by
      unfold gateValue renameGate
      simp only [List.map_map]
      apply congrArg g.op.eval
      exact List.map_congr_left fun i hi => rel.2.2 i (avoid g (by simp) i hi)
    change Rel v base h (run gs (a++[gateValue g a]))
      (run (gs.map (renameGate base h)) (b++[gateValue (renameGate base h g) b]))
    rw [vals]
    exact ih (fun g mem => avoid g (List.mem_cons_of_mem _ mem)) (rel_next valid rel _)

private theorem rel_start {v base h : ℕ} (a b : List Bool) (alen : a.length=base) (blen : b.length=base)
    (old : ∀ i, i≠v → a.getD i false = b.getD i false) (valid : h<base) (hne : h≠v) (p q : Bool) :
    Rel v base h (a++[p,q,false,a.getD h false]) b := by
  refine ⟨blen.ge, by simp [alen,blen], ?_⟩
  intro i protect
  obtain ⟨different,outside⟩ := protect
  rcases outside with lower | upper
  · rw [List.getD_append _ _ _ _ (by omega)]
    simpa [redirect,lower] using old i different
  · rw [List.getD_append_right _ _ _ _ (by omega),alen]
    by_cases last : i=base+3
    · subst i
      simpa [redirect] using old h hne
    · have far : base + 4 ≤ i := by omega
      rw [show redirect base h i=i-4 by simp [redirect,show ¬i<base by omega,show ¬i<base+4 by omega]]
      rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]

/-- Pin a sole centre AND whose two supplying gates and first consumer form a private
four-gate block. Every later gate may read the fourth output, including repeated uses. -/
theorem internal_four_raw {n : ℕ} (C : Circuit) (v : Fin n) (pre post : List Gate)
    (p q : Gate) (k h : ℕ)
    (layout : C.gates = (pre ++ block v.val (n+pre.length) k h p q) ++ post)
    (legal : FanInTwo C) (prefixClean : ∀ g ∈ pre, v.val ∉ g.inputs)
    (suffixClean : ∀ g ∈ post, ∀ i ∈ g.inputs, mayRead v.val (n+pre.length) i)
    (outputClean : mayRead v.val (n+pre.length) C.output)
    (hvalid : h<n+pre.length) (hne : h≠v.val) :
    ∃ s, s+4 ≤ C.size ∧ HasCircuitSize n (fun x => circuitFun n C (Function.update x v false)) s := by
  let base := n+pre.length
  let ren := renameGate base h
  let D : Circuit := ⟨pre++post.map ren,redirect base h C.output⟩
  refine ⟨pre.length+post.length, by simp [Circuit.size,layout,block]; omega,
    ⟨D,?_,by simp [D,Circuit.size],?_⟩⟩
  · intro g mem
    change g ∈ pre++post.map ren at mem
    rcases List.mem_append.mp mem with fromPre | fromPost
    · exact legal g (layout ▸ List.mem_append_left _ (List.mem_append_left _ fromPre))
    · obtain ⟨old,inpost,rfl⟩ := List.mem_map.mp fromPost
      have oldok := legal old (layout ▸ List.mem_append_right _ inpost)
      simpa [ren,renameGate] using oldok
  · intro x
    let a := run pre (List.ofFn (Function.update x v false))
    let b := run pre (List.ofFn x)
    have alen : a.length=base := by simp [a,base,run_length]
    have blen : b.length=base := by simp [b,base,run_length]
    have off : a.getD v.val false=false := by
      rw [show a=run pre (List.ofFn (Function.update x v false)) from rfl,retain_raw _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD]
    have init : Rel v.val base h (run (block v.val base k h p q) a) b := by
      rw [show block v.val base k h p q = block v.val a.length k h p q by rw [alen],
        collapse _ _ _ _ _ _ (by dsimp [base] at alen; omega) (by omega) off]
      exact rel_start a b alen blen (fun i ne => (unchanged v x pre prefixClean i ne).symm) hvalid hne _ _
    have final := (rel_run post hvalid suffixClean init).2.2 C.output outputClean
    change (run (pre++post.map ren) (List.ofFn x)).getD (redirect base h C.output) false =
      (run C.gates (List.ofFn (Function.update x v false))).getD C.output false
    rw [layout,run_append,run_append,run_append]
    exact final.symm

private def trim (g : Gate) : Gate :=
  ⟨g.op, g.inputs.take (if g.op.eval [false] then 1 else 2)⟩

private def trimmed (C : Circuit) : Circuit := ⟨C.gates.map trim, C.output⟩

private theorem trim_gate (g : Gate) (w : List Bool)
    (ok : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    gateValue (trim g) w = gateValue g w := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨opOK,len⟩ := ok
  change op = .and ∨ op = .or ∨ op = .not at opOK
  change ins.length ≤ 2 at len
  rcases opOK with rfl | rfl | rfl
  · simp [trim,gateValue,GateOp.eval,List.take_of_length_le len]
  · simp [trim,gateValue,GateOp.eval,List.take_of_length_le len]
  · cases ins <;> rfl

private theorem trim_run (gs : List Gate)
    (ok : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (w : List Bool) : run (gs.map trim) w = run gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change run (gs.map trim) (w++[gateValue (trim g) w]) = run gs (w++[gateValue g w])
    rw [trim_gate g w (ok g (by simp))]
    exact ih (fun t ht => ok t (List.mem_cons_of_mem _ ht)) _

/-- Four-gate saving for a private block read through its final output. Both exclusion
conditions use the posted effective inputs, so a NOT gate may contain an ignored
second operand naming the pinned variable or either of the private intermediate wires. -/
theorem internal_four {n : ℕ} (C : Circuit) (v : Fin n) (pre post : List Gate)
    (p q : Gate) (k h : ℕ)
    (layout : C.gates = (pre ++ block v.val (n+pre.length) k h p q) ++ post)
    (legal : FanInTwo C) (prefixClean : ∀ g ∈ pre, ¬ effective v.val g)
    (suffixClean : ∀ g ∈ post, ∀ i, effective i g → mayRead v.val (n+pre.length) i)
    (outputClean : mayRead v.val (n+pre.length) C.output)
    (hvalid : h<n+pre.length) (hne : h≠v.val) :
    ∃ s, s+4 ≤ C.size ∧ HasCircuitSize n (fun x => circuitFun n C (Function.update x v false)) s := by
  let D := trimmed C
  have size : D.size=C.size := by simp [D,trimmed,Circuit.size]
  have ops : FanInTwo D := by
    intro g mg
    obtain ⟨t,mem,rfl⟩ := List.mem_map.mp mg
    obtain ⟨opc,len⟩ := legal t mem
    refine ⟨opc,?_⟩
    change (t.inputs.take _).length ≤ 2
    rw [List.length_take]
    exact (Nat.min_le_right _ _).trans len
  have lyt : D.gates = ((pre.map trim) ++ block v.val (n+(pre.map trim).length) k h (trim p) (trim q)) ++ post.map trim := by
    simp only [D,trimmed,layout,List.map_append,List.length_map]
    rfl
  have before : ∀ g ∈ pre.map trim, v.val ∉ g.inputs := by
    intro g mg
    obtain ⟨t,mt,rfl⟩ := List.mem_map.mp mg
    exact prefixClean t mt
  have after : ∀ g ∈ post.map trim, ∀ i ∈ g.inputs, mayRead v.val (n+(pre.map trim).length) i := by
    intro g mg i hi
    obtain ⟨t,mt,rfl⟩ := List.mem_map.mp mg
    simpa using suffixClean t mt i hi
  have out : mayRead v.val (n+(pre.map trim).length) D.output := by simpa [D,trimmed] using outputClean
  obtain ⟨s,save,result⟩ := internal_four_raw D v _ _ _ _ k h lyt ops before after out (by simpa using hvalid) hne
  have same : circuitFun n D = circuitFun n C := by
    funext x
    change (run (C.gates.map trim) (List.ofFn x)).getD C.output false =
      (run C.gates (List.ofFn x)).getD C.output false
    rw [trim_run _ legal]
  exact ⟨s,size ▸ save,same ▸ result⟩

end Cubic1971.LocalSaving

#print axioms Cubic1971.LocalSaving.terminal_four
#print axioms Cubic1971.LocalSaving.internal_four
