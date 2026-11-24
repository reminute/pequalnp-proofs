import NormalForm

namespace Cubic1971.SuffixBarrier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity StarReader

private def Ordered (w z : List Bool) : Prop :=
  w.length = z.length ∧ ∀ i, w.getD i false = true → z.getD i false = true

private theorem extend {w z : List Bool} (h : Ordered w z) {x y : Bool}
    (xy : x = true → y = true) : Ordered (w ++ [x]) (z ++ [y]) := by
  refine ⟨by simp [h.1],fun i => ?_⟩
  by_cases earlier : i < w.length
  · rw [List.getD_append _ _ _ _ earlier,List.getD_append _ _ _ _ (h.1 ▸ earlier)]
    exact h.2 i
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by rw [←h.1]; omega),h.1]
    cases i-z.length with
    | zero => exact xy
    | succ j => simp [List.getD_eq_getElem?_getD]

private theorem run_order (gs : List Gate)
    (pos : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) {w z : List Bool}
    (h : Ordered w z) : Ordered (run gs w) (run gs z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    apply ih (fun d mem => pos d (List.mem_cons_of_mem _ mem))
    apply extend h
    rcases pos g (by simp) with op | op
    · simp [gateValue,op,GateOp.eval]
      exact fun all i mem => h.2 i (all i mem)
    · simp [gateValue,op,GateOp.eval]
      exact fun i mem on => ⟨i,mem,h.2 i on⟩

/-- A minimum circuit whose gate copies v on every rejecting row, and is at
    most v on every row, must contain a later inverter. -/
theorem needs_not {n : Nat} (C : Circuit) (f : (Fin n → Bool) → Bool) (v : Fin n)
    (pre post : List Gate) (r : Gate) (layout : C.gates = pre ++ r :: post)
    (legal : FanInTwo C) (correct : circuitFun n C = f)
    (least : ∀ s, HasCircuitSize n f s → C.size ≤ s)
    (below : ∀ x : Fin n → Bool, let w := run pre (List.ofFn x)
      gateValue r w = true → w.getD v.val false = true)
    (copyOnFalse : ∀ x : Fin n → Bool, f x = false → let w := run pre (List.ofFn x)
      gateValue r w = w.getD v.val false) :
    ∃ g ∈ post, g.op = .not := by
  by_contra! no
  have pos : ∀ g ∈ post, g.op = .and ∨ g.op = .or := by
    intro g mem
    have hop := (legal g (layout ▸ List.mem_append_right _ (List.mem_cons_of_mem _ mem))).1
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at hop
    exact hop.elim Or.inl (fun h => h.elim Or.inr (fun e => (no g mem e).elim))
  let idGate : Gate := ⟨.and,[v.val]⟩
  let D : Circuit := ⟨pre ++ idGate :: post,C.output⟩
  have copy (w : List Bool) : gateValue idGate w = w.getD v.val false := by
    simp [gateValue,idGate,GateOp.eval]
  have newFan : FanInTwo D := by
    intro g mem
    rcases List.mem_append.mp mem with first | rest
    · exact legal _ (layout ▸ List.mem_append_left _ first)
    · rcases List.mem_cons.mp rest with rfl | last
      · simp [idGate]
      · exact legal _ (layout ▸ List.mem_append_right _ (List.mem_cons_of_mem _ last))
  have eval_eq (x : Fin n → Bool) : circuitFun n D x = f x := by
    let w := run pre (List.ofFn x)
    have splitAt (g : Gate) : run (pre ++ g :: post) (List.ofFn x) =
        run post (w ++ [gateValue g w]) := by
      simp only [w,run,List.foldl_append,List.foldl_cons]
    have original := congrFun correct x
    change (run C.gates (List.ofFn x)).getD C.output false = f x at original
    rw [layout,splitAt] at original
    change (run (pre ++ idGate :: post) (List.ofFn x)).getD C.output false = f x
    rw [splitAt,copy]
    cases fx : f x with
    | false =>
      have eqv : gateValue r w = w.getD v.val false := copyOnFalse x fx
      exact eqv ▸ (original.trans fx)
    | true =>
      have mono := run_order post pos (extend (w:=w) (z:=w) ⟨rfl,fun _ h => h⟩ (below x))
      exact mono.2 _ (original.trans fx)
  have sz : D.size = C.size := by simp [D,Circuit.size,layout]
  exact NormalForm.not_copy newFan (funext eval_eq) (fun s hs => sz ▸ least s hs) rfl v (fun x => copy _)

end Cubic1971.SuffixBarrier

#print axioms Cubic1971.SuffixBarrier.needs_not
