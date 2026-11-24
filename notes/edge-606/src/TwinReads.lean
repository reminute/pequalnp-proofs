import WeightedPin

namespace Edge606.TwinReads

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1708_aux

variable {n : Nat}

private def value (x : Fin n → Bool) (t : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun j => (List.ofFn x ++ t).getD j false)

private theorem raw (x : Fin n → Bool) (t : List Bool) (i : Fin n) :
    (List.ofFn x ++ t).getD i.val false = x i := by
  rw [List.getD_append _ _ _ _ (by simp)]
  simp

private theorem agreeAt (x y : Fin n → Bool) (t : List Bool) (j : Nat)
    (agree : ∀ i : Fin n, i.val = j → x i = y i) :
    (List.ofFn x ++ t).getD j false = (List.ofFn y ++ t).getD j false := by
  by_cases small : j < n
  · let i : Fin n := ⟨j, small⟩
    exact (raw x t i).trans ((agree i rfl).trans (raw y t i).symm)
  · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt small),
      List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt small)]
    simp

private theorem sameTail (gs : List Gate) (x y : Fin n → Bool) (t : List Bool)
    (step : ∀ g ∈ gs, ∀ w, value x w g = value y w g) :
    ∃ s : List Bool, wiresFrom gs (List.ofFn x ++ t) = List.ofFn x ++ s ∧
      wiresFrom gs (List.ofFn y ++ t) = List.ofFn y ++ s := by
  induction gs generalizing t with
  | nil => exact ⟨t,rfl,rfl⟩
  | cons g gs ih =>
    have eq := step g List.mem_cons_self t
    obtain ⟨s, left, right⟩ := ih (t ++ [value x t g])
      (fun z hz => step z (List.mem_cons_of_mem _ hz))
    refine ⟨s, ?_, ?_⟩
    · simpa only [wiresFrom,List.foldl_cons,List.append_assoc,value] using left
    · rw [eq] at right
      simpa only [wiresFrom,List.foldl_cons,List.append_assoc,value] using right

private theorem eval_of_steps (C : Circuit) (x y : Fin n → Bool)
    (gates : ∀ g ∈ C.gates, ∀ t, value x t g = value y t g)
    (output : ∀ i : Fin n, i.val = C.output → x i = y i) :
    circuitFun n C x = circuitFun n C y := by
  obtain ⟨s, left, right⟩ := sameTail C.gates x y [] gates
  simp only [List.append_nil] at left right
  change (wiresFrom C.gates _).getD C.output false = (wiresFrom C.gates _).getD C.output false
  rw [left,right]
  exact agreeAt x y s _ output

private theorem two_raw {a b : Nat} (ab : a ≠ b) {l : List Nat}
    (size : l.length ≤ 2) (ha : a ∈ l) (hb : b ∈ l) :
    l = [a,b] ∨ l = [b,a] := by
  rcases l with _ | ⟨c, _ | ⟨d, _ | ⟨e,t⟩⟩⟩ <;> simp_all
  grind

theorem output_ne {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (computes : circuitFun n C = fun x : Fin n → Bool =>
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) (v : Fin n) :
    C.output ≠ v.val := by
  intro eq
  have h := congrFun computes (fun p => decide (p = v))
  change (C.wires _).getD C.output false = _ at h
  rw [eq, input_value, singleton_false] at h
  simp at h

/-- Raw inputs that always occur together are interchangeable at every gate. -/
theorem swap (C : Circuit) (mono : Monotone2 C) {u v : Fin n} (uv : u ≠ v)
    (paired : ∀ j : Fin C.gates.length,
      u.val ∈ (C.gates.get j).inputs ↔ v.val ∈ (C.gates.get j).inputs)
    (outU : C.output ≠ u.val) (outV : C.output ≠ v.val) (x : Fin n → Bool) :
    circuitFun n C (x ∘ Equiv.swap u v) = circuitFun n C x := by
  have off (i : Fin n) (hui : i.val ≠ u.val) (hvi : i.val ≠ v.val) :
      (x ∘ Equiv.swap u v) i = x i := by
    simp [Equiv.swap_apply_of_ne_of_ne (fun e => hui (congrArg Fin.val e))
      (fun e => hvi (congrArg Fin.val e))]
  apply eval_of_steps
  · intro g hg t
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hg
    have both := paired j
    rw [hj] at both
    by_cases readU : u.val ∈ g.inputs
    · obtain ⟨ops, size⟩ := mono g hg
      change g.op = .and ∨ g.op = .or at ops
      obtain order | order := two_raw (Fin.val_ne_of_ne uv) size readU (both.mp readU)
      all_goals
        rcases ops with op | op
        all_goals
          simp only [value, order, op, List.map_cons, List.map_nil, raw, Function.comp_apply,
            Equiv.swap_apply_left, Equiv.swap_apply_right]
          cases x u <;> cases x v <;> rfl
    · have readV : v.val ∉ g.inputs := fun h => readU (both.mpr h)
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro k hk
      apply agreeAt
      rintro i rfl
      exact off i (fun e => readU (e ▸ hk)) (fun e => readV (e ▸ hk))
  · intro i eq
    exact off i (fun h => outU (eq.symm.trans h)) (fun h => outV (eq.symm.trans h))

theorem graph_swap (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (mono : Monotone2 C)
    (computes : circuitFun n C = fun x : Fin n → Bool =>
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true))
    {u v : Fin n} (uv : u ≠ v)
    (paired : ∀ j : Fin C.gates.length,
      u.val ∈ (C.gates.get j).inputs ↔ v.val ∈ (C.gates.get j).inputs)
    (x : Fin n → Bool) :
    decide (∃ a b, G.Adj a b ∧ (x ∘ Equiv.swap u v) a = true ∧
        (x ∘ Equiv.swap u v) b = true) =
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) := by
  simpa only [computes] using swap C mono uv paired (output_ne computes u) (output_ne computes v) x

/-- The blocking raw partner may vary from one reader gate to the next. -/
theorem masked_many (C : Circuit) {v : Fin n}
    (out : C.output ≠ v.val) (x y : Fin n → Bool)
    (agree : ∀ i, i ≠ v → x i = y i)
    (blocked : ∀ j : Fin C.gates.length, v.val ∈ (C.gates.get j).inputs →
      ∃ w : Fin n, w ≠ v ∧
      ((C.gates.get j).inputs = [v.val,w.val] ∨ (C.gates.get j).inputs = [w.val,v.val]) ∧
      (((C.gates.get j).op = .and ∧ x w = false) ∨
       ((C.gates.get j).op = .or ∧ x w = true))) :
    circuitFun n C x = circuitFun n C y := by
  apply eval_of_steps
  · intro g hg t
    by_cases hv : v.val ∈ g.inputs
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hg
      have h := blocked j
      rw [hj] at h
      obtain ⟨w,wv,order,op⟩ := h hv
      have wy := (agree w wv).symm
      rcases order with order | order <;> rcases op with ⟨op,b⟩ | ⟨op,b⟩
      all_goals
        simp only [value,order,op,List.map_cons,List.map_nil,raw,wy,b]
        cases x v <;> cases y v <;> rfl
    · apply congrArg g.op.eval
      apply List.map_congr_left
      intro k hk
      apply agreeAt
      rintro i rfl
      exact agree i (fun e => hv (e ▸ hk))
  · rintro i eq
    exact agree i (fun e => out (eq.symm.trans (congrArg Fin.val e)))

/-- Uses of the blocking partner w at other gates are unrestricted. -/
theorem masked (C : Circuit) {v w : Fin n} (vw : v ≠ w)
    (out : C.output ≠ v.val) (x y : Fin n → Bool)
    (agree : ∀ i, i ≠ v → x i = y i)
    (blocked : ∀ j : Fin C.gates.length, v.val ∈ (C.gates.get j).inputs →
      ((C.gates.get j).inputs = [v.val,w.val] ∨ (C.gates.get j).inputs = [w.val,v.val]) ∧
      (((C.gates.get j).op = .and ∧ x w = false) ∨
       ((C.gates.get j).op = .or ∧ x w = true))) :
    circuitFun n C x = circuitFun n C y :=
  masked_many C out x y agree (fun j hj => ⟨w,vw.symm,blocked j hj⟩)

/-- A set of reader gates with one assigned partner per gate has at most one
    distinct partner per direct reader of v. -/
theorem partner_count (C : Circuit) (v : Fin n) (U : Finset (Fin C.gates.length))
    (partner : Fin C.gates.length → Fin n)
    (reads : ∀ j ∈ U, v.val ∈ (C.gates.get j).inputs) :
    (U.image partner).card ≤ Edge606.WeightedPin.readers C v :=
  Finset.card_image_le.trans (Finset.card_le_card (fun j hj =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ j,reads j hj⟩))

end Edge606.TwinReads
