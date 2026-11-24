import OwnershipBase
import RawPartner

namespace Petersen3831.SignedPath

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1490

/-- A path of changing wires. Only the first operand of a NOT carries a signal.
The Boolean index toggles on each NOT and counts its parity. -/
inductive Path (n : Nat) (C : Circuit) (x y : List Bool) : Nat → Bool → Prop
  | input (change : val C x 0 ≠ val C y 0) : Path n C x y 0 false
  | pos {j i : Nat} {s : Bool} (valid : j < C.gates.length)
      (op : (gateAt C j).op = .and ∨ (gateAt C j).op = .or)
      (reads : i ∈ (gateAt C j).inputs) (back : i < n+j)
      (same : val C x i = val C x (n+j))
      (change : val C x (n+j) ≠ val C y (n+j))
      (prior : Path n C x y i s) : Path n C x y (n+j) s
  | neg {j i : Nat} {s : Bool} (valid : j < C.gates.length)
      (op : (gateAt C j).op = .not)
      (reads : (gateAt C j).inputs.head? = some i) (back : i < n+j)
      (flips : val C x (n+j) = !val C x i)
      (change : val C x (n+j) ≠ val C y (n+j))
      (prior : Path n C x y i s) : Path n C x y (n+j) (!s)

private theorem transfers {op : GateOp} (pos : op = .and ∨ op = .or)
    (l : List Nat) (f g : Nat → Bool) (ordered : ∀ i ∈ l, f i = true → g i = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases pos with rfl | rfl <;> simp [GateOp.eval]
  · intro yes i hi
    exact ordered i hi (yes i hi)
  · intro i hi yes
    exact ⟨i, hi, ordered i hi yes⟩

private theorem source {op : GateOp} (pos : op = .and ∨ op = .or)
    (l : List Nat) (f g : Nat → Bool) (hf : op.eval (l.map f) = true)
    (hg : op.eval (l.map g) = false) : ∃ i ∈ l, f i = true ∧ g i = false := by
  by_contra! missing
  have order (i) (hi : i ∈ l) (hit : f i = true) : g i = true := by
    cases eq : g i <;> simp_all
  have := transfers pos l f g order hf
  simp_all

theorem trace {n : Nat} (C : Circuit) (fan : FanInTwo C) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n) (zero : x.getD 0 false = false)
    (only : ∀ i < n, i ≠ 0 → x.getD i false = y.getD i false) (w : Nat)
    (changed : val C x w ≠ val C y w) : Path n C x y w (val C x w) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w < n
    · have xv := val_input (C:=C) hx raw
      have yv := val_input (C:=C) hy raw
      have eq : w = 0 := by
        by_contra h
        exact changed (xv.trans ((only w raw h).trans yv.symm))
      subst w
      rw [xv, zero]
      exact .input changed
    by_cases out : n + C.gates.length ≤ w
    · exact (changed ((val_ge hx out).trans (val_ge hy out).symm)).elim
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt raw)
    have valid : j < C.gates.length := by omega
    let d := gateAt C j
    let f (i : Nat) := if i < n+j then val C x i else false
    let g (i : Nat) := if i < n+j then val C y i else false
    have a : val C x (n+j) = d.op.eval (d.inputs.map f) := val_gate hx valid
    have b : val C y (n+j) = d.op.eval (d.inputs.map g) := val_gate hy valid
    have old {i} (h : f i ≠ g i) : i < n+j := by
      by_contra bad
      simp [f,g,bad] at h
    have hops := (fan d (gateAt_mem valid)).1
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hops
    rcases (show (d.op=.and ∨ d.op=.or) ∨ d.op=.not by tauto) with pos | neg
    · have get : ∃ i ∈ d.inputs, f i = val C x (n+j) ∧ g i = val C y (n+j) := by
        cases xx : val C x (n+j) <;> cases yy : val C y (n+j)
        · exact (changed (xx.trans yy.symm)).elim
        · obtain ⟨i, inps, gy, fx⟩ := source pos d.inputs g f (b.symm.trans yy) (a.symm.trans xx)
          exact ⟨i, inps, fx, gy⟩
        · exact source pos d.inputs f g (a.symm.trans xx) (b.symm.trans yy)
        · exact (changed (xx.trans yy.symm)).elim
      obtain ⟨i, reads, fx, gy⟩ := get
      have diff : f i ≠ g i := fun h => changed (fx.symm.trans (h.trans gy))
      have back := old diff
      simp only [f,g,back,↓reduceIte] at diff fx
      rw [← fx]
      exact .pos valid pos reads back fx changed (ih i back diff)
    · rw [neg] at a b
      cases inputs : d.inputs with
      | nil => simp [inputs, GateOp.eval] at a b; exact (changed (a.trans b.symm)).elim
      | cons i rest =>
        simp [inputs,GateOp.eval] at a b
        have diff : f i ≠ g i := fun h => changed (a.trans ((congrArg Bool.not h).trans b.symm))
        have back := old diff
        simp only [f,g,back,↓reduceIte] at diff a
        rw [a]
        exact .neg valid neg (by change d.inputs.head? = some i; simp [inputs]) back a changed (ih i back diff)

theorem Path.polarity {n C x y w s} (p : Path n C x y w s) (start : val C x 0 = false) :
    val C x w = s := by
  induction p with
  | input => exact start
  | pos _ _ _ _ same _ _ ih => exact same.symm.trans ih
  | neg _ _ _ _ flips _ _ ih => simpa [ih] using flips

theorem Path.odd_not {n C x y w s} (p : Path n C x y w s) (start : val C x 0 = false)
    (odd : s = true) :
    ∃ j < C.gates.length, n+j ≤ w ∧ (gateAt C j).op = .not ∧
      val C x (n+j) = true ∧ val C y (n+j) = false := by
  induction p with
  | input => contradiction
  | pos valid _ _ back _ _ _ ih =>
    obtain ⟨j, hj, le, rest⟩ := ih odd
    exact ⟨j, hj, by omega, rest⟩
  | neg valid op _ _ flips changed prior ih =>
    have yes := flips.trans ((congrArg Bool.not (prior.polarity start)).trans odd)
    exact ⟨_,valid,le_rfl,op,yes, by cases h : val _ _ _ <;> simp_all⟩

private theorem head_member {l : List Nat} {i} (h : l.head? = some i) : i ∈ l := by
  cases l with
  | nil => simp at h
  | cons a rest =>
    have eq : a = i := Option.some.inj h
    simp [eq]

theorem Path.first_bound {n C x y w s k} (p : Path n C x y w s)
    (reader : ∀ j < C.gates.length, 0 ∈ (gateAt C j).inputs → j = k) :
    w = 0 ∨ n+k ≤ w := by
  induction p with
  | input => exact Or.inl rfl
  | pos valid _ reads back _ _ _ ih =>
    right
    rcases ih with rfl | le
    · rw [reader _ valid reads]
    · omega
  | neg valid _ reads back _ _ _ ih =>
    right
    rcases ih with rfl | le
    · rw [reader _ valid (head_member reads)]
    · omega

theorem Path.odd_after {n C x y w s k} (p : Path n C x y w s)
    (start : val C x 0 = false) (odd : s = true)
    (reader : ∀ j < C.gates.length, 0 ∈ (gateAt C j).inputs → j = k)
    (positive : (gateAt C k).op ≠ .not) :
    ∃ j < C.gates.length, k < j ∧ n+j ≤ w ∧ (gateAt C j).op = .not ∧
      val C x (n+j) = true ∧ val C y (n+j) = false := by
  induction p with
  | input => contradiction
  | pos _ _ _ back _ _ _ ih =>
    obtain ⟨j, bound, after, le, rest⟩ := ih odd
    exact ⟨j, bound, after, by omega, rest⟩
  | neg valid op reads back flips changed prior ih =>
    have yes := flips.trans ((congrArg Bool.not (prior.polarity start)).trans odd)
    rcases prior.first_bound reader with src | tail
    · have eq := reader _ valid (src ▸ head_member reads)
      exact (positive (eq ▸ op)).elim
    · exact ⟨_,valid,by omega,le_rfl,op,yes, by cases h : val _ _ _ <;> simp_all⟩

open RawPartner in
theorem output_path (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x : Input, circuitFun 9 C (flip x) = graph x)
    (m : Fin 512) (sens : sensitive m) :
    Path 9 C (List.ofFn (row m false)) (List.ofFn (row m true)) C.output true := by
  have table : ∀ t : Fin 512, sensitive t →
      graph (row t false) = false ∧ graph (row t true) = true := by decide +kernel
  obtain ⟨lo,hi⟩ := table m sens
  have flipRow (b : Bool) : flip (row m b) = row m (!b) := by
    funext i
    by_cases h : i=0 <;> simp [RawPartner.flip,row,h]
  have xv : val C (List.ofFn (row m false)) C.output = true := by
    change circuitFun 9 C (row m false) = true
    rw [← show flip (row m true) = row m false from flipRow true]
    exact (correct _).trans hi
  have yv : val C (List.ofFn (row m true)) C.output = false := by
    change circuitFun 9 C (row m true) = false
    rw [← show flip (row m false) = row m true from flipRow false]
    exact (correct _).trans lo
  have p := trace (n:=9) C fan (List.ofFn (row m false)) (List.ofFn (row m true))
    (by simp) (by simp) (by rfl) (by
      intro i hi ne
      have nonzero : (⟨i, hi⟩ : Fin 9) ≠ 0 := fun h => ne (congrArg Fin.val h)
      simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left hi,Option.getD_some,
        row,nonzero,↓reduceIte])
    C.output (fun eq => Bool.noConfusion (xv.symm.trans (eq.trans yv)))
  rwa [xv] at p

open RawPartner in
theorem post_reader_not (C : Circuit) (fan : FanInTwo C) {k a : Nat}
    (uq : unique C) (hk : k < C.gates.length) (args : (gateAt C k).inputs = [0,a])
    (op : (gateAt C k).op = .and ∨ (gateAt C k).op = .or)
    (correct : ∀ x : Input, circuitFun 9 C (RawPartner.flip x) = graph x)
    (m : Fin 512) (sens : sensitive m) :
    ∃ j < C.gates.length, k < j ∧ 9+j ≤ C.output ∧ (gateAt C j).op = .not ∧
      val C (List.ofFn (row m false)) (9+j) = true ∧
      val C (List.ofFn (row m true)) (9+j) = false := by
  apply (output_path C fan correct m sens).odd_after _ rfl
  · exact fun j hj h => reader_index uq hk (by simp [args]) hj h
  · rcases op with h | h <;> simp [h]
  · rw [val_input (n:=9) (by simp) (by decide)]
    rfl

end Petersen3831.SignedPath

#print axioms Petersen3831.SignedPath.output_path
#print axioms Petersen3831.SignedPath.Path.odd_not
#print axioms Petersen3831.SignedPath.post_reader_not
