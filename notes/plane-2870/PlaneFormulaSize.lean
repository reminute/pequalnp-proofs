import Mathlib.Data.List.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.BigOperators

/-!
# Sparse point-line incidence requires at least one formula leaf per incident flag

For a regular incidence structure of order q > 1, any binary monotone formula
that accepts each incident pair and rejects every negative input with at most
q selected lines has at least n * (q + 1) variable leaves. Variables may
appear repeatedly. The final statement is PlaneKW.unrestricted_formula_bound.

The proof was assembled during the investigation of L-meta-2870. The sections
below identify the local source of each argument. All library dependencies are
listed above.
-/

/-!
## Binary monotone formulas

The formula syntax and Boolean evaluation are shared with the local read-once analysis.

Local proof source: PlaneFormulaCore.lean.
-/

inductive PlaneFormula (α : Type) where
  | leaf (a : α)
  | bot
  | or (l r : PlaneFormula α)
  | and (l r : PlaneFormula α)

namespace PlaneFormula

def eval {α : Type} (v : α → Bool) : PlaneFormula α → Bool
  | .leaf a => v a
  | .bot => false
  | .or l r => eval v l || eval v r
  | .and l r => eval v l && eval v r

def leaves {α : Type} : PlaneFormula α → List α
  | .leaf a => [a]
  | .bot => []
  | .or l r | .and l r => l.leaves ++ r.leaves

end PlaneFormula

/-!
## The Karchmer-Wigderson rank bound for a formula

The positive rows split at an OR node and the negative columns split at an AND node. Matrix rank is subadditive under these splits.

Local proof source: PlaneFormulaRankKW.lean.
-/

open Matrix

namespace PlaneKW

theorem rank_sum_le {ι κ : Type} [Fintype ι] [Fintype κ] (A B : Matrix ι κ ℝ) :
    (A+B).rank ≤ A.rank+B.rank := by
  change Module.finrank ℝ (LinearMap.range (A+B).mulVecLin) ≤ _
  refine (Submodule.finrank_mono ?_).trans
    (Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range A.mulVecLin)
      (LinearMap.range B.mulVecLin))
  rintro _ ⟨x,rfl⟩
  rw [Matrix.mulVecLin_add,LinearMap.add_apply]
  exact Submodule.add_mem_sup ⟨x,rfl⟩ ⟨x,rfl⟩

def block {ι κ : Type} (M : Matrix ι κ ℝ) (r : ι → Bool) (c : κ → Bool) :
    Matrix ι κ ℝ := fun i j => if r i && c j then M i j else 0

theorem formula_rank {α ι κ : Type} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) (pos : ι → α → Bool) (neg : κ → α → Bool)
    (leafBound : ∀ (a : α) (r : ι → Bool) (c : κ → Bool),
      (∀ i, r i = true → pos i a = true) →
      (∀ j, c j = true → neg j a = false) → (block M r c).rank ≤ 1)
    (t : PlaneFormula α) (accept : ∀ i, t.eval (pos i) = true)
    (reject : ∀ j, t.eval (neg j) = false) : M.rank ≤ t.leaves.length := by
  have part (u : PlaneFormula α) (r : ι → Bool) (c : κ → Bool)
      (right : ∀ i, r i = true → u.eval (pos i) = true)
      (left : ∀ j, c j = true → u.eval (neg j) = false) :
      (block M r c).rank ≤ u.leaves.length := by
    induction u generalizing r c with
    | bot =>
      have zero : block M r c = 0 := by
        ext i j
        have off : r i = false := by
          cases e : r i
          · rfl
          · have impossible : false = true := right i e
            contradiction
        simp [block,off]
      simp [zero]
    | leaf a => exact leafBound a r c right left
    | or a b ha hb =>
      let z (i : ι) := a.eval (pos i)
      let r₁ (i : ι) := r i && z i
      let r₂ (i : ι) := r i && !z i
      have splitM : block M r c = block M r₁ c + block M r₂ c := by
        ext i j
        by_cases e : z i = true <;> simp [block,r₁,r₂,e,Matrix.add_apply]
      have h₁ := ha r₁ c (fun i h => (Bool.and_eq_true_iff.mp h).2)
        (fun j h => (Bool.or_eq_false_iff.mp (left j h)).1)
      have h₂ := hb r₂ c (fun i h => by
        obtain ⟨hr,hz⟩ := Bool.and_eq_true_iff.mp h
        rcases Bool.or_eq_true_iff.mp (right i hr) with yes | yes
        · change (!z i) = true at hz
          have e : z i = true := yes
          simp [e] at hz
        · exact yes) (fun j h => (Bool.or_eq_false_iff.mp (left j h)).2)
      rw [splitM]
      exact (rank_sum_le _ _).trans (by simpa [PlaneFormula.leaves] using Nat.add_le_add h₁ h₂)
    | and a b ha hb =>
      let z (j : κ) := a.eval (neg j)
      let c₁ (j : κ) := c j && !z j
      let c₂ (j : κ) := c j && z j
      have splitM : block M r c = block M r c₁ + block M r c₂ := by
        ext i j
        by_cases e : z j = true <;> simp [block,c₁,c₂,e,Matrix.add_apply]
      have h₁ := ha r c₁ (fun i h => (Bool.and_eq_true_iff.mp (right i h)).1)
        (fun j h => by
          have e : (!z j) = true := (Bool.and_eq_true_iff.mp h).2
          simpa [z] using e)
      have h₂ := hb r c₂ (fun i h => (Bool.and_eq_true_iff.mp (right i h)).2)
        (fun j h => by
          obtain ⟨hc,hz⟩ := Bool.and_eq_true_iff.mp h
          have v := left j hc
          change (z j && b.eval (neg j)) = false at v
          simpa [hz] using v)
      rw [splitM]
      exact (rank_sum_le _ _).trans (by simpa [PlaneFormula.leaves] using Nat.add_le_add h₁ h₂)
  have h := part t (fun _ => true) (fun _ => true) (fun i _ => accept i) (fun j _ => reject j)
  have eqn : block M (fun _ => true) (fun _ => true) = M := by ext; rfl
  simpa only [eqn] using h

end PlaneKW

/-!
## Positive and negative tests for incident flags

For a flag (p,l), the negative test selects the other points of l and the other lines through p. At each formula leaf the corresponding restricted matrix has rank at most one.

Local proof source: PlaneFormulaRankGeometry.lean.
-/

open Finset Matrix

namespace PlaneKW

variable {n q : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
abbrev Flag := {e : Fin n × Fin n // I e.1 e.2}

def pos (e : Flag I) : Fin (n+n) → Bool :=
  Fin.addCases (fun p => decide (p = e.1.1)) (fun l => decide (l = e.1.2))

def neg (e : Flag I) : Fin (n+n) → Bool :=
  Fin.addCases (fun p => decide (I p e.1.2 ∧ p ≠ e.1.1))
    (fun l => decide (I e.1.1 l ∧ l ≠ e.1.2))

omit [DecidableRel I] in
theorem pos_p (f : Flag I) (p : Fin n) :
    pos I f (Fin.castAdd n p) = decide (p = f.1.1) := Fin.addCases_left _
omit [DecidableRel I] in
theorem pos_l (f : Flag I) (l : Fin n) :
    pos I f (Fin.natAdd n l) = decide (l = f.1.2) := Fin.addCases_right _
theorem neg_p (f : Flag I) (p : Fin n) :
    neg I f (Fin.castAdd n p) = decide (I p f.1.2 ∧ p ≠ f.1.1) := Fin.addCases_left _
theorem neg_l (f : Flag I) (l : Fin n) :
    neg I f (Fin.natAdd n l) = decide (I f.1.1 l ∧ l ≠ f.1.2) := Fin.addCases_right _

noncomputable def flagMatrix : Matrix (Flag I) (Flag I) ℝ :=
  fun e f => if e.1.1 = f.1.1 ∨ e.1.2 = f.1.2 then 1 else 0

omit [DecidableRel I] in
theorem pos_is_flag (e : Flag I) :
    pos I e = (fun i => decide (i = Fin.castAdd n e.1.1 ∨ i = Fin.natAdd n e.1.2)) := by
  funext i
  have sep (a b : Fin n) : Fin.castAdd n a ≠ Fin.natAdd n b := by
    intro h
    have hv := congrArg Fin.val h
    change a.val = n + b.val at hv
    omega
  refine Fin.addCases (fun p => ?_) (fun l => ?_) i
  · simp only [pos_p,Fin.castAdd_inj,sep,or_false]
  · rw [pos_l]
    apply decide_eq_decide.mpr
    constructor
    · intro h
      exact Or.inr (congrArg _ h)
    · rintro (h | h)
      · exact (sep _ _ h.symm).elim
      · apply Fin.ext
        have hv := congrArg Fin.val h
        change n + l.val = n + e.1.2.val at hv
        omega

theorem neg_line_count (row : ∀ p, (univ.filter (I p)).card = q+1) (f : Flag I) :
    Fintype.card {l : Fin n // neg I f (Fin.natAdd n l) = true} = q := by
  let S := univ.filter (I f.1.1)
  have member : f.1.2 ∈ S := mem_filter.mpr ⟨mem_univ _, f.2⟩
  let eqv : {l : Fin n // neg I f (Fin.natAdd n l) = true} ≃ ↥(S.erase f.1.2) :=
    Equiv.subtypeEquivRight (fun l => by rw [neg_l]; simp [S,and_comm])
  rw [Fintype.card_congr eqv,Fintype.card_coe,card_erase_of_mem member]
  simp [S,row]

theorem neg_no_edge (uniq : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) (f : Flag I) :
    ¬∃ p l, I p l ∧ neg I f (Fin.castAdd n p) = true ∧ neg I f (Fin.natAdd n l) = true := by
  rintro ⟨p,l,incident,hp,hl⟩
  rw [neg_p] at hp
  rw [neg_l] at hl
  replace hp := of_decide_eq_true hp
  replace hl := of_decide_eq_true hl
  exact hl.2 ((uniq p f.1.1 hp.2).unique ⟨incident,hl.1⟩ ⟨hp.1,f.2⟩)

theorem flag_leaf_rank (a : Fin (n+n)) (r : Flag I → Bool) (c : Flag I → Bool)
    (posOn : ∀ i, r i = true → pos I i a = true)
    (negOff : ∀ j, c j = true → neg I j a = false) :
    (block (flagMatrix I) r c).rank ≤ 1 := by
  -- On a monochromatic leaf rectangle each column is constant on the selected rows.
  have rows (pick : Flag I → Prop) [DecidablePred pick]
      (const : ∀ i j, r i = true → c j = true →
        (i.1.1 = j.1.1 ∨ i.1.2 = j.1.2 ↔ pick j)) :
      (block (flagMatrix I) r c).rank ≤ 1 := by
    let u (i : Flag I) : ℝ := if r i then 1 else 0
    let v (j : Flag I) : ℝ := if c j = true ∧ pick j then 1 else 0
    have eqn : block (flagMatrix I) r c = vecMulVec u v := by
      ext i j
      by_cases hr : r i = true
      · by_cases hc : c j = true
        · simp [block, flagMatrix, Matrix.vecMulVec, u,v,hr,hc,const i j hr hc]
        · simp [block, Matrix.vecMulVec,u,v,hr,hc]
      · simp [block, Matrix.vecMulVec,u,v,hr]
    rw [eqn]
    exact Matrix.rank_vecMulVec_le _ _
  revert posOn negOff
  refine Fin.addCases (fun p => ?_) (fun l => ?_) a
  · intro hp hn
    apply rows (fun j => p = j.1.1)
    intro i j hi hj
    have pi : p = i.1.1 := by simpa only [pos_p,decide_eq_true_eq] using hp i hi
    have off := hn j hj
    rw [neg_p] at off
    simp at off
    constructor
    · rintro (h | h)
      · exact pi.trans h
      · exact off (by simpa [pi,h] using i.2)
    · exact fun h => Or.inl (pi.symm.trans h)
  · intro hp hn
    apply rows (fun j => l = j.1.2)
    intro i j hi hj
    have li : l = i.1.2 := by simpa only [pos_l,decide_eq_true_eq] using hp i hi
    have off := hn j hj
    rw [neg_l] at off
    simp at off
    constructor
    · rintro (h | h)
      · exact off (by simpa [li,h] using i.2)
      · exact li.trans h
    · exact fun h => Or.inr (li.symm.trans h)

theorem formula_flag_rank (row : ∀ p, (univ.filter (I p)).card = q+1)
    (uniq : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (t : PlaneFormula (Fin (n+n)))
    (accept : ∀ p l, I p l → t.eval
      (fun i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l)) = true)
    (sound : ∀ x : Fin (n+n) → Bool, Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} ≤ q →
      (¬∃ p l, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true) → t.eval x = false) :
    (flagMatrix I).rank ≤ t.leaves.length := by
  apply formula_rank _ (pos I) (neg I) (flag_leaf_rank I) t
  · intro i
    rw [pos_is_flag]
    exact accept i.1.1 i.1.2 i.2
  · intro j
    exact sound _ (neg_line_count I row j).le (neg_no_edge I uniq j)

end PlaneKW

/-!
## Full rank of the flag matrix

The local full-rank proof sums a kernel vector over point stars and line stars, then uses uniqueness of a line through two points.

Local proof source: PlaneFormulaRankFull.lean.
-/

namespace PlaneFormulaRankFull

open Finset Matrix

abbrev Flag {n : ℕ} (I : Fin n → Fin n → Prop) := {e : Fin n × Fin n // I e.1 e.2}

def flagMatrix {n : ℕ} (I : Fin n → Fin n → Prop) : Matrix (Flag I) (Flag I) ℝ :=
  fun e f => if e.val.1 = f.val.1 ∨ e.val.2 = f.val.2 then 1 else 0

variable {n q : ℕ} {I : Fin n → Fin n → Prop} [DecidableRel I]

def extend (x : Flag I → ℝ) (p l : Fin n) : ℝ := if h : I p l then x ⟨(p,l),h⟩ else 0

theorem flag_sum (x : Flag I → ℝ) (c : Fin n → Fin n → ℝ) :
    ∑ e, c e.val.1 e.val.2 * x e = ∑ p, ∑ l, c p l * extend x p l := by
  classical
  have split := Fintype.sum_subtype_add_sum_subtype
    (fun e : Fin n × Fin n => I e.1 e.2) (fun e => c e.1 e.2 * extend x e.1 e.2)
  rw [Fintype.sum_prod_type] at split
  have yes (e : Flag I) : extend x e.val.1 e.val.2 = x e := by simp [extend,e.property]
  have no (e : {e : Fin n × Fin n // ¬I e.1 e.2}) : extend x e.val.1 e.val.2 = 0 := by
    simp [extend,e.property]
  simpa only [yes,no,mul_zero,sum_const_zero,add_zero] using split

theorem crossed_sum (w : Fin n → Fin n → ℝ) (p l : Fin n) :
    (∑ r, ∑ k, if p = r ∨ l = k then w r k else 0) =
      (∑ k, w p k) + (∑ r, w r l) - w p l := by
  have split (r k : Fin n) : (if p=r ∨ l=k then w r k else 0) =
      (if p=r then w r k else 0) + (if l=k then w r k else 0) -
        (if p=r then (if l=k then w r k else 0) else 0) := by
    by_cases a : p=r <;> by_cases b : l=k <;> simp [a,b]
  simp_rw [split,sum_sub_distrib,sum_add_distrib]
  simp [sum_ite_irrel]

theorem sum_constant {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] (a : ℝ) :
    (∑ i, if P i then a else 0) = (Fintype.card {i // P i} : ℝ) * a := by
  classical
  rw [← sum_filter]
  simp [Fintype.card_subtype]

theorem square_incidence (rows : ∀ p, Fintype.card {l // I p l} = q+1)
    (join : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) (a : Fin n → ℝ) (p : Fin n) :
    (∑ l, if I p l then ∑ r, if I r l then a r else 0 else 0) =
      (q : ℝ) * a p + ∑ r, a r := by
  classical
  have both (l : Fin n) : (if I p l then ∑ r, if I r l then a r else 0 else 0) =
      ∑ r, if I p l ∧ I r l then a r else 0 := by by_cases h : I p l <;> simp [h]
  simp_rw [both]
  rw [sum_comm]
  have factor (r : Fin n) : (∑ l, if I p l ∧ I r l then a r else 0) =
      (if p=r then (q : ℝ)*a r else 0) + a r := by
    by_cases equal : p=r
    · subst r
      simp only [and_self,ite_true]
      rw [sum_constant,rows]
      push_cast
      ring
    · obtain ⟨k,hk,unique⟩ := join p r equal
      have one (l : Fin n) : (I p l ∧ I r l) ↔ k=l :=
        ⟨fun h => (unique l h).symm,fun e => e ▸ hk⟩
      simp [one,equal]
  simp_rw [factor]
  simp [sum_add_distrib]

theorem regular_kernel (hq : 1 < q)
    (rows : ∀ p, Fintype.card {l // I p l} = q+1)
    (cols : ∀ l, Fintype.card {p // I p l} = q+1)
    (join : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (x : Flag I → ℝ) (hx : (flagMatrix I).mulVec x = 0) : x = 0 := by
  classical
  let w := extend x
  let a (p : Fin n) := ∑ l, w p l
  let b (l : Fin n) := ∑ p, w p l
  have flow (p l : Fin n) (inc : I p l) : w p l = a p + b l := by
    have z := congrFun hx (⟨(p,l),inc⟩ : Flag I)
    change (∑ f : Flag I, (if p = f.val.1 ∨ l = f.val.2 then (1 : ℝ) else 0) * x f) = 0 at z
    rw [flag_sum x (fun r k => if p=r ∨ l=k then 1 else 0)] at z
    simp only [ite_mul,one_mul,zero_mul] at z
    rw [crossed_sum] at z
    change a p + b l - w p l = 0 at z
    linarith
  have walt (p l : Fin n) : w p l = if I p l then a p + b l else 0 := by
    by_cases h : I p l
    · simp [h,flow p l h]
    · simp [w,extend,h]
  have sumA (p : Fin n) : (q : ℝ)*a p + (∑ l, if I p l then b l else 0) = 0 := by
    have sp (l : Fin n) : w p l = (if I p l then a p else 0) + (if I p l then b l else 0) := by
      rw [walt]; by_cases h : I p l <;> simp [h]
    have e : a p = ∑ l, w p l := rfl
    simp_rw [sp] at e
    rw [sum_add_distrib,sum_constant,rows] at e
    push_cast at e
    linarith
  have sumB (l : Fin n) : (q : ℝ)*b l + (∑ r, if I r l then a r else 0) = 0 := by
    have sp (r : Fin n) : w r l = (if I r l then b l else 0) + (if I r l then a r else 0) := by
      rw [walt]; by_cases h : I r l <;> simp [h,add_comm]
    have e : b l = ∑ r, w r l := rfl
    simp_rw [sp] at e
    rw [sum_add_distrib,sum_constant,cols] at e
    push_cast at e
    linarith
  have totals : ∑ p, a p = ∑ l, b l := sum_comm
  have sum0 : ∑ p, a p = 0 := by
    have step : (∑ p, ∑ l, if I p l then b l else 0) = ((q : ℝ)+1) * ∑ l, b l := by
      rw [sum_comm,mul_sum]
      apply sum_congr rfl
      intro l _
      rw [sum_constant,cols]
      push_cast
      rfl
    have e := congrArg (fun f : Fin n → ℝ => ∑ p, f p) (funext sumA)
    change (∑ p, ((q : ℝ)*a p + ∑ l, if I p l then b l else 0)) = ∑ _ : Fin n, (0 : ℝ) at e
    rw [sum_add_distrib, ← mul_sum,step,← totals] at e
    simp only [sum_const_zero] at e
    have pos : 0 < 2*(q : ℝ)+1 := by positivity
    apply (mul_eq_zero.mp (show (2*(q : ℝ)+1) * (∑ p, a p) = 0 by linarith)).resolve_left pos.ne'
  have allA (p : Fin n) : a p = 0 := by
    have swap (l : Fin n) : (if I p l then ∑ r, if I r l then a r else 0 else 0) =
        -(q : ℝ)*(if I p l then b l else 0) := by
      by_cases h : I p l
      · simp only [ite_eq_left h]
        linarith [sumB l]
      · simp [h]
    have e := square_incidence rows join a p
    simp_rw [swap] at e
    rw [← mul_sum,sum0,add_zero] at e
    have sp : (∑ l, if I p l then b l else 0) = -(q : ℝ)*a p := by linarith [sumA p]
    rw [sp] at e
    have hreal : 1 < (q : ℝ) := by exact_mod_cast hq
    have pos : 0 < (q : ℝ)*((q : ℝ)-1) := mul_pos (by linarith) (by linarith)
    apply (mul_eq_zero.mp (show (q : ℝ)*((q : ℝ)-1) * a p = 0 by linarith)).resolve_left pos.ne'
  have allB (l : Fin n) : b l = 0 := by
    have e := sumB l
    simp [allA] at e
    exact e.resolve_left (by omega)
  funext e
  obtain ⟨⟨p,l⟩,inc⟩ := e
  simpa [w,extend,inc,allA,allB] using flow p l inc

theorem full_rank (hq : 1 < q)
    (rows : ∀ p, Fintype.card {l // I p l} = q+1)
    (cols : ∀ l, Fintype.card {p // I p l} = q+1)
    (join : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) :
    (flagMatrix I).rank = Fintype.card (Flag I) := by
  classical
  apply Matrix.rank_of_isUnit
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y e
  apply sub_eq_zero.mp
  apply regular_kernel hq rows cols join
  simp [Matrix.mulVec_sub,e]

end PlaneFormulaRankFull

/-!
## The formula size bound

The flag count converts full rank into the lower bound on leaf occurrences.

Local proof source: PlaneFormulaRankLower.lean.
-/

namespace PlaneKW

open Finset

variable {n q : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]

theorem card_flags (rows : ∀ p, Fintype.card {l // I p l} = q+1) :
    Fintype.card (Flag I) = n*(q+1) := by
  let e : Flag I ≃ (p : Fin n) × {l // I p l} :=
    { toFun := fun f => ⟨f.1.1,⟨f.1.2,f.2⟩⟩
      invFun := fun f => ⟨(f.1,f.2.val), f.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e,Fintype.card_sigma]
  simp [rows]

theorem unrestricted_formula_bound (hq : 1 < q)
    (rows : ∀ p, Fintype.card {l // I p l} = q+1)
    (cols : ∀ l, Fintype.card {p // I p l} = q+1)
    (uniq : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (t : PlaneFormula (Fin (n+n)))
    (accept : ∀ p l, I p l → t.eval
      (fun i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l)) = true)
    (sound : ∀ x : Fin (n+n) → Bool, Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} ≤ q →
      (¬∃ p l, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true) → t.eval x = false) :
    n*(q+1) ≤ t.leaves.length := by
  have reg (p : Fin n) : (univ.filter (I p)).card = q+1 := by
    rw [← Fintype.card_coe]
    exact (Fintype.card_congr (Equiv.subtypeEquivRight (fun l => by simp))).trans (rows p)
  have rankBound := formula_flag_rank I reg uniq t accept sound
  change (PlaneFormulaRankFull.flagMatrix I).rank ≤ t.leaves.length at rankBound
  rw [PlaneFormulaRankFull.full_rank hq rows cols uniq] at rankBound
  exact (card_flags I rows).symm.le.trans rankBound

theorem size_of_unfold {s q n leaves : ℕ} (floor : n*(q+1) ≤ leaves)
    (unfolded : leaves ≤ 100*s+1) : n*q ≤ 100*s := by
  rw [Nat.mul_add,Nat.mul_one] at floor
  by_cases h : n = 0
  · simp [h]
  · omega

end PlaneKW
