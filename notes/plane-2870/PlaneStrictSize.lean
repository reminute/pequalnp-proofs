import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PEqualNP.Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.List.Count
import Mathlib.Data.Fintype.Basic

-- Projective-plane circuit size bound, by reminute.
-- The initial graph and plane estimates, through linearLower, are from KainanP's
-- companion to open-goat/pequalnp-proofs PR 7096 (head 9838826d943184d843ad47bc109e77c1741087bc).
-- That argument credits Itay Raveh (PR 728) and JaviSoto (PR 5439).
-- The equality context below refactors their graph and incidence arguments.
-- The equality analysis, formula extraction, incidence counting, and the
-- final strict bound are the contributions of this companion.

-- Prior graph and plane bounds
section
namespace Plane2866Graph

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

def Next (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ p g, C.gates[p]? = some g ∧ b = n+p ∧ a ∈ g.inputs

def Live (n : ℕ) (C : Circuit) (i : ℕ) : Prop :=
  ReflTransGen (Next n C) i C.output

def LNext (n : ℕ) (C : Circuit) (a b : ℕ) : Prop := Next n C a b ∧ Live n C b

def Trace (n : ℕ) (C : Circuit) (P : ℕ → Prop) (i j : ℕ) : Prop :=
  ReflTransGen (fun a b => P a ∧ LNext n C a b) i j

theorem next_le {n : ℕ} {C : Circuit} {a b : ℕ} (h : ReflTransGen (Next n C) a b) :
    a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.1.le

theorem trace_le {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.2.1.1.le

theorem live_before {n : ℕ} {C : Circuit} {a b : ℕ} (hn : Next n C a b) (h : Live n C b) :
    Live n C a := (ReflTransGen.single hn).trans h

theorem trace_start {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) (hb : P b) : P a := by
  rcases h.cases_head with rfl | ⟨_, hs, _⟩
  · exact hb
  · exact hs.1

theorem align {n : ℕ} {C : Circuit} {P Q : ℕ → Prop} {v b : ℕ}
    (p : Trace n C P v b)
    (unique : ∀ a j j', a < b → P a → LNext n C a j → LNext n C a j' → j = j') :
    ∀ d, Trace n C Q v d → (d < b ∧ P d) ∨ Trace n C Q b d := by
  induction p using ReflTransGen.head_induction_on with
  | refl =>
    intro d q
    exact Or.inr q
  | head hp pt ih =>
    intro d q
    have hlt := hp.2.1.1.trans_le (trace_le pt)
    rcases q.cases_head with rfl | ⟨j, hq, qt⟩
    · exact Or.inl ⟨hlt, hp.1⟩
    · have e := unique _ _ _ hlt hp.1 hp.2 hq.2
      subst j
      exact ih _ qt

theorem difference {n : ℕ} (C : Circuit) (x y : Fin n → Bool) :
    ∀ j, Live n C j → val C x j ≠ val C y j →
      ∃ i : Fin n, x i ≠ y i ∧ Trace n C (fun a => val C x a ≠ val C y a) i.val j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hd
    by_cases hin : j < n
    · let i : Fin n := ⟨j,hin⟩
      exact ⟨i, by simpa only [← val_input C x i, ← val_input C y i] using hd, .refl⟩
    have hb : j < n+C.gates.length := by
      by_contra! he
      exact hd ((val_beyond C x he).trans (val_beyond C y he).symm)
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hdiff : ∃ i ∈ g.inputs, i < n+p ∧ val C x i ≠ val C y i := by
      by_contra! hn
      apply hd
      rw [val_gate C x hg, val_gate C y hg]
      apply congrArg _
      apply List.map_congr_left
      intro i hi
      by_cases hj : i < n+p
      · simp [operand, hj, hn i hi hj]
      · simp [operand, hj]
    obtain ⟨a, ha, hlt, ha'⟩ := hdiff
    have hs : Next n C a (n+p) := ⟨hlt,p,g,hg,rfl,ha⟩
    obtain ⟨i, hi, hpath⟩ := ih a hlt (live_before hs hj) ha'
    exact ⟨i, hi, hpath.tail ⟨ha',hs,hj⟩⟩

end Plane2866Graph


namespace Plane2866Graph

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit}

theorem acts_mono (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ j, val C x j = true → val C y j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    by_cases hin : j < n
    · let i : Fin n := ⟨j, hin⟩
      simpa only [← val_input C x i, ← val_input C y i] using hxy i (by
        simpa only [← val_input C x i] using hj)
    by_cases hgt : n + C.gates.length ≤ j
    · rw [val_beyond C x hgt] at hj
      contradiction
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hgate := (hC g (List.mem_of_getElem? hg)).1
    have hm (a : ℕ) : operand C x (n+p) a = true → operand C y (n+p) a = true := by
      by_cases ha : a < n+p
      · simp only [operand, ite_eq_left ha]
        exact ih a ha
      · simp [operand, ha]
    rw [val_gate C x hg] at hj
    rw [val_gate C y hg]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgate
    rcases hgate with h | h
    · simp only [h, GateOp.eval, List.all_map, Function.comp_apply, id, List.all_eq_true] at hj ⊢
      exact fun a ha => hm a (hj a ha)
    · simp only [h, GateOp.eval, List.any_map, Function.comp_apply, id, List.any_eq_true] at hj ⊢
      obtain ⟨a, ha, he⟩ := hj
      exact ⟨a, ha, hm a he⟩

def point (s : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ s)

theorem point_mono {s t : Finset (Fin n)} (h : s ⊆ t) :
    ∀ i, point s i = true → point t i = true := by
  intro i hi
  simpa only [point, decide_eq_true_eq] using h (by simpa only [point, decide_eq_true_eq] using hi)

theorem point_insert {s : Finset (Fin n)} {v u : Fin n} (h : u ≠ v) :
    point (insert v s) u = point s u := by simp [point, h]

def Carries (C : Circuit) (v : Fin n) (a : ℕ) : Prop :=
  val C (point {v}) a ≠ val C (point (∅ : Finset (Fin n))) a

theorem carries_iff (hC : Monotone2 C) {v : Fin n} {a : ℕ} :
    Carries C v a ↔
      val C (point {v}) a = true ∧ val C (point (∅ : Finset (Fin n))) a = false := by
  have hm := acts_mono hC (point_mono (Finset.empty_subset {v})) a
  unfold Carries
  cases ha : val C (point {v}) a <;>
    cases hb : val C (point (∅ : Finset (Fin n))) a <;> simp_all

theorem singleton_path {v : Fin n} {a : ℕ} (ha : Live n C a) (hd : Carries C v a) :
    Trace n C (Carries C v) v.val a := by
  obtain ⟨i, hi, hpath⟩ := difference C (point {v}) (point ∅) a ha hd
  have e : i = v := by
    by_contra h
    exact hi (by simp [point, h])
  exact e ▸ hpath

theorem influence {v : Fin n} {P : ℕ → Prop} {b j : ℕ} {x y : Fin n → Bool}
    (path : Trace n C P v.val b)
    (unique : ∀ a k k', a < b → P a → LNext n C a k → LNext n C a k' → k = k')
    (agrees : ∀ i, i ≠ v → x i = y i) (hj : Live n C j) (hd : val C x j ≠ val C y j) :
    (j < b ∧ P j) ∨ (b ≤ j ∧ val C x b ≠ val C y b) := by
  obtain ⟨i, hi, trace⟩ := difference C x y j hj hd
  have e : i = v := by
    by_contra h
    exact hi (agrees i h)
  subst i
  rcases align path unique j trace with ha | hb
  · exact Or.inl ha
  · exact Or.inr ⟨trace_le hb, trace_start hb hd⟩

noncomputable def readers (n : ℕ) (C : Circuit) (a : ℕ) : Finset ℕ :=
  open Classical in (Finset.range (n+C.gates.length)).filter (fun b => LNext n C a b)

theorem next_in_range {a b : ℕ} (h : Next n C a b) : b < n+C.gates.length := by
  obtain ⟨_,p,g,hg,rfl,_⟩ := h
  exact Nat.add_lt_add_left (List.getElem?_eq_some_iff.1 hg).1 n

theorem mem_readers {a b : ℕ} : b ∈ readers n C a ↔ LNext n C a b := by
  classical
  unfold readers
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨next_in_range h.1, h⟩⟩

def Branch (n : ℕ) (C : Circuit) (a : ℕ) : Prop := 2 ≤ (readers n C a).card

theorem nonbranch_unique {a j j' : ℕ} (h : ¬ Branch n C a)
    (hj : LNext n C a j) (hj' : LNext n C a j') : j = j' := by
  apply Finset.card_le_one_iff.1 (show (readers n C a).card ≤ 1 from by
    unfold Branch at h; omega) (mem_readers.2 hj) (mem_readers.2 hj')

def Eligible (C : Circuit) (v : Fin n) : Prop := ∃ b, Live n C b ∧ Carries C v b ∧ Branch n C b

noncomputable def firstBranch (C : Circuit) (v : Fin n) (h : Eligible C v) : ℕ := by
  classical exact Nat.find h

theorem firstBranch_spec (v : Fin n) (h : Eligible C v) :
    Live n C (firstBranch C v h) ∧ Carries C v (firstBranch C v h) ∧ Branch n C (firstBranch C v h) := by
  classical exact Nat.find_spec h

theorem firstBranch_unique (v : Fin n) (h : Eligible C v) :
    ∀ a j j', a < firstBranch C v h → Carries C v a → LNext n C a j → LNext n C a j' → j = j' := by
  classical
  intro a j j' hl hc hj hj'
  apply nonbranch_unique _ hj hj'
  intro hb
  exact (Nat.not_le_of_gt hl) (Nat.find_min' h ⟨live_before hj.1 hj.2,hc,hb⟩)

theorem no_eligible_unique {v : Fin n} (h : ¬ Eligible C v) :
    ∀ a j j', Carries C v a → LNext n C a j → LNext n C a j' → j = j' := by
  intro a j j' hc hj hj'
  exact nonbranch_unique (fun hb => h ⟨a,live_before hj.1 hj.2,hc,hb⟩) hj hj'

end Plane2866Graph


namespace Plane2866Graph

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}

-- The graph and live-wire lemmas are adapted from Itay Raveh, PR 728.
-- Here only the two-input tests are required. Positive tests extend to supersets by monotonicity.
def GraphEval (C : Circuit) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v w : Fin n, C.eval (List.ofFn fun i => decide (i=v ∨ i=w)) = true ↔ G.Adj v w

theorem point_pair (he : GraphEval C G) (v w : Fin n) :
    val C (point {v,w}) C.output = true ↔ G.Adj v w := by
  have h : point ({v,w} : Finset (Fin n)) = (fun i => decide (i=v ∨ i=w)) := by
    funext i
    simp [point]
  rw [h]
  exact he v w

theorem edge_positive (hC : Monotone2 C) (he : GraphEval C G) {S : Finset (Fin n)}
    (h : ∃ u ∈ S, ∃ v ∈ S, G.Adj u v) : val C (point S) C.output = true := by
  obtain ⟨u,hu,v,hv,adj⟩ := h
  apply acts_mono hC (x:=point {u,v}) (y:=point S) _ _ ((point_pair he u v).2 adj)
  intro i yes
  have hi : i=u ∨ i=v := by simpa [point] using yes
  rcases hi with rfl | rfl <;> simp_all [point]

theorem point_pair_quiet (he : GraphEval C G) {v w : Fin n} (hn : ¬ G.Adj v w) :
    val C (point {v,w}) C.output = false := by
  rw [← Bool.not_eq_true, point_pair he]
  exact hn

theorem point_single_quiet (he : GraphEval C G) (v : Fin n) :
    val C (point {v}) C.output = false := by
  simpa using point_pair_quiet he (G.irrefl (v := v))

theorem edge_at_output (he : GraphEval C G) {v w : Fin n} (hvw : G.Adj v w) :
    n ≤ C.output ∧ C.output < n+C.gates.length := by
  have hp := (point_pair he v w).2 hvw
  constructor
  · by_contra! hl
    let i : Fin n := ⟨C.output,hl⟩
    have hv := point_single_quiet he i
    rw [show C.output = i.val from rfl,val_input] at hv
    simp [point] at hv
  · by_contra! hgt
    rw [val_beyond C _ hgt] at hp
    contradiction

theorem two_inputs {l : List ℕ} {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b)
    (hl : l.length ≤ 2) :
    ∀ i ∈ l, i = a ∨ i = b := by
  have hsub : ({a,b} : Finset ℕ) ⊆ l.toFinset := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact List.mem_toFinset.mpr ha
    · exact List.mem_toFinset.mpr hb
  have hcard : l.toFinset.card ≤ ({a,b} : Finset ℕ).card := by
    simpa [hne] using l.toFinset_card_le.trans hl
  have hEq := Finset.eq_of_subset_of_card_le hsub hcard
  intro i hi
  have hm : i ∈ ({a,b} : Finset ℕ) := hEq.symm ▸ (List.mem_toFinset.mpr hi)
  simpa using hm

theorem carries_separate (hC : Monotone2 C) {v w : Fin n} {a : ℕ}
    (h1 : val C (point {v}) a = true) (h0 : val C (point {w}) a = false) :
    Carries C v a ∧ ¬ Carries C w a := by
  have hb : val C (point (∅ : Finset (Fin n))) a = false := by
    rw [← Bool.not_eq_true]
    intro hc
    have hh := acts_mono hC (point_mono (Finset.empty_subset {w})) a hc
    rw [h0] at hh
    contradiction
  rw [carries_iff hC,carries_iff hC]
  simp [h1,h0,hb]

theorem meeting_gate (hC : Monotone2 C) (he : GraphEval C G) {v w : Fin n}
    (hvw : G.Adj v w) :
    ∃ p g a b, C.gates[p]? = some g ∧ g.op = GateOp.and ∧ Live n C (n+p) ∧
      LNext n C a (n+p) ∧ LNext n C b (n+p) ∧
      Carries C v a ∧ ¬ Carries C w a ∧ Carries C w b ∧ ¬ Carries C v b ∧
      (∀ i ∈ g.inputs, i = a ∨ i = b) := by
  classical
  let P (i : ℕ) := Live n C i ∧ val C (point {v,w}) i = true ∧
    val C (point {v}) i = false ∧ val C (point {w}) i = false
  have hex : ∃ i, P i :=
    ⟨C.output, .refl, (point_pair he v w).2 hvw, point_single_quiet he v, point_single_quiet he w⟩
  let j := Nat.find hex
  have hj : P j := Nat.find_spec hex
  have earlier (i : ℕ) (hlt : i < j) (hl : Live n C i)
      (htrue : val C (point {v,w}) i = true) :
      val C (point {v}) i = true ∨ val C (point {w}) i = true := by
    by_contra! h
    have h' : P i := ⟨hl, htrue, by simpa using h.1, by simpa using h.2⟩
    exact (Nat.not_le_of_gt hlt) (Nat.find_min' hex h')
  have hge : n ≤ j := by
    by_contra! hh
    let i : Fin n := ⟨j,hh⟩
    obtain ⟨_,ht,hv,hw⟩ := hj
    rw [show j = i.val from rfl,val_input] at ht hv hw
    simp only [point,decide_eq_true_eq,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with h | h
    · simp [point,h] at hv
    · simp [point,h] at hw
  have hlt : j < n+C.gates.length := by
    by_contra! hh
    have ht := hj.2.1
    rw [val_beyond C _ hh] at ht
    contradiction
  let p := j-n
  have hp : p < C.gates.length := by dsimp [p]; omega
  have ep : n+p = j := by dsimp [p]; omega
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp,rfl⟩
  have hl := hC g (List.mem_of_getElem? hg)
  have hh : Live n C (n+p) := ep ▸ hj.1
  have hs1 : val C (point {v,w}) (n+p) = true := ep ▸ hj.2.1
  have hs2 : val C (point {v}) (n+p) = false := ep ▸ hj.2.2.1
  have hs3 : val C (point {w}) (n+p) = false := ep ▸ hj.2.2.2
  have reads (i : ℕ) (hi : i < n+p) (hm : i ∈ g.inputs) : LNext n C i (n+p) :=
    ⟨⟨hi,p,g,hg,rfl,hm⟩,hh⟩
  have hAnd : g.op = GateOp.and := by
    rcases hl.1 with h | h
    · exact h
    have hop : g.op = GateOp.or := h
    simp only [val_gate C _ hg, hop, GateOp.eval, List.any_map, Function.comp_apply, id,
      List.any_eq_true] at hs1
    obtain ⟨i,hi,ht⟩ := hs1
    have hi' : i < n+p := by
      by_contra hh'
      simp [operand,hh'] at ht
    have ht' : val C (point {v,w}) i = true := by simpa [operand,hi'] using ht
    rcases earlier i (ep ▸ hi') (live_before (reads i hi' hi).1 hh) ht' with hV | hW
    · have hs := hs2
      rw [← Bool.not_eq_true, val_gate C _ hg,hop,GateOp.eval,List.any_map,List.any_eq_true] at hs
      exact (hs ⟨i,hi,by simpa [operand,hi'] using hV⟩).elim
    · have hs := hs3
      rw [← Bool.not_eq_true, val_gate C _ hg,hop,GateOp.eval,List.any_map,List.any_eq_true] at hs
      exact (hs ⟨i,hi,by simpa [operand,hi'] using hW⟩).elim
  have hAll : ∀ i ∈ g.inputs, operand C (point {v,w}) (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hs1
  have hFalse (x : Fin n → Bool) (hX : val C x (n+p) = false) :
      ∃ i ∈ g.inputs, operand C x (n+p) i = false := by
    by_contra! h
    have ht : val C x (n+p) = true := by
      rw [val_gate C _ hg,hAnd,GateOp.eval,List.all_map,List.all_eq_true]
      intro i hi
      simpa using h i hi
    rw [hX] at ht
    contradiction
  obtain ⟨a,ha,hwa⟩ := hFalse _ hs3
  obtain ⟨b,hb,hvb⟩ := hFalse _ hs2
  have before (i : ℕ) (h : i ∈ g.inputs) : i < n+p := by
    by_contra hi
    have hX := hAll i h
    simp [operand,hi] at hX
  have ha' := before a ha
  have hb' := before b hb
  rw [operand,ite_eq_left ha'] at hwa
  rw [operand,ite_eq_left hb'] at hvb
  have near (i : ℕ) (h : i ∈ g.inputs) :
      val C (point {v}) i = true ∨ val C (point {w}) i = true := by
    have hi := before i h
    apply earlier i (ep ▸ hi) (live_before (reads i hi h).1 hh)
    simpa [operand,hi] using hAll i h
  have hva := (near a ha).resolve_right (by rw [hwa]; decide)
  have hwb := (near b hb).resolve_left (by rw [hvb]; decide)
  have hne : a ≠ b := fun e => Bool.noConfusion (hva.symm.trans (e ▸ hvb))
  exact ⟨p,g,a,b,hg,hAnd,hh,reads a ha' ha,reads b hb' hb,
    (carries_separate hC hva hwa).1,(carries_separate hC hva hwa).2,
    (carries_separate hC hwb hvb).1,(carries_separate hC hwb hvb).2,
    two_inputs ha hb hne hl.2⟩

theorem covers_edge (hC : Monotone2 C) (he : GraphEval C G) {v w a₀ b₀ : Fin n}
    (hvw : G.Adj v w) (ha₀ : G.Adj v a₀) (_ha₁ : a₀ ≠ w)
    (hb₀ : G.Adj w b₀) (_hb₁ : b₀ ≠ v) (hind : a₀ = b₀ ∨ ¬ G.Adj a₀ b₀) :
    Eligible C v ∨ Eligible C w := by
  by_contra! bad
  obtain ⟨p,g,a,b,hg,hAnd,hj,ha,hb,hva,hwa,hwb,hvb,hs⟩ := meeting_gate hC he hvw
  have pathV : Trace n C (Carries C v) v.val (n+p) :=
    (singleton_path (live_before ha.1 ha.2) hva).tail ⟨hva,ha⟩
  have pathW : Trace n C (Carries C w) w.val (n+p) :=
    (singleton_path (live_before hb.1 hb.2) hwb).tail ⟨hwb,hb⟩
  have uniqueV : ∀ k j j', k < n+p → Carries C v k → LNext n C k j → LNext n C k j' → j=j' :=
    fun k j j' _ => no_eligible_unique bad.1 k j j'
  have uniqueW : ∀ k j j', k < n+p → Carries C w k → LNext n C k j → LNext n C k j' → j=j' :=
    fun k j j' _ => no_eligible_unique bad.2 k j j'
  let S : Finset (Fin n) := {a₀,b₀}
  let x := point S
  let y := point (insert v S)
  let z := point (insert w S)
  have hzero : val C x C.output = false :=
    point_pair_quiet he (hind.elim (fun e => e ▸ G.irrefl (v := a₀)) id)
  have hY : val C y C.output = true := edge_positive hC he ⟨v,by simp,a₀,by simp [S],ha₀⟩
  have hZ : val C z C.output = true := edge_positive hC he ⟨w,by simp,b₀,by simp [S],hb₀⟩
  have jout := next_le hj
  have hvj := influence pathV uniqueV (fun _ hi => (point_insert hi).symm) ReflTransGen.refl (show val C x C.output ≠ val C y C.output from by rw [hzero,hY]; decide)
  have hwj := influence pathW uniqueW (fun _ hi => (point_insert hi).symm) ReflTransGen.refl (show val C x C.output ≠ val C z C.output from by rw [hzero,hZ]; decide)
  have hdiffV := (hvj.resolve_left (fun h => (Nat.not_lt_of_ge jout) h.1)).2
  have hdiffW := (hwj.resolve_left (fun h => (Nat.not_lt_of_ge jout) h.1)).2
  have hX : val C x (n+p) = false := by
    rw [← Bool.not_eq_true]
    intro htrue
    exact hdiffV (htrue.trans (acts_mono hC (point_mono (Finset.subset_insert _ _)) _ htrue).symm)
  have hyj : val C y (n+p) = true := by
    rw [hX] at hdiffV
    simpa using hdiffV.symm
  have hzj : val C z (n+p) = true := by
    rw [hX] at hdiffW
    simpa using hdiffW.symm
  have hAX : val C x a = val C z a := by
    by_contra h
    rcases influence pathW uniqueW (fun _ hi => (point_insert hi).symm) (live_before ha.1 ha.2) h with h' | h'
    · exact hwa h'.2
    · exact (Nat.not_le_of_gt ha.1.1) h'.1
  have hBX : val C x b = val C y b := by
    by_contra h
    rcases influence pathV uniqueV (fun _ hi => (point_insert hi).symm) (live_before hb.1 hb.2) h with h' | h'
    · exact hvb h'.2
    · exact (Nat.not_le_of_gt hb.1.1) h'.1
  have hYall : ∀ i ∈ g.inputs, operand C y (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hyj
  have hZall : ∀ i ∈ g.inputs, operand C z (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hzj
  have hin (i : ℕ) : LNext n C i (n+p) → i ∈ g.inputs := by
    rintro ⟨⟨_,k,g',he',hk,hmem⟩,_⟩
    have e : k=p := by omega
    subst k
    rw [hg] at he'
    cases he'
    exact hmem
  have hxA := hZall a (hin a ha)
  have hxB := hYall b (hin b hb)
  rw [operand,ite_eq_left ha.1.1,← hAX] at hxA
  rw [operand,ite_eq_left hb.1.1,← hBX] at hxB
  have hs' : val C x (n+p) = true := by
    rw [val_gate C _ hg,hAnd,GateOp.eval,List.all_map,List.all_eq_true]
    intro i hi
    rcases hs i hi with rfl | rfl
    · simpa [Function.comp_apply,operand,ha.1.1] using hxA
    · simpa [Function.comp_apply,operand,hb.1.1] using hxB
  rw [hX] at hs'
  contradiction

end Plane2866Graph


namespace Plane2866Graph

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}

theorem value_at_branch {v : Fin n} {x y : Fin n → Bool} (hv : Eligible C v)
    (agrees : ∀ i, i ≠ v → x i = y i)
    (hb : val C x (firstBranch C v hv) = val C y (firstBranch C v hv)) :
    val C x C.output = val C y C.output := by
  by_contra h
  have spec := firstBranch_spec v hv
  have path := singleton_path spec.1 spec.2.1
  rcases influence path (firstBranch_unique v hv) agrees ReflTransGen.refl h with bad | bad
  · exact (Nat.not_lt_of_ge (next_le spec.1)) bad.1
  · exact bad.2 hb

theorem branch_injective (hC : Monotone2 C) (he : GraphEval C G)
    (htwins : ∀ v w : Fin n, v ≠ w → ¬ G.Adj v w → 2 ≤ (G.neighborSet v).ncard →
      2 ≤ (G.neighborSet w).ncard → ∃ u : Fin n, ¬ (G.Adj v u ↔ G.Adj w u))
    {v w : Fin n} (hv : Eligible C v) (hw : Eligible C w)
    (hdv : 2 ≤ (G.neighborSet v).ncard) (hdw : 2 ≤ (G.neighborSet w).ncard)
    (h : firstBranch C v hv = firstBranch C w hw) : v = w := by
  classical
  by_contra hne
  let b := firstBranch C v hv
  have hw_b : firstBranch C w hw = b := h.symm
  have hvtrue : val C (point {v}) b = true :=
    (carries_iff hC).1 (firstBranch_spec v hv).2.1 |>.1
  have hwtrue : val C (point {w}) b = true := by
    rw [← hw_b]
    exact (carries_iff hC).1 (firstBranch_spec w hw).2.1 |>.1
  by_cases hadj : G.Adj v w
  · have hbig : val C (point (insert w ({v} : Finset (Fin n)))) b = true :=
      acts_mono hC (point_mono (Finset.subset_insert _ _)) b hvtrue
    have eq := value_at_branch hw
      (x := point {v}) (y := point (insert w ({v} : Finset (Fin n))))
      (fun _ hi => (point_insert hi).symm) (by rw [hw_b,hvtrue,hbig])
    have hy : val C (point (insert w ({v} : Finset (Fin n)))) C.output = true :=
      (point_pair he w v).2 (G.adj_symm hadj)
    rw [point_single_quiet he v,hy] at eq
    contradiction
  obtain ⟨u,hu⟩ := htwins v w hne hadj hdv hdw
  have hx : val C (point {v,u}) b = true := acts_mono hC
    (point_mono (by simp)) b hvtrue
  have hy : val C (point {w,u}) b = true := acts_mono hC
    (point_mono (by simp)) b hwtrue
  have hxyz : val C (point (insert w ({v,u} : Finset (Fin n)))) b = true :=
    acts_mono hC (point_mono (Finset.subset_insert _ _)) b hx
  have hEq : (insert w ({v,u} : Finset (Fin n))) = insert v {w,u} :=
    Finset.insert_comm _ _ _
  have e1 := value_at_branch hw
    (x := point {v,u}) (y := point (insert w ({v,u} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm) (by rw [hw_b,hx,hxyz])
  have e2 := value_at_branch hv
    (x := point {w,u}) (y := point (insert v ({w,u} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm) (by rw [← hEq]; exact hy.trans hxyz.symm)
  have e : val C (point {v,u}) C.output = val C (point {w,u}) C.output :=
    e1.trans (by rw [hEq,e2])
  apply hu
  rw [← point_pair he v u, ← point_pair he w u, e]

noncomputable def living (n : ℕ) (C : Circuit) : Finset ℕ :=
  open Classical in (Finset.range (n+C.gates.length)).filter (Live n C)

theorem mem_living {w : ℕ} : w ∈ living n C ↔ w < n+C.gates.length ∧ Live n C w := by
  classical
  simp [living]

theorem input_live (he : GraphEval C G) {v u : Fin n} (hvu : G.Adj v u) :
    Live n C v.val := by
  have hx : val C (point {u}) C.output = false := point_single_quiet he u
  have hy : val C (point {v,u}) C.output = true := (point_pair he v u).2 hvu
  obtain ⟨i,hi,trace⟩ := difference C (point {u}) (point {v,u}) C.output ReflTransGen.refl
    (by rw [hx,hy]; decide)
  have ei : i=v := by
    by_contra h
    exact hi ((point_insert h).symm)
  subst i
  rcases trace.cases_head with h | ⟨b,hb,_⟩
  · rw [h]
    exact .refl
  · exact live_before hb.2.1 hb.2.2

theorem live_readers_nonempty {a : ℕ} (ha : Live n C a) (hneq : a ≠ C.output) :
    (readers n C a).Nonempty := by
  rcases ha.cases_head with h | ⟨b,hb,hpath⟩
  · exact (hneq h).elim
  · exact ⟨b,mem_readers.2 ⟨hb,hpath⟩⟩

theorem readers_filter (a : ℕ) :
    open Classical in readers n C a = (living n C).filter (fun b => LNext n C a b) := by
  classical
  ext b
  simp only [mem_readers,Finset.mem_filter,mem_living]
  exact ⟨fun h => ⟨⟨next_in_range h.1,h.2⟩,h⟩, And.right⟩

theorem incoming_bound {j : ℕ} (hC : Monotone2 C) (hj : j ∈ living n C) :
    open Classical in ((living n C).filter fun i => LNext n C i j).card ≤ if j<n then 0 else 2 := by
  classical
  by_cases hi : j < n
  · rw [ite_eq_left hi]
    apply Nat.le_of_eq
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.2
    intro i hm
    obtain ⟨_,⟨_,p,g,hg,hp,_⟩,_⟩ := Finset.mem_filter.mp hm
    omega
  rw [ite_eq_right hi]
  have hj' := (mem_living.1 hj).1
  let p := j-n
  have hp : p < C.gates.length := by dsimp [p]; omega
  have he : j=n+p := by dsimp [p]; omega
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp,rfl⟩
  have hsub : ((living n C).filter fun i => LNext n C i j) ⊆ g.inputs.toFinset := by
    intro a ha
    obtain ⟨_,⟨_,q,g',hg',hq,hm⟩,_⟩ := Finset.mem_filter.1 ha
    have ep : p=q := by omega
    subst q
    rw [hg] at hg'
    cases hg'
    exact List.mem_toFinset.2 hm
  exact (Finset.card_le_card hsub).trans (g.inputs.toFinset_card_le.trans
    (hC g (List.mem_of_getElem? hg)).2)

theorem branch_budget (hC : Monotone2 C) (he : GraphEval C G)
    (hdegree : ∀ v : Fin n, ∃ u, G.Adj v u) (ho : C.output ∈ living n C) :
    open Classical in n + ((living n C).filter (Branch n C)).card ≤ C.size + 1 := by
  classical
  let W := living n C
  let S := W.filter (fun a => ¬ a < n)
  let B := W.filter (Branch n C)
  let R := W.erase C.output
  have hSub : Finset.range n ⊆ W := by
    intro a ha
    have hi := Finset.mem_range.1 ha
    let v : Fin n := ⟨a,hi⟩
    obtain ⟨u,hu⟩ := hdegree v
    exact mem_living.2 ⟨by omega,input_live he hu⟩
  have hW : W.card = n + S.card := by
    have h := Finset.card_sdiff_add_card_eq_card hSub
    have e : W \ Finset.range n = S := by ext a; simp [S]
    rw [e,Finset.card_range] at h
    omega
  have hR : R.card + 1 = W.card := by
    dsimp [R]
    have h := Finset.card_erase_add_one ho
    exact h
  have hS : S.card ≤ C.gates.length := by
    rw [show C.gates.length = (Finset.range C.gates.length).card by simp]
    apply Finset.card_le_card_of_injOn (fun a => a-n)
    · intro a ha
      have h : a < n+C.gates.length := (mem_living.1 (Finset.mem_filter.1 ha).1).1
      have h0 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      apply Finset.mem_range.2
      change a-n < C.gates.length
      omega
    · intro a ha b hb hab
      have h1 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      have h2 : n ≤ b := Nat.le_of_not_gt (Finset.mem_filter.1 hb).2
      change a-n=b-n at hab
      omega
  have hoNone : ¬ Branch n C C.output := by
    intro h
    have hgt : 0 < (readers n C C.output).card := by unfold Branch at h; omega
    obtain ⟨b,hb⟩ := Finset.card_pos.1 hgt
    have hs := mem_readers.1 hb
    exact (Nat.not_lt_of_ge (next_le hs.2)) hs.1.1
  have hlow : R.card+B.card ≤ ∑ a ∈ W, (readers n C a).card := by
    have eR : (∑ a ∈ W, (if a=C.output then 0 else 1 : ℕ)) = R.card := by
      calc
        _ = ∑ a ∈ W, (if a≠C.output then 1 else 0 : ℕ) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : a=C.output <;> simp [h]
        _ = R.card := by rw [← Finset.sum_filter]; simp [R,Finset.filter_ne']
    have eB : (∑ a ∈ W, (if Branch n C a then 1 else 0 : ℕ)) = B.card := by
      rw [← Finset.sum_filter]
      simp [B]
    rw [← eR,← eB,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a ha
    have hl := (mem_living.1 ha).2
    by_cases heq : a=C.output
    · subst a
      simp [hoNone]
    · by_cases hb : Branch n C a
      · have hb' : 2 ≤ (readers n C a).card := hb
        simpa [heq,hb] using hb'
      · simpa [heq,hb] using Nat.succ_le_of_lt (Finset.card_pos.2 (live_readers_nonempty hl heq))
  have hcomm :
      (∑ a ∈ W, (readers n C a).card) =
        ∑ j ∈ W, (W.filter fun a => LNext n C a j).card := by
    simp_rw [readers_filter,Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_comm
  have hupp : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤ 2*S.card := by
    have H : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤
        ∑ j ∈ W, (if j<n then 0 else 2 : ℕ) :=
      Finset.sum_le_sum fun j hj => incoming_bound hC hj
    have e : (∑ j ∈ W, (if j<n then 0 else 2 : ℕ)) = 2*S.card := by
      simp [S,Finset.sum_ite, Nat.mul_comm]
    exact H.trans_eq e
  rw [hcomm] at hlow
  change n+B.card ≤ C.gates.length+1
  omega

end Plane2866Graph


namespace Plane2866Results

theorem pairLower :
    ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ v : Fin n, ∃ w : Fin n, G.Adj v w) → (∀ v w : Fin n, v ≠ w → ¬ G.Adj v w → 2 ≤ (G.neighborSet v).ncard → 2 ≤ (G.neighborSet w).ncard → ∃ u : Fin n, ¬ (G.Adj v u ↔ G.Adj w u)) → (∀ v w : Fin n, G.Adj v w → 2 ≤ (G.neighborSet v).ncard → 2 ≤ (G.neighborSet w).ncard → ∃ a b : Fin n, G.Adj v a ∧ a ≠ w ∧ G.Adj w b ∧ b ≠ v ∧ (a = b ∨ ¬ G.Adj a b)) → (∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → 2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard → u ∈ S ∨ v ∈ S) ∧ S.card = t) → (∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → 2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard → u ∈ S ∨ v ∈ S) → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ v w : Fin n, C.eval (List.ofFn fun i : Fin n => decide (i = v ∨ i = w)) = true ↔ G.Adj v w) → n + t ≤ C.size + 1 := by
  open Plane2866Graph in
  classical
  intro n t G C hdegree htwins hadj _ ht hC he
  by_cases hn : n=0
  · subst n
    have ht0 := ht ∅ (fun u => Fin.elim0 u)
    simp at ht0
    omega
  have hE : GraphEval C G := he
  let v : Fin n := ⟨0, by omega⟩
  obtain ⟨w, hve⟩ := hdegree v
  have ho := (edge_at_output hE hve).2
  have ho' : C.output ∈ living n C := mem_living.2 ⟨ho, Relation.ReflTransGen.refl⟩
  let S : Finset (Fin n) := Finset.univ.filter fun v =>
    2 ≤ (G.neighborSet v).ncard ∧ Eligible C v
  have hS (u : Fin n) : u ∈ S ↔ 2 ≤ (G.neighborSet u).ncard ∧ Eligible C u := by
    simp [S]
  have htc : t ≤ S.card := by
    apply ht S
    intro a b hab hda hdb
    obtain ⟨u,v,hu,hu',hv,hv',hind⟩ := hadj a b hab hda hdb
    rcases covers_edge hC hE hab hu hu' hv hv' hind with ha | hb
    · exact Or.inl ((hS a).2 ⟨hda,ha⟩)
    · exact Or.inr ((hS b).2 ⟨hdb,hb⟩)
  let B := (living n C).filter (Branch n C)
  let f (u : Fin n) := if h : Eligible C u then firstBranch C u h else 0
  have hf (u : Fin n) (hu : Eligible C u) : f u = firstBranch C u hu := by simp [f,hu]
  have hcap : S.card ≤ B.card := by
    apply Finset.card_le_card_of_injOn f
    · intro u hu
      obtain ⟨_,hs⟩ := (hS u).1 hu
      have hb := firstBranch_spec u hs
      have hlt := (next_le hb.1).trans_lt ho
      show f u ∈ B
      rw [hf u hs]
      exact Finset.mem_filter.2 ⟨mem_living.2 ⟨hlt,hb.1⟩,hb.2.2⟩
    · intro u hu v hv huv
      obtain ⟨hdu,hsu⟩ := (hS u).1 hu
      obtain ⟨hdv,hsv⟩ := (hS v).1 hv
      rw [hf u hsu,hf v hsv] at huv
      exact branch_injective hC hE htwins hsu hsv hdu hdv huv
  have hbudget := branch_budget hC hE hdegree ho'
  exact (Nat.add_le_add_left (htc.trans hcap) n).trans hbudget

end Plane2866Results

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The transfer to a projective plane is from the accepted reduction in PR 5439.
theorem linearLower :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   101 ≤ x1 →      x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.MetaComplexity.Monotone2 x5 →             (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) →               (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →                 3*x2 ≤ x5.size+1 := by
  let L {N : ℕ} : Fin N → Fin (N+N) := Fin.castAdd N
  let R {N : ℕ} : Fin N → Fin (N+N) := Fin.natAdd N
  have sides {N : ℕ} (p l : Fin N) : L p ≠ R l := by
    intro equal
    have val := congrArg Fin.val equal
    change p.val = N + l.val at val
    have inRange := p.isLt
    omega
  have leftInjective {N : ℕ} : Function.Injective (@L N) := by
    intro a b eq
    have valuations : (L a).val = (L b).val := congrArg Fin.val eq
    exact Fin.ext valuations
  have rightInjective {N : ℕ} : Function.Injective (@R N) := by
    intro a b eq
    have val := congrArg Fin.val eq
    change N + a.val = N + b.val at val
    exact Fin.ext (by omega)
  let graph {N : ℕ} (I : Fin N → Fin N → Prop) : SimpleGraph (Fin (N+N)) :=
    SimpleGraph.fromRel (fun x y => ∃ p l, x = L p ∧ y = R l ∧ I p l)
  have adjEither {N : ℕ} (I : Fin N → Fin N → Prop) (x y : Fin (N+N)) :
      (graph I).Adj x y ↔
        (∃ p l, x = L p ∧ y = R l ∧ I p l) ∨ (∃ p l, y = L p ∧ x = R l ∧ I p l) := by
    unfold graph
    rw [SimpleGraph.fromRel_adj]
    constructor
    · exact And.right
    · intro ok
      refine ⟨?_,ok⟩
      rintro rfl
      rcases ok with ⟨p,l,atP,atL,_⟩ | ⟨p,l,atP,atL,_⟩
      · exact sides p l (atP.symm.trans atL)
      · exact sides p l (atP.symm.trans atL)
  have leftNeighbors {N : ℕ} (I : Fin N → Fin N → Prop) (p : Fin N) (y : Fin (N+N)) :
      (graph I).Adj (L p) y ↔ ∃ l, y = R l ∧ I p l := by
    rw [adjEither]
    constructor
    · rintro (⟨p',l,atP,atL,inc⟩ | ⟨p',l,_,invalid,_⟩)
      · exact ⟨l, atL, (leftInjective atP).symm ▸ inc⟩
      · exact (sides p l invalid).elim
    · rintro ⟨l,eq,inc⟩
      exact Or.inl ⟨p,l,rfl,eq,inc⟩
  have rightNeighbors {N : ℕ} (I : Fin N → Fin N → Prop) (l : Fin N) (y : Fin (N+N)) :
      (graph I).Adj (R l) y ↔ ∃ p, y = L p ∧ I p l := by
    rw [adjEither]
    constructor
    · rintro (⟨p,l',invalid,_,_⟩ | ⟨p,l',atP,atL,inc⟩)
      · exact (sides p l invalid.symm).elim
      · exact ⟨p,atP,(rightInjective atL).symm ▸ inc⟩
    · rintro ⟨p,eq,inc⟩
      exact Or.inr ⟨p,l,eq,rfl,inc⟩
  have leftRight {N : ℕ} (I : Fin N → Fin N → Prop) (p l : Fin N) :
      (graph I).Adj (L p) (R l) ↔ I p l := by
    rw [leftNeighbors]
    constructor
    · rintro ⟨k,eq,inc⟩
      exact (rightInjective eq).symm ▸ inc
    · exact fun inc => ⟨l,rfl,inc⟩
  have noFour {N : ℕ} (I : Fin N → Fin N → Prop)
      (unique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
      (u v a b : Fin (N+N)) (vertices : u ≠ v) (neighbors : a ≠ b)
      (ua : (graph I).Adj u a) (ub : (graph I).Adj u b)
      (va : (graph I).Adj v a) (vb : (graph I).Adj v b) : False := by
    have crosses (p l : Fin N) (otherP otherL : Fin (N+N))
        (differentP : L p ≠ otherP) (differentL : R l ≠ otherL)
        (pl : I p l) (pOther : (graph I).Adj (L p) otherL)
        (otherL' : (graph I).Adj otherP (R l)) (pair : (graph I).Adj otherP otherL) : False := by
      obtain ⟨k, rfl, pk⟩ := (leftNeighbors I p otherL).mp pOther
      obtain ⟨r, rfl, rl⟩ := (rightNeighbors I l otherP).mp ((graph I).adj_symm otherL')
      have rk := (leftRight I r k).mp pair
      have distinct : p ≠ r := fun eq => differentP (congrArg L eq)
      have same := (unique p r distinct).unique ⟨pl,rl⟩ ⟨pk,rk⟩
      exact differentL (congrArg R same)
    rcases (adjEither I u a).mp ua with ⟨p,l,rfl,rfl,pl⟩ | ⟨p,l,rfl,rfl,pl⟩
    · exact crosses p l v b vertices neighbors pl ub va vb
    · exact crosses p l b v neighbors vertices pl ((graph I).adj_symm va) ((graph I).adj_symm ub) ((graph I).adj_symm vb)
  have enoughNeighbors (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (big : 101 ≤ q) (order : N = q^2+q+1)
      (degree : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1)
      (unique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
      (v : Fin (N+N)) : ∃ a b, a ≠ b ∧ (graph I).Adj v a ∧ (graph I).Adj v b := by
    classical
    have roomy : q+1 < N := by rw [order]; nlinarith
    have pointsOn (l : Fin N) : (Finset.univ.filter fun p : Fin N => I p l).card = q+1 :=
      (Fintype.card_subtype (fun p => I p l)).symm.trans (degree l)
    have outside (l : Fin N) : ∃ p, ¬ I p l := by
      by_contra! every
      have full : (Finset.univ.filter fun p : Fin N => I p l) = Finset.univ := by ext p; simp [every]
      have count := pointsOn l
      rw [full] at count
      simp at count
      omega
    have twoPoints : ∃ a b : Fin N, a ≠ b := by
      obtain ⟨a,b,_,_,distinct⟩ := Finset.one_lt_card_iff.mp
        (show 1 < (Finset.univ : Finset (Fin N)).card from by simp; omega)
      exact ⟨a,b,distinct⟩
    refine Fin.addCases (fun p => ?_) (fun l => ?_) v
    · obtain ⟨a,b,distinct⟩ := twoPoints
      have other : ∃ r : Fin N, p ≠ r := by by_cases eq : p=a; exact ⟨b,eq ▸ distinct⟩; exact ⟨a,eq⟩
      obtain ⟨r,diff⟩ := other
      obtain ⟨l,onL,_⟩ := unique p r diff
      obtain ⟨z,off⟩ := outside l
      have newPoint : p ≠ z := fun eq => off (eq ▸ onL.1)
      obtain ⟨k,onK,_⟩ := unique p z newPoint
      have otherLine : l ≠ k := fun eq => off (eq ▸ onK.2)
      exact ⟨R l,R k,fun eq => otherLine (rightInjective eq),(leftRight I p l).mpr onL.1,
        (leftRight I p k).mpr onK.1⟩
    · obtain ⟨a,b,memA,memB,distinct⟩ := Finset.one_lt_card_iff.mp
        (show 1 < (Finset.univ.filter fun p : Fin N => I p l).card from by rw [pointsOn]; omega)
      exact ⟨L a,L b,fun eq => distinct (leftInjective eq),
        (graph I).adj_symm ((leftRight I a l).mpr (Finset.mem_filter.mp memA).2),
        (graph I).adj_symm ((leftRight I b l).mpr (Finset.mem_filter.mp memB).2)⟩
  have pointDegree (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (positive : 0 < q) (order : N = q^2+q+1)
      (degrees : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1)
      (unique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
      (p : Fin N) : (Finset.univ.filter fun l : Fin N => I p l).card = q+1 := by
    classical
    let through := Finset.univ.filter (fun l : Fin N => I p l)
    let rest (l : Fin N) := Finset.univ.filter (fun r : Fin N => I r l ∧ r ≠ p)
    have count (l : Fin N) (hl : l ∈ through) : (rest l).card = q := by
      let full := Finset.univ.filter (fun r : Fin N => I r l)
      have same : rest l = full.erase p := by ext r; simp [rest,full,and_comm]
      have inFull : p ∈ full := Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hl).2⟩
      have cardFull : full.card = q+1 := (Fintype.card_subtype (fun r => I r l)).symm.trans (degrees l)
      rw [same,Finset.card_erase_of_mem inFull,cardFull]
      omega
    have disjoint : (↑through : Set (Fin N)).PairwiseDisjoint rest := by
      intro l other k more different
      refine Finset.disjoint_left.mpr ?_
      intro r here there
      have throughL : I p l := (Finset.mem_filter.mp other).2
      have throughK : I p k := (Finset.mem_filter.mp more).2
      obtain ⟨rl,diff⟩ := (Finset.mem_filter.mp here).2
      have rk := (Finset.mem_filter.mp there).2.1
      exact different ((unique p r (Ne.symm diff)).unique ⟨throughL,rl⟩ ⟨throughK,rk⟩)
    have together : through.biUnion rest = Finset.univ.erase p := by
      ext r
      constructor
      · intro seen
        obtain ⟨l,_,rl⟩ := Finset.mem_biUnion.mp seen
        exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp rl).2.2,Finset.mem_univ _⟩
      · intro seen
        have diff := (Finset.mem_erase.mp seen).1
        obtain ⟨l,⟨pl,rl⟩,_⟩ := unique p r (Ne.symm diff)
        exact Finset.mem_biUnion.mpr ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,pl⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,rl,diff⟩⟩
    have rightSize : (Finset.univ.erase p).card = (q+1)*q := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,Fintype.card_fin,order]
      rw [Nat.add_sub_cancel]
      ring
    have scale : through.card*q = (q+1)*q := by
      calc
        through.card*q = ∑ l ∈ through, q := by simp
        _ = ∑ l ∈ through, (rest l).card := Finset.sum_congr rfl (fun l hl => (count l hl).symm)
        _ = (through.biUnion rest).card := (Finset.card_biUnion disjoint).symm
        _ = (q+1)*q := by rw [together,rightSize]
    exact Nat.eq_of_mul_eq_mul_right positive scale
  have coverBudget (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (rowDegree : ∀ p : Fin N, (Finset.univ.filter fun l : Fin N => I p l).card = q+1)
      (columnDegree : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1)
      (S : Finset (Fin (N+N))) (covers : ∀ p l, I p l → L p ∈ S ∨ R l ∈ S) : N ≤ S.card := by
    classical
    let edges := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)
    let rows (p : Fin N) := (Finset.univ.filter fun l : Fin N => I p l).image fun l => (p,l)
    let columns (l : Fin N) := (Finset.univ.filter fun p : Fin N => I p l).image fun p => (p,l)
    let star (v : Fin (N+N)) : Finset (Fin N × Fin N) := Fin.addCases rows columns v
    have rowSize (p : Fin N) : (rows p).card = q+1 := by
      dsimp only [rows]
      rw [Finset.card_image_of_injective _ (fun _ _ eq => congrArg Prod.snd eq),rowDegree]
    have columnSize (l : Fin N) : (columns l).card = q+1 := by
      dsimp only [columns]
      rw [Finset.card_image_of_injective _ (fun _ _ eq => congrArg Prod.fst eq),
        ← Fintype.card_subtype (fun p => I p l),columnDegree]
    have starSize (v : Fin (N+N)) : (star v).card = q+1 := by
      refine Fin.addCases (fun p => ?_) (fun l => ?_) v
      · simpa [star] using rowSize p
      · simpa only [star,Fin.addCases_right] using columnSize l
    have distinct : (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint columns := by
      intro l _ k _ different
      refine Finset.disjoint_left.mpr ?_
      intro e inL inK
      obtain ⟨p,_,left⟩ := Finset.mem_image.mp inL
      obtain ⟨r,_,right⟩ := Finset.mem_image.mp inK
      exact different (congrArg Prod.snd (left.trans right.symm))
    have edgeSize : edges.card = N*(q+1) := by
      have same : edges = Finset.univ.biUnion columns := by
        ext e
        rcases e with ⟨p,l⟩
        simp [edges,columns,Prod.mk.injEq]
      rw [same,Finset.card_biUnion distinct]
      simp [columnSize]
    have capture : edges ⊆ S.biUnion star := by
      rintro ⟨p,l⟩ good
      have relation := (Finset.mem_filter.mp good).2
      rcases covers p l relation with atP | atL
      · apply Finset.mem_biUnion.mpr
        refine ⟨L p,atP,?_⟩
        have inRow : (p,l) ∈ rows p := Finset.mem_image.mpr ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,relation⟩,rfl⟩
        simpa [star,L] using inRow
      · apply Finset.mem_biUnion.mpr
        refine ⟨R l,atL,?_⟩
        have inCol : (p,l) ∈ columns l := Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,relation⟩,rfl⟩
        simpa only [star,R,Fin.addCases_right] using inCol
    have budget : edges.card ≤ S.card*(q+1) :=
      (Finset.card_le_card capture).trans (Finset.card_biUnion_le.trans (by simp [starSize]))
    rw [edgeSize] at budget
    exact Nat.le_of_mul_le_mul_right budget (by omega)
  have pairTests (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (big : 101 ≤ q) (C : Circuit)
      (positive : ∀ p l : Fin N, I p l →
        circuitFun (N+N) C (fun i => decide (i = L p ∨ i = R l)) = true)
      (negative : ∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (R l) = true} ≤ q →
        (¬∃ p l, I p l ∧ x (L p) = true ∧ x (R l) = true) → circuitFun (N+N) C x = false) :
      ∀ u v : Fin (N+N), C.eval (List.ofFn fun i : Fin (N+N) => decide (i = u ∨ i = v)) = true ↔
        (graph I).Adj u v := by
    intro u v
    let x : Fin (N+N) → Bool := fun i => decide (i=u ∨ i=v)
    change circuitFun (N+N) C x = true ↔ (graph I).Adj u v
    constructor
    · intro recognized
      by_contra missing
      let toPair (a : {l : Fin N // x (R l) = true}) : {v' : Fin (N+N) // v' ∈ ({u,v} : Finset _)} := by
        refine ⟨R a.val,?_⟩
        have sits : R a.val = u ∨ R a.val = v := of_decide_eq_true a.property
        simpa only [Finset.mem_insert,Finset.mem_singleton] using sits
      have injective : Function.Injective toPair := by
        intro a b equal
        apply Subtype.ext
        have same := congrArg (fun z : {j : Fin (N+N) // j ∈ ({u,v} : Finset _)} => z.val) equal
        change R a.val = R b.val at same
        exact rightInjective same
      have small : Fintype.card {l : Fin N // x (R l) = true} ≤ q := by
        apply (Fintype.card_le_of_injective toPair injective).trans
        rw [Fintype.card_of_subtype ({u,v} : Finset (Fin (N+N))) (fun _ => Iff.rfl)]
        have bound := Finset.card_insert_le (a := u) (s := ({v} : Finset (Fin (N+N))))
        simp only [Finset.card_singleton] at bound
        omega
      have cannot : ¬∃ p l, I p l ∧ x (L p) = true ∧ x (R l) = true := by
        rintro ⟨p,l,inc,onP,onL⟩
        have hereP : L p = u ∨ L p = v := of_decide_eq_true onP
        have hereL : R l = u ∨ R l = v := of_decide_eq_true onL
        rcases hereP with left | right <;> rcases hereL with first | second
        · exact sides p l (left.trans first.symm)
        · apply missing
          exact (adjEither I u v).mpr (Or.inl ⟨p,l,left.symm,second.symm,inc⟩)
        · apply missing
          exact (adjEither I u v).mpr (Or.inr ⟨p,l,right.symm,first.symm,inc⟩)
        · exact sides p l (right.trans second.symm)
      rw [negative x small cannot] at recognized
      contradiction
    · intro inc
      rcases (adjEither I u v).mp inc with ⟨p,l,rfl,rfl,hit⟩ | ⟨p,l,rfl,rfl,hit⟩
      · exact positive p l hit
      · have eq : x = (fun i => decide (i=L p ∨ i=R l)) := by funext i; simp [x,or_comm]
        rw [eq]
        exact positive p l hit
  intro q N I _ C big order degrees unique mono positive negative
  classical
  let G := graph I
  have neighbors (v : Fin (N+N)) : ∃ a b, a ≠ b ∧ G.Adj v a ∧ G.Adj v b :=
    enoughNeighbors q N I big order degrees unique v
  have atLeastTwo (v : Fin (N+N)) : 2 ≤ (G.neighborSet v).ncard := by
    obtain ⟨a,b,diff,va,vb⟩ := neighbors v
    have finite : (G.neighborSet v).Finite := Set.toFinite _
    rw [Set.ncard_eq_toFinset_card _ finite]
    exact Finset.one_lt_card_iff.mpr ⟨a,b,finite.mem_toFinset.mpr va,finite.mem_toFinset.mpr vb,diff⟩
  have noTwins (v w : Fin (N+N)) (different : v ≠ w) : ∃ a, ¬(G.Adj v a ↔ G.Adj w a) := by
    by_contra! same
    obtain ⟨a,b,distinct,va,vb⟩ := neighbors v
    exact noFour I unique v w a b different distinct va vb ((same a).mp va) ((same b).mp vb)
  have other (v w : Fin (N+N)) : ∃ a, G.Adj v a ∧ a ≠ w := by
    obtain ⟨a,b,different,va,vb⟩ := neighbors v
    by_cases first : a = w
    · exact ⟨b,vb,fun second => different (first.trans second.symm)⟩
    · exact ⟨a,va,first⟩
  have adjacent (v w : Fin (N+N)) (edge : G.Adj v w) :
      ∃ a b : Fin (N+N), G.Adj v a ∧ a ≠ w ∧ G.Adj w b ∧ b ≠ v ∧ (a = b ∨ ¬G.Adj a b) := by
    obtain ⟨a,va,notW⟩ := other v w
    obtain ⟨b,wb,notV⟩ := other w v
    refine ⟨a,b,va,notW,wb,notV,Or.inr ?_⟩
    intro ab
    exact noFour I unique w a v b (Ne.symm notW) (Ne.symm notV) (G.adj_symm edge) wb (G.adj_symm va) ab
  let cover (S : Finset (Fin (N+N))) : Prop :=
    ∀ u v, G.Adj u v → 2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard → u ∈ S ∨ v ∈ S
  let coverSize (k : ℕ) : Prop := ∃ S : Finset (Fin (N+N)), cover S ∧ S.card = k
  have some : ∃ k, coverSize k :=
    ⟨_,Finset.univ,fun _ _ _ _ _ => Or.inl (Finset.mem_univ _),rfl⟩
  let t := Nat.find some
  have minimum : ∀ S : Finset (Fin (N+N)), cover S → t ≤ S.card := fun S ok =>
    Nat.find_min' some ⟨S,ok,rfl⟩
  obtain ⟨S,coverS,count⟩ := Nat.find_spec some
  have rows := pointDegree q N I (by omega) order degrees unique
  have tBig : N ≤ t := by
    change N ≤ Nat.find some
    rw [← count]
    apply coverBudget q N I rows degrees S
    intro p l inc
    exact coverS (L p) (R l) ((leftRight I p l).mpr inc) (atLeastTwo _) (atLeastTwo _)
  have floor := Plane2866Results.pairLower (N+N) t G C
    (fun v => by obtain ⟨a,_,_,adj,_⟩ := neighbors v; exact ⟨a,adj⟩)
    (fun v w distinct _ _ _ => noTwins v w distinct)
    (fun v w edge _ _ => adjacent v w edge)
    ⟨S,coverS,count⟩ minimum mono (pairTests q N I big C positive negative)
  omega
end

-- PlaneMinimumCover
section
open Finset

theorem regularIncidenceCoverSide {n d : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (rows : ∀ p, (univ.bipartiteAbove I p).card = d)
    (cols : ∀ l, (univ.bipartiteBelow I l).card = d)
    (connected : ∀ p r, Relation.ReflTransGen (fun a b => ∃ l, I a l ∧ I b l) p r)
    (P L : Finset (Fin n)) (size : P.card + L.card = n)
    (cover : ∀ p l, I p l → p ∈ P ∨ l ∈ L) :
    (P = univ ∧ L = ∅) ∨ (P = ∅ ∧ L = univ) := by
  classical
  have complement : Pᶜ.card = L.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  have above (p) (hp : p ∈ Pᶜ) : L.bipartiteAbove I p = univ.bipartiteAbove I p := by
    ext l
    simp only [mem_bipartiteAbove, mem_univ, true_and]
    exact ⟨And.right, fun hi => ⟨(cover p l hi).resolve_left (mem_compl.mp hp), hi⟩⟩
  have below (l) : Pᶜ.bipartiteBelow I l ⊆ univ.bipartiteBelow I l := by
    intro p hp
    exact (mem_bipartiteBelow I).mpr ⟨mem_univ _, ((mem_bipartiteBelow I).mp hp).2⟩
  have count : (∑ l ∈ L, (Pᶜ.bipartiteBelow I l).card) = ∑ _l ∈ L, d := by
    rw [← sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow I]
    calc
      _ = ∑ _p ∈ Pᶜ, d := sum_congr rfl (fun p hp => (congrArg Finset.card (above p hp)).trans (rows p))
      _ = _ := by simp [complement]
  have coveredOnce (l) (hl : l ∈ L) : Pᶜ.bipartiteBelow I l = univ.bipartiteBelow I l := by
    apply eq_of_subset_of_card_le (below l)
    rw [cols l]
    by_contra! bad
    have strict := Finset.sum_lt_sum
      (fun k (_ : k ∈ L) => (card_le_card (below k)).trans_eq (cols k)) ⟨l,hl,bad⟩
    omega
  have exclusive (p l) (hi : I p l) : p ∈ P ↔ l ∉ L := by
    constructor
    · intro hp hl
      have mem : p ∈ Pᶜ.bipartiteBelow I l := (coveredOnce l hl).symm ▸
        ((mem_bipartiteBelow I).mpr ⟨mem_univ _,hi⟩)
      exact (mem_compl.mp ((mem_bipartiteBelow I).mp mem).1) hp
    · exact (cover p l hi).resolve_right
  have equal (p r : Fin n) : p ∈ P ↔ r ∈ P := by
    induction connected p r with
    | refl => rfl
    | tail _ step ih =>
      obtain ⟨l, left, right⟩ := step
      exact ih.trans ((exclusive _ l left).trans (exclusive _ l right).symm)
  by_cases empty : P = ∅
  · refine Or.inr ⟨empty, eq_univ_of_card _ ?_⟩
    simpa [empty] using size
  · obtain ⟨p,hp⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    have allP : P = univ := eq_univ_of_forall fun r => (equal p r).mp hp
    refine Or.inl ⟨allP,card_eq_zero.mp ?_⟩
    simpa [allP] using size

theorem planeBranchBudgetEquality {n d s : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (rows : ∀ p, (univ.bipartiteAbove I p).card = d)
    (cols : ∀ l, (univ.bipartiteBelow I l).card = d)
    (join : ∀ p r, p ≠ r → ∃ l, I p l ∧ I r l)
    (S : Finset (Fin (n+n))) (B : Finset ℕ) (first : Fin (n+n) → ℕ)
    (cover : ∀ p l, I p l → Fin.castAdd n p ∈ S ∨ Fin.natAdd n l ∈ S)
    (floor : n ≤ S.card)
    (into : ∀ v ∈ S, first v ∈ B) (inj : Set.InjOn first S)
    (budget : n+n+B.card ≤ s+1) (tight : s+1 = 3*n) :
    S.image first = B ∧
      (((∀ p, Fin.castAdd n p ∈ S) ∧ (∀ l, Fin.natAdd n l ∉ S)) ∨
       ((∀ p, Fin.castAdd n p ∉ S) ∧ (∀ l, Fin.natAdd n l ∈ S))) := by
  classical
  have subset : S.image first ⊆ B := by
    intro b hb
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hb
    exact into v hv
  have count := card_le_card subset
  have imageSize := card_image_of_injOn inj
  have sizeS : S.card = n := by omega
  refine ⟨eq_of_subset_of_card_le subset (by omega), ?_⟩
  let P := univ.filter fun p => Fin.castAdd n p ∈ S
  let L := univ.filter fun l => Fin.natAdd n l ∈ S
  have splitCount := Fin.sum_univ_add (fun v : Fin (n+n) => if v ∈ S then 1 else (0 : ℕ))
  have splitSize : P.card + L.card = n := by
    simpa [P,L,Finset.sum_boole,sizeS] using splitCount.symm
  have conn (p r : Fin n) : Relation.ReflTransGen (fun a b => ∃ l, I a l ∧ I b l) p r := by
    by_cases e : p = r
    · subst r; exact .refl
    · exact .single (join p r e)
  have covered (p l) (edge : I p l) : p ∈ P ∨ l ∈ L := by
    simpa [P,L] using cover p l edge
  rcases regularIncidenceCoverSide I rows cols conn P L splitSize covered with
    ⟨allP,noL⟩ | ⟨noP,allL⟩
  · left
    constructor
    · intro p
      have h : p ∈ P := allP ▸ mem_univ _
      simpa [P] using h
    · intro l
      have h : l ∉ L := noL ▸ notMem_empty _
      simpa [L] using h
  · right
    constructor
    · intro p
      have h : p ∉ P := noP ▸ notMem_empty _
      simpa [P] using h
    · intro l
      have h : l ∈ L := allL ▸ mem_univ _
      simpa [L] using h
end

-- PlaneLeafBudget
section
open Finset

theorem cutForestLeafCount {W : Type*} [Fintype W] [DecidableEq W]
    (root : W) (cuts : Finset W) (parents : W → Finset W)
    (raw seed before after : W → ℕ) (terminal : root ∉ cuts)
    (build : ∀ w, before w = raw w + ∑ u ∈ parents w, after u)
    (cut : ∀ w, after w = if w ∈ cuts then seed w else before w)
    (fanout : ∀ u, (univ.filter fun w => u ∈ parents w).card =
      if u = root then 0 else if u ∈ cuts then 2 else 1) :
    before root + ∑ w ∈ cuts, before w = (∑ w, raw w) + 2 * ∑ w ∈ cuts, seed w := by
  classical
  let users (u : W) := (univ.filter fun w => u ∈ parents w).card
  have edges : ∑ w, ∑ u ∈ parents w, after u = ∑ u, users u * after u := by
    calc
      _ = ∑ w, ∑ u, if u ∈ parents w then after u else 0 := by
        apply sum_congr rfl
        intro w _
        simp
      _ = ∑ u, ∑ w, if u ∈ parents w then after u else 0 := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro u _
        simp [← sum_filter, users]
  have total : ∑ w, before w = (∑ w, raw w) + ∑ u, users u * after u := by
    calc
      _ = ∑ w, (raw w + ∑ u ∈ parents w, after u) := sum_congr rfl fun w _ => build w
      _ = _ := by rw [sum_add_distrib, edges]
  have each (w : W) :
      ((if w = root then before w else 0) + (if w ∈ cuts then before w else 0)) +
          users w * after w = before w + 2 * (if w ∈ cuts then seed w else 0) := by
    by_cases h : w = root
    · subst w
      simp [users, fanout, terminal]
    · by_cases b : w ∈ cuts <;> simp [users, fanout, cut, h, b]
  have combined := sum_congr (s₁ := (univ : Finset W)) rfl (fun w _ => each w)
  simp only [sum_add_distrib, ← mul_sum] at combined
  simp at combined
  omega

theorem cutForestResidualBudget {W : Type*} [DecidableEq W]
    (cuts : Finset W) (output : ℕ) (before residual seed : W → ℕ)
    (balance : output + ∑ w ∈ cuts, before w = 1 + 2 * ∑ w ∈ cuts, seed w)
    (remove : ∀ w ∈ cuts, residual w + seed w ≤ before w) :
    output + ∑ w ∈ cuts, residual w ≤ 1 + ∑ w ∈ cuts, seed w := by
  have saved := sum_le_sum remove
  rw [sum_add_distrib] at saved
  omega
end

-- PlaneFormulaCore
section
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
end

-- PlaneFormulaTrace
section
namespace PlaneFormula
namespace Trace

variable {α L : Type} [DecidableEq α] [Fintype L] [DecidableEq L]

def W (line : L → α) : PlaneFormula α → Finset L
  | .bot => ∅
  | .leaf a => Finset.univ.filter (line · = a)
  | .or s t => W line s ∪ W line t
  | .and _ _ => ∅

def pieces (line : L → α) : PlaneFormula α → Finset (Finset L)
  | .bot => {∅}
  | .leaf a => {W line (.leaf a)}
  | .or s t => insert (W line (.or s t)) (pieces line s ∪ pieces line t)
  | .and s t => insert ∅ (pieces line s ∪ pieces line t)

theorem root_mem (line : L → α) (t : PlaneFormula α) : W line t ∈ pieces line t := by
  cases t <;> simp [pieces, W]

def point (p a : α) := decide (a = p)
def pair (p b a : α) := decide (a = p ∨ a = b)

omit [DecidableEq α] in
theorem eval_triggered (t : PlaneFormula α) (v : α → Bool) (h : t.eval v = true) :
    ∃ a ∈ t.leaves, v a = true := by
  induction t with
  | bot => contradiction
  | leaf a => exact ⟨a,by simp [leaves],h⟩
  | or s t hs ht =>
    rcases Bool.or_eq_true_iff.mp h with val | val
    · obtain ⟨a,ha,hit⟩ := hs val
      exact ⟨a,List.mem_append_left _ ha,hit⟩
    · obtain ⟨a,ha,hit⟩ := ht val
      exact ⟨a,List.mem_append_right _ ha,hit⟩
  | and s t hs ht =>
    obtain ⟨a,ha,hit⟩ := hs (Bool.and_eq_true_iff.mp h).1
    exact ⟨a,List.mem_append_left _ ha,hit⟩

omit [DecidableEq α] in
theorem eval_mono (t : PlaneFormula α) {v w : α → Bool}
    (h : ∀ a, v a = true → w a = true) (ht : t.eval v = true) : t.eval w = true := by
  induction t with
  | bot => contradiction
  | leaf a => exact h a ht
  | or s t hs ht' =>
    exact Bool.or_eq_true_iff.mpr ((Bool.or_eq_true_iff.mp ht).imp hs ht')
  | and s t hs ht' =>
    exact Bool.and_eq_true_iff.mpr ⟨hs (Bool.and_eq_true_iff.mp ht).1, ht' (Bool.and_eq_true_iff.mp ht).2⟩

omit [DecidableEq α] in
theorem eval_congr_leaves (t : PlaneFormula α) {v w : α → Bool}
    (agree : ∀ a ∈ t.leaves, v a = w a) : t.eval v = t.eval w := by
  induction t with
  | bot => rfl
  | leaf a => exact agree a (by simp [leaves])
  | or s t hs ht =>
    exact congrArg₂ Bool.or (hs (fun a ha => agree a (List.mem_append_left _ ha)))
      (ht (fun a ha => agree a (List.mem_append_right _ ha)))
  | and s t hs ht =>
    exact congrArg₂ Bool.and (hs (fun a ha => agree a (List.mem_append_left _ ha)))
      (ht (fun a ha => agree a (List.mem_append_right _ ha)))

theorem line_needed {t : PlaneFormula α} {p b : α}
    (off : t.eval (point p) = false) (on : t.eval (pair p b) = true) : b ∈ t.leaves := by
  by_contra absent
  have same : t.eval (pair p b) = t.eval (point p) :=
    eval_congr_leaves t (fun a ha => by
      have ne : a ≠ b := fun e => absent (e ▸ ha)
      simp [pair, point, ne])
  simp [on,off] at same

theorem still_true (t : PlaneFormula α) (p b : α) (h : t.eval (point p) = true) :
    t.eval (pair p b) = true := eval_mono t (by
      intro a ha
      exact decide_eq_true (Or.inl (of_decide_eq_true ha))) h

def charges (line : L → α) (p : α) : PlaneFormula α → List (Finset L)
  | .bot | .leaf _ => []
  | .or s t => charges line p s ++ charges line p t
  | .and s t =>
      if s.eval (point p) then W line t :: charges line p t
      else if t.eval (point p) then W line s :: charges line p s else []

theorem charge_budget (line : L → α) (p : α) (t : PlaneFormula α) :
    (charges line p t).length ≤ t.leaves.count p := by
  have pays (a : PlaneFormula α) (h : a.eval (point p) = true) : 0 < a.leaves.count p := by
    obtain ⟨v,hv,ht⟩ := eval_triggered a _ h
    have hp : v = p := of_decide_eq_true ht
    exact List.count_pos_iff.mpr (hp ▸ hv)
  induction t with
  | bot | leaf => simp [charges]
  | or s t hs ht => simpa [charges,leaves] using Nat.add_le_add hs ht
  | and s t hs ht =>
    simp only [charges,leaves,List.count_append]
    split
    · rename_i h
      have := pays s h
      simp only [List.length_cons]
      omega
    · split
      · rename_i h
        have := pays t h
        simp only [List.length_cons]
        omega
      · simp

theorem charges_inside (line : L → α) (p : α) (t : PlaneFormula α) :
    ∀ z ∈ charges line p t, z ∈ pieces line t := by
  induction t with
  | bot | leaf => simp [charges]
  | or s t hs ht =>
    intro z hz
    rcases List.mem_append.mp hz with h | h
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (hs _ h))
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (ht _ h))
  | and s t hs ht =>
    intro z hz
    simp only [charges] at hz
    split at hz
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (root_mem line t))
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (ht _ hz))
    · split at hz
      · rcases List.mem_cons.mp hz with rfl | hz
        · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (root_mem line s))
        · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (hs _ hz))
      · contradiction

theorem sensitive (line : L → α) (p : α) (t : PlaneFormula α)
    (unique : ∀ l, t.leaves.count (line l) ≤ 1) (off : t.eval (point p) = false) (l : L) :
    t.eval (pair p (line l)) = true ↔ l ∈ W line t ∨ ∃ z ∈ charges line p t, l ∈ z := by
  have splitCounts {s t : PlaneFormula α} (h : ∀ l, (s.leaves ++ t.leaves).count (line l) ≤ 1) :
      (∀ l, s.leaves.count (line l) ≤ 1) ∧ (∀ l, t.leaves.count (line l) ≤ 1) := by
    constructor <;> intro j <;> have hj := h j <;> rw [List.count_append] at hj <;> omega
  induction t with
  | bot => simp [eval,W,charges]
  | leaf a =>
    have ne : a ≠ p := of_decide_eq_false off
    simp [eval, pair, ne, W, charges, eq_comm]
  | or s t hs ht =>
    obtain ⟨us,ut⟩ := splitCounts unique
    obtain ⟨os,ot⟩ := Bool.or_eq_false_iff.mp off
    simp only [eval, Bool.or_eq_true_iff, W, Finset.mem_union, charges, List.mem_append]
    have leftChange := hs us os
    have rightChange := ht ut ot
    grind
  | and s t hs ht =>
    obtain ⟨us,ut⟩ := splitCounts unique
    by_cases os : s.eval (point p) = true
    · have ot : t.eval (point p) = false := by simpa [eval,os] using off
      have on := still_true s p (line l) os
      simpa [eval,on,W,charges,os] using ht ut ot
    · have os' : s.eval (point p) = false := Bool.eq_false_iff.mpr os
      by_cases ot : t.eval (point p) = true
      · have on := still_true t p (line l) ot
        simpa [eval,on,W,charges,os',ot] using hs us os'
      · have ot' : t.eval (point p) = false := Bool.eq_false_iff.mpr ot
        have impossible : ¬ (s.eval (pair p (line l)) = true ∧ t.eval (pair p (line l)) = true) := by
          rintro ⟨a,b⟩
          have c := List.count_pos_iff.mpr (line_needed os' a)
          have d := List.count_pos_iff.mpr (line_needed ot' b)
          have bound := unique l
          change (s.leaves ++ t.leaves).count (line l) ≤ 1 at bound
          rw [List.count_append] at bound
          omega
        simpa [eval, W, charges, os', ot'] using impossible

theorem raw_support (line : L → α) (t : PlaneFormula α) {l : L}
    (h : l ∈ W line t) : line l ∈ t.leaves := by
  induction t with
  | bot | and => simp [W] at h
  | leaf a => simpa [W,leaves] using h
  | or s t hs ht =>
    rcases Finset.mem_union.mp h with h | h
    · exact List.mem_append_left _ (hs h)
    · exact List.mem_append_right _ (ht h)

theorem piece_support (line : L → α) (t : PlaneFormula α) {S : Finset L} {l : L}
    (inTree : S ∈ pieces line t) (mem : l ∈ S) : line l ∈ t.leaves := by
  induction t with
  | bot => simp [pieces] at inTree; simp [inTree] at mem
  | leaf a =>
    have e : S = W line (.leaf a) := Finset.mem_singleton.mp inTree
    exact raw_support _ _ (e ▸ mem)
  | or s t hs ht =>
    rcases Finset.mem_insert.mp inTree with e | sub
    · exact raw_support _ _ (e ▸ mem)
    · rcases Finset.mem_union.mp sub with h | h
      · exact List.mem_append_left _ (hs h)
      · exact List.mem_append_right _ (ht h)
  | and s t hs ht =>
    rcases Finset.mem_insert.mp inTree with e | sub
    · simp [e] at mem
    · rcases Finset.mem_union.mp sub with h | h
      · exact List.mem_append_left _ (hs h)
      · exact List.mem_append_right _ (ht h)

theorem singleton_accepts_raw (line : L → α) (t : PlaneFormula α) {l : L} (h : l ∈ W line t) :
    t.eval (point (line l)) = true := by
  induction t with
  | bot | and => simp [W] at h
  | leaf a =>
    have e : line l = a := (Finset.mem_filter.mp h).2
    simp [eval,point,e]
  | or s t hs ht => exact Bool.or_eq_true_iff.mpr ((Finset.mem_union.mp h).imp hs ht)

theorem empty_raw (line : L → α) (t : PlaneFormula α)
    (off : ∀ l, t.eval (point (line l)) = false) : W line t = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro l hl
  have := singleton_accepts_raw line t hl
  simp [off] at this

theorem tree_laminar (line : L → α) (t : PlaneFormula α) (uniq : ∀ l, t.leaves.count (line l) ≤ 1) :
    (∀ A ∈ pieces line t, A ⊆ W line t ∨ Disjoint A (W line t)) ∧
    (∀ A ∈ pieces line t, ∀ B ∈ pieces line t, Disjoint A B ∨ A ⊆ B ∨ B ⊆ A) := by
  have join (a b : PlaneFormula α) (root : Finset L) (u : ∀ l, (a.leaves ++ b.leaves).count (line l) ≤ 1)
      (form : root = W line a ∪ W line b ∨ root = ∅)
      (lh : (∀ A ∈ pieces line a, A ⊆ W line a ∨ Disjoint A (W line a)) ∧
        (∀ A ∈ pieces line a, ∀ B ∈ pieces line a, Disjoint A B ∨ A ⊆ B ∨ B ⊆ A))
      (rh : (∀ A ∈ pieces line b, A ⊆ W line b ∨ Disjoint A (W line b)) ∧
        (∀ A ∈ pieces line b, ∀ B ∈ pieces line b, Disjoint A B ∨ A ⊆ B ∨ B ⊆ A)) :
      let F := insert root (pieces line a ∪ pieces line b)
      (∀ A ∈ F, A ⊆ root ∨ Disjoint A root) ∧
        (∀ A ∈ F, ∀ B ∈ F, Disjoint A B ∨ A ⊆ B ∨ B ⊆ A) := by
    dsimp only
    have across {A B : Finset L} (ha : A ∈ pieces line a) (hb : B ∈ pieces line b) : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro l la lb
      have sa := List.count_pos_iff.mpr (piece_support line a ha la)
      have sb := List.count_pos_iff.mpr (piece_support line b hb lb)
      have ub := u l
      rw [List.count_append] at ub
      omega
    have rootCase (A : Finset L) (hA : A ∈ insert root (pieces line a ∪ pieces line b)) :
        A ⊆ root ∨ Disjoint A root := by
      rcases Finset.mem_insert.mp hA with rfl | sub
      · exact Or.inl (fun _ h => h)
      rcases form with rfl | rfl
      · rcases Finset.mem_union.mp sub with al | ar
        · rcases lh.1 A al with h | h
          · exact Or.inl (h.trans Finset.subset_union_left)
          · exact Or.inr (Finset.disjoint_union_right.mpr ⟨h,across al (root_mem line b)⟩)
        · rcases rh.1 A ar with h | h
          · exact Or.inl (h.trans Finset.subset_union_right)
          · exact Or.inr (Finset.disjoint_union_right.mpr ⟨(across (root_mem line a) ar).symm,h⟩)
      · simp
    refine ⟨rootCase, ?_⟩
    intro A hA B hB
    rcases Finset.mem_insert.mp hA with rfl | asub
    · rcases rootCase B hB with h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl h.symm
    rcases Finset.mem_insert.mp hB with rfl | bsub
    · rcases rootCase A hA with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
    rcases Finset.mem_union.mp asub with al | ar <;> rcases Finset.mem_union.mp bsub with bl | br
    · exact lh.2 A al B bl
    · exact Or.inl (across al br)
    · exact Or.inl (across bl ar).symm
    · exact rh.2 A ar B br
  have child {s t : PlaneFormula α} (u : ∀ l, (s.leaves ++ t.leaves).count (line l) ≤ 1) :
      (∀ l, s.leaves.count (line l) ≤ 1) ∧ (∀ l, t.leaves.count (line l) ≤ 1) := by
    constructor <;> intro l <;> have h := u l <;> rw [List.count_append] at h <;> omega
  induction t with
  | bot | leaf => simp [pieces,W]
  | or s t hs ht => exact join _ _ _ uniq (Or.inl rfl) (hs (child uniq).1) (ht (child uniq).2)
  | and s t hs ht => exact join _ _ _ uniq (Or.inr rfl) (hs (child uniq).1) (ht (child uniq).2)

theorem small_sensitivity (line : L → α) (p : α) (t : PlaneFormula α)
    (unique : ∀ l, t.leaves.count (line l) ≤ 1) (pSmall : t.leaves.count p ≤ 2)
    (pOff : t.eval (point p) = false) (lOff : ∀ l, t.eval (point (line l)) = false) :
    ∃ A ∈ insert ∅ (pieces line t), ∃ B ∈ insert ∅ (pieces line t),
      ∀ l, t.eval (pair p (line l)) = true ↔ l ∈ A ∪ B := by
  let cs := charges line p t
  have nb : cs.length ≤ 2 := (charge_budget line p t).trans pSmall
  have mem : ∀ A ∈ cs, A ∈ insert ∅ (pieces line t) := fun A h =>
    Finset.mem_insert_of_mem (charges_inside line p t A h)
  have cover (l : L) : t.eval (pair p (line l)) = true ↔ ∃ A ∈ cs, l ∈ A := by
    simpa [empty_raw line t lOff,cs] using sensitive line p t unique pOff l
  cases eqn : cs with
  | nil =>
    refine ⟨∅,by simp,∅,by simp,?_⟩
    simpa [eqn] using cover
  | cons a as =>
    have ha := mem a (by simp [eqn])
    cases ea : as with
    | nil =>
      refine ⟨a,ha,∅,by simp,?_⟩
      simpa [eqn,ea] using cover
    | cons b bs =>
      have hb := mem b (by simp [eqn,ea])
      have eb : bs = [] := by simpa [eqn,ea] using nb
      refine ⟨a,ha,b,hb,?_⟩
      simpa [eqn,ea,eb,Finset.mem_union] using cover

theorem common_laminar (line : L → α) (t : PlaneFormula α)
    (unique : ∀ l, t.leaves.count (line l) ≤ 1) :
    ∀ A ∈ insert ∅ (pieces line t), ∀ B ∈ insert ∅ (pieces line t),
      Disjoint A B ∨ A ⊆ B ∨ B ⊆ A := by
  intro A ha B hb
  rcases Finset.mem_insert.mp ha with rfl | ha
  · simp
  rcases Finset.mem_insert.mp hb with rfl | hb
  · simp
  exact (tree_laminar line t unique).2 A ha B hb

theorem incidence_cover {P : Type} (inc : P → L → Prop) [DecidableRel inc]
    (pin : P → α) (line : L → α) (t : PlaneFormula α)
    (unique : ∀ l, t.leaves.count (line l) ≤ 1)
    (pSmall : ∀ p, t.leaves.count (pin p) ≤ 2)
    (pOff : ∀ p, t.eval (point (pin p)) = false)
    (lOff : ∀ l, t.eval (point (line l)) = false)
    (edges : ∀ p l, t.eval (pair (pin p) (line l)) = true ↔ inc p l) :
    ∃ family : Set (Finset L),
      (∀ A ∈ family, ∀ B ∈ family, Disjoint A B ∨ A ⊆ B ∨ B ⊆ A) ∧
      ∀ p, ∃ A ∈ family, ∃ B ∈ family, Finset.univ.filter (inc p) = A ∪ B := by
  refine ⟨↑(insert ∅ (pieces line t)), common_laminar line t unique, ?_⟩
  intro p
  obtain ⟨A,ha,B,hb,eqn⟩ := small_sensitivity line (pin p) t unique (pSmall p) (pOff p) lOff
  refine ⟨A,ha,B,hb,?_⟩
  ext l
  simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using (edges p l).symm.trans (eqn l)

end Trace
end PlaneFormula
end

-- PlaneLaminarBudget
section
open Finset

theorem laminarPieceBudget {n : ℕ} (neighbors : Fin n → Finset (Fin n))
    (family : Set (Finset (Fin n))) (pieces : Fin n → Finset (Finset (Fin n)))
    (inside : ∀ p a, a ∈ pieces p → a ∈ family)
    (linear : ∀ p r, p ≠ r → (neighbors p ∩ neighbors r).card ≤ 1)
    (laminar : ∀ a ∈ family, ∀ b ∈ family, Disjoint a b ∨ a ⊆ b ∨ b ⊆ a)
    (cover : ∀ p, neighbors p = (pieces p).biUnion id) :
    ∑ p, (neighbors p).card ≤ n + ∑ p, (pieces p).card := by
  classical
  let big (p : Fin n) := ((pieces p).filter (fun a => 2 ≤ a.card)).biUnion id
  let small (p : Fin n) := (pieces p).filter (fun a => a.card ≤ 1)
  have included {p a} (h : a ∈ pieces p) : a ⊆ neighbors p := by
    rw [cover p]
    exact fun _ hx => mem_biUnion.mpr ⟨a, h, hx⟩
  have noNest {p r a b} (ne : p ≠ r) (ha : a ∈ pieces p) (large : 2 ≤ a.card)
      (hb : b ∈ pieces r) (nest : a ⊆ b) : False := by
    have sub := subset_inter (included ha) (Subset.trans nest (included hb))
    have low := card_le_card sub
    have high := linear p r ne
    omega
  have disj : ((univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint big := by
    intro p _ r _ ne
    apply disjoint_left.mpr
    intro l hl hr
    obtain ⟨a, ha, hla⟩ := mem_biUnion.mp hl
    obtain ⟨b, hb, hlb⟩ := mem_biUnion.mp hr
    obtain ⟨ha, la⟩ := mem_filter.mp ha
    obtain ⟨hb, lb⟩ := mem_filter.mp hb
    rcases laminar _ (inside p a ha) _ (inside r b hb) with sep | ab | ba
    · exact disjoint_left.mp sep hla hlb
    · exact noNest ne ha la hb ab
    · exact noNest ne.symm hb lb ha ba
  have allBig := card_le_univ (univ.biUnion big)
  rw [card_biUnion disj, Fintype.card_fin] at allBig
  have rowBound (p : Fin n) : (neighbors p).card ≤ (big p).card + (pieces p).card := by
    have covers : neighbors p ⊆ big p ∪ (small p).biUnion id := by
      rw [cover p]
      intro l hl
      obtain ⟨a, ha, hit⟩ := mem_biUnion.mp hl
      by_cases large : 2 ≤ a.card
      · exact mem_union_left _ (mem_biUnion.mpr ⟨a, mem_filter.mpr ⟨ha,large⟩, hit⟩)
      · exact mem_union_right _ (mem_biUnion.mpr ⟨a, mem_filter.mpr ⟨ha,by omega⟩, hit⟩)
    have smallBound : ((small p).biUnion id).card ≤ (pieces p).card := by
      calc
        _ ≤ ∑ a ∈ small p, a.card := card_biUnion_le
        _ ≤ ∑ _a ∈ small p, 1 := sum_le_sum fun a ha => (mem_filter.mp ha).2
        _ = (small p).card := by simp
        _ ≤ _ := card_le_card (filter_subset _ _)
    exact (card_le_card covers).trans ((card_union_le ..).trans (Nat.add_le_add_left smallBound _))
  have total := sum_le_sum (s := univ) (fun p _ => rowBound p)
  rw [sum_add_distrib] at total
  omega

theorem regularLaminarPieceBudget {n q : ℕ} (neighbors : Fin n → Finset (Fin n))
    (family : Set (Finset (Fin n))) (pieces : Fin n → Finset (Finset (Fin n)))
    (degree : ∀ p, (neighbors p).card = q + 1)
    (inside : ∀ p a, a ∈ pieces p → a ∈ family)
    (linear : ∀ p r, p ≠ r → (neighbors p ∩ neighbors r).card ≤ 1)
    (laminar : ∀ a ∈ family, ∀ b ∈ family, Disjoint a b ∨ a ⊆ b ∨ b ⊆ a)
    (cover : ∀ p, neighbors p = (pieces p).biUnion id) :
    n * q ≤ ∑ p, (pieces p).card := by
  have bound := laminarPieceBudget neighbors family pieces inside linear laminar cover
  simpa [degree, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using bound
end

-- PlaneFormulaLower
section
open Finset PlaneFormula PlaneFormula.Trace

theorem planeFormulaPointOccurrences {α : Type} [DecidableEq α] {n q : ℕ}
    (inc : Fin n → Fin n → Prop) [DecidableRel inc]
    (pin line : Fin n → α) (t : PlaneFormula α)
    (degree : ∀ p, (univ.filter (inc p)).card = q + 1)
    (linear : ∀ p r, p ≠ r → ((univ.filter (inc p)) ∩ (univ.filter (inc r))).card ≤ 1)
    (unique : ∀ l, t.leaves.count (line l) ≤ 1)
    (pOff : ∀ p, t.eval (point (pin p)) = false)
    (lOff : ∀ l, t.eval (point (line l)) = false)
    (edges : ∀ p l, t.eval (pair (pin p) (line l)) = true ↔ inc p l) :
    n * q ≤ ∑ p, t.leaves.count (pin p) := by
  let N (p : Fin n) := univ.filter (inc p)
  let family : Set (Finset (Fin n)) := ↑(pieces line t)
  let use (p : Fin n) := (charges line (pin p) t).toFinset
  have sub (p : Fin n) (A : Finset (Fin n)) (h : A ∈ use p) : A ∈ family :=
    charges_inside line (pin p) t A (List.mem_toFinset.mp h)
  have eqn (p : Fin n) : N p = (use p).biUnion id := by
    ext l
    have cover := sensitive line (pin p) t unique (pOff p) l
    rw [empty_raw line t lOff] at cover
    simpa [N, use] using (edges p l).symm.trans cover
  have bound := regularLaminarPieceBudget N family use degree sub linear
    (tree_laminar line t unique).2 eqn
  refine bound.trans (sum_le_sum (fun p _ => ?_))
  exact (List.toFinset_card_le _).trans (charge_budget line (pin p) t)
end

-- PlaneTwoShores
section
open Finset PlaneFormula.Trace

theorem fewOccurrencesImpossible {α : Type} [DecidableEq α] {n q : ℕ}
    (hn : 0 < n) (hq : 2 < q)
    (inc : Fin n → Fin n → Prop) [DecidableRel inc] (pin line : Fin n → α) (t : PlaneFormula α)
    (degree : ∀ p, (univ.filter (inc p)).card = q + 1)
    (linear : ∀ p r, p ≠ r → ((univ.filter (inc p)) ∩ (univ.filter (inc r))).card ≤ 1)
    (p2 : ∀ p, t.leaves.count (pin p) ≤ 2)
    (l1 : ∀ l, t.leaves.count (line l) ≤ 1)
    (pOff : ∀ p, t.eval (point (pin p)) = false)
    (lOff : ∀ l, t.eval (point (line l)) = false)
    (edges : ∀ p l, t.eval (pair (pin p) (line l)) = true ↔ inc p l) : False := by
  have low := planeFormulaPointOccurrences inc pin line t degree linear l1 pOff lOff edges
  have high := sum_le_sum (s := (univ : Finset (Fin n))) (fun p _ => p2 p)
  simp at high
  have gap := Nat.mul_lt_mul_of_pos_left hq hn
  omega

theorem twoShoresImpossible {n q : ℕ} (hn : 0 < n) (hq : 2 < q)
    (I : Fin n → Fin n → Prop) [DecidableRel I] (t : PlaneFormula (Fin (n+n)))
    (rows : ∀ p, Fintype.card {l // I p l} = q+1)
    (cols : ∀ l, Fintype.card {p // I p l} = q+1)
    (join : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (off : ∀ v, t.eval (point v) = false)
    (edges : ∀ p l, t.eval (pair (Fin.castAdd n p) (Fin.natAdd n l)) = true ↔ I p l)
    (counts :
      ((∀ p, t.leaves.count (Fin.castAdd n p) ≤ 2) ∧ (∀ l, t.leaves.count (Fin.natAdd n l) ≤ 1)) ∨
      ((∀ p, t.leaves.count (Fin.castAdd n p) ≤ 1) ∧ (∀ l, t.leaves.count (Fin.natAdd n l) ≤ 2))) :
    False := by
  classical
  have rect {p r a b} (diff : p ≠ r) (pa : I p a) (ra : I r a) (pb : I p b) (rb : I r b) :
      a = b := (join p r diff).unique ⟨pa,ra⟩ ⟨pb,rb⟩
  rcases counts with ⟨p2,l1⟩ | ⟨p1,l2⟩
  · refine fewOccurrencesImpossible hn hq I (Fin.castAdd n) (Fin.natAdd n) t ?_ ?_ p2 l1
      (fun p => off _) (fun l => off _) edges
    · intro p
      exact (Fintype.card_subtype (I p)).symm.trans (rows p)
    · intro p r diff
      apply card_le_one_iff.mpr
      intro a b ha hb
      simp only [mem_inter, mem_filter, mem_univ, true_and] at ha hb
      exact rect diff ha.1 ha.2 hb.1 hb.2
  · refine fewOccurrencesImpossible hn hq (fun l p => I p l) (Fin.natAdd n) (Fin.castAdd n) t
      ?_ ?_ l2 p1 (fun l => off _) (fun p => off _) ?_
    · intro l
      exact (Fintype.card_subtype (fun p => I p l)).symm.trans (cols l)
    · intro l k diff
      apply card_le_one_iff.mpr
      intro p r hp hr
      simp only [mem_inter, mem_filter, mem_univ, true_and] at hp hr
      by_contra ne
      exact diff (rect ne hp.1 hr.1 hp.2 hr.2)
    · intro l p
      have symmetric : pair (Fin.natAdd n l) (Fin.castAdd n p) =
          pair (Fin.castAdd n p) (Fin.natAdd n l) := by
        funext u
        simp [pair, or_comm]
      rw [symmetric]
      exact edges p l
end

-- PlaneTightFanout
section
namespace PlaneTightFanout

open Plane2866Graph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Classical

noncomputable def fanoutFloor (n : ℕ) (C : Circuit) (a : ℕ) : ℕ :=
  (if a = C.output then 0 else 1) + (if Branch n C a then 1 else 0)

noncomputable def parents (n : ℕ) (C : Circuit) (j : ℕ) : Finset ℕ :=
  (living n C).filter (fun i => LNext n C i j)

structure Tight (n : ℕ) (C : Circuit) : Prop where
  all_live : living n C = Finset.range (n + C.size)
  outgoing : ∀ a ∈ living n C, (readers n C a).card = fanoutFloor n C a
  incoming : ∀ j ∈ living n C, (parents n C j).card = if j < n then 0 else 2

theorem output_readers (n : ℕ) (C : Circuit) : readers n C C.output = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j h
  have hj := mem_readers.mp h
  exact (Nat.not_lt_of_ge (next_le hj.2)) hj.1.1

-- Equality in the two edge counts in Plane2866Graph.branch_budget is pointwise.
theorem tight_of_budget {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}
    (hC : Monotone2 C) (he : GraphEval C G)
    (hdegree : ∀ v : Fin n, ∃ u, G.Adj v u) (ho : C.output ∈ living n C)
    (tight : n + ((living n C).filter (Branch n C)).card = C.size + 1) : Tight n C := by
  classical
  let W := living n C
  let S := W.filter (fun j => ¬ j < n)
  let B := W.filter (Branch n C)
  let R := W.erase C.output
  have inputs : Finset.range n ⊆ W := by
    intro v hv
    have hv' := Finset.mem_range.mp hv
    obtain ⟨u,hu⟩ := hdegree ⟨v,hv'⟩
    exact mem_living.mpr ⟨by omega, input_live he hu⟩
  have numW : W.card = n + S.card := by
    have h := Finset.card_sdiff_add_card_eq_card inputs
    have diff : W \ Finset.range n = S := by ext a; simp [S]
    rw [diff, Finset.card_range] at h
    omega
  have numR : R.card + 1 = W.card := Finset.card_erase_add_one ho
  have Wsub : W ⊆ Finset.range (n+C.size) := fun _ hw => Finset.mem_range.mpr (mem_living.mp hw).1
  have boundW : W.card ≤ n+C.size := by simpa using Finset.card_le_card Wsub
  have lo : ∀ a ∈ W, fanoutFloor n C a ≤ (readers n C a).card := by
    intro a ha
    by_cases out : a = C.output
    · subst a
      simp [fanoutFloor, Branch, output_readers]
    · by_cases branch : Branch n C a
      · simpa [fanoutFloor, out, branch] using (show 2 ≤ (readers n C a).card from branch)
      · simpa [fanoutFloor, out, branch] using
          (Finset.card_pos.mpr (live_readers_nonempty (mem_living.mp ha).2 out))
  have loTotal : (∑ a ∈ W, fanoutFloor n C a) = R.card + B.card := by
    unfold fanoutFloor
    rw [Finset.sum_add_distrib]
    congr 1
    · calc
        _ = ∑ a ∈ W, (if a ≠ C.output then 1 else 0 : ℕ) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : a = C.output <;> simp [h]
        _ = R.card := by rw [← Finset.sum_filter]; simp [R, Finset.filter_ne']
    · rw [← Finset.sum_filter]
      simp [B]
  have edges : (∑ a ∈ W, (readers n C a).card) = ∑ j ∈ W, (parents n C j).card := by
    simp_rw [parents, readers_filter, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hi : ∀ j ∈ W, (parents n C j).card ≤ if j < n then 0 else 2 :=
    fun j hj => incoming_bound hC hj
  have hiTotal : (∑ j ∈ W, (if j < n then 0 else 2 : ℕ)) = 2*S.card := by
    simp [S, Finset.sum_ite, Nat.mul_comm]
  have loSum := Finset.sum_le_sum lo
  have hiSum := Finset.sum_le_sum hi
  change n + B.card = C.size + 1 at tight
  have eqW : W.card = n+C.size := by omega
  have eqLo : (∑ a ∈ W, fanoutFloor n C a) = ∑ a ∈ W, (readers n C a).card := by omega
  have eqHi : (∑ j ∈ W, (parents n C j).card) = ∑ j ∈ W, (if j < n then 0 else 2) := by omega
  refine ⟨Finset.eq_of_subset_of_card_le Wsub (by simpa using eqW.ge), ?_, ?_⟩
  · intro a ha
    exact ((Finset.sum_eq_sum_iff_of_le lo).mp eqLo a ha).symm
  · exact (Finset.sum_eq_sum_iff_of_le hi).mp eqHi

theorem fanout_cases {n : ℕ} {C : Circuit} (h : Tight n C) {a : ℕ}
    (ha : a ∈ living n C) :
    (a = C.output → (readers n C a).card = 0) ∧
    (Branch n C a → (readers n C a).card = 2) ∧
    (a ≠ C.output → ¬ Branch n C a → (readers n C a).card = 1) := by
  constructor
  · rintro rfl
    simp [output_readers]
  constructor
  · intro hb
    have hn : a ≠ C.output := by
      rintro rfl
      simp [Branch, output_readers] at hb
    simpa [fanoutFloor, hn, hb] using h.outgoing a ha
  · intro hn hb
    simpa [fanoutFloor, hn, hb] using h.outgoing a ha

theorem gate_inputs {n : ℕ} {C : Circuit} (hm : Monotone2 C) (h : Tight n C)
    {p : ℕ} {g : Gate} (hg : C.gates[p]? = some g) :
    Live n C (n+p) ∧ ∃ i j, g.inputs = [i,j] ∧ i ≠ j ∧ i < n+p ∧ j < n+p := by
  have hp := (List.getElem?_eq_some_iff.mp hg).1
  have live : n+p ∈ living n C := by
    rw [h.all_live, Finset.mem_range]
    exact Nat.add_lt_add_left hp n
  refine ⟨(mem_living.mp live).2, ?_⟩
  have two : (parents n C (n+p)).card = 2 := by simpa using h.incoming (n+p) live
  obtain ⟨a,b,ha,hb,ne⟩ := Finset.one_lt_card_iff.mp (show 1 < (parents n C (n+p)).card by omega)
  have member (x : ℕ) (hx : x ∈ parents n C (n+p)) : x ∈ g.inputs ∧ x < n+p := by
    obtain ⟨_,⟨lt,k,g',hk,eq,mem⟩,_⟩ := Finset.mem_filter.mp hx
    have ek : k = p := by omega
    subst k
    rw [hg] at hk
    cases hk
    exact ⟨mem,lt⟩
  obtain ⟨ha,la⟩ := member a ha
  obtain ⟨hb,lb⟩ := member b hb
  have arity := (hm g (List.mem_of_getElem? hg)).2
  rcases list : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k,rest⟩⟩⟩
  · simp [list] at ha
  · simp [list] at ha hb
    exact (ne (ha.trans hb.symm)).elim
  · refine ⟨i,j,rfl, ?_⟩
    simp [list] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> omega
  · simp [list] at arity

theorem all_zero {n : ℕ} {C : Circuit} (hm : Monotone2 C) (h : Tight n C) :
    ∀ j, val C (point (∅ : Finset (Fin n))) j = false := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    by_cases input : j < n
    · rw [val_input C _ (⟨j,input⟩ : Fin n)]
      simp [point]
    by_cases far : n+C.gates.length ≤ j
    · exact val_beyond C _ far
    obtain ⟨p,hp,rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.mpr ⟨hp,rfl⟩
    obtain ⟨_,a,b,ins,_,ha,hb⟩ := gate_inputs hm h hg
    rw [val_gate C _ hg, ins]
    have ops := (hm g (List.mem_of_getElem? hg)).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ops
    rcases ops with op | op <;>
      simp [op, GateOp.eval, operand, ha, hb, ih a ha, ih b hb]

abbrev Wire (n : ℕ) (C : Circuit) := Fin (n+C.size)

noncomputable def wireParents (n : ℕ) (C : Circuit) (w : Wire n C) : Finset (Wire n C) :=
  Finset.univ.filter fun u => LNext n C u w

noncomputable def branchCuts (n : ℕ) (C : Circuit) : Finset (Wire n C) :=
  Finset.univ.filter fun u => Branch n C u

@[simp] theorem mem_wireParents {n : ℕ} {C : Circuit} {u w : Wire n C} :
    u ∈ wireParents n C w ↔ LNext n C u w := by simp [wireParents]

@[simp] theorem mem_branchCuts {n : ℕ} {C : Circuit} {u : Wire n C} :
    u ∈ branchCuts n C ↔ Branch n C u := by simp [branchCuts]

theorem root_not_cut {n : ℕ} {C : Circuit} (ho : C.output < n+C.size) :
    (⟨C.output,ho⟩ : Wire n C) ∉ branchCuts n C := by
  simp [Branch, output_readers]

theorem wireParents_input {n : ℕ} {C : Circuit} {w : Wire n C} (input : w.val < n) :
    wireParents n C w = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨⟨_,p,_,_,eq,_⟩,_⟩ := mem_wireParents.mp hu
  omega

theorem wireParents_gate {n : ℕ} {C : Circuit} (h : Tight n C)
    {w i j : Wire n C} {p : ℕ} {g : Gate} (hg : C.gates[p]? = some g)
    (hw : w.val = n+p) (ins : g.inputs = [i.val,j.val]) (hi : i.val < w.val)
    (hj : j.val < w.val) : wireParents n C w = {i,j} := by
  have live : Live n C w := (mem_living.mp (h.all_live.symm ▸ Finset.mem_range.mpr w.isLt)).2
  ext u
  rw [mem_wireParents, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨_,k,g',hk,eq,mem⟩,_⟩
    have same : k = p := by omega
    subst k
    rw [hg] at hk
    cases hk
    simp [ins] at mem
    exact mem.imp Fin.ext Fin.ext
  · rintro (rfl | rfl)
    · exact ⟨⟨hi,p,g,hg,hw,by simp [ins]⟩,live⟩
    · exact ⟨⟨hj,p,g,hg,hw,by simp [ins]⟩,live⟩

theorem wire_fanout {n : ℕ} {C : Circuit} (h : Tight n C)
    (ho : C.output < n+C.size) (u : Wire n C) :
    (Finset.univ.filter fun w => u ∈ wireParents n C w).card =
      if u = (⟨C.output,ho⟩ : Wire n C) then 0 else if u ∈ branchCuts n C then 2 else 1 := by
  classical
  let U := Finset.univ.filter fun w => u ∈ wireParents n C w
  let embedding : Wire n C ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  have same : U.map embedding = readers n C u.val := by
    ext v
    rw [Finset.mem_map, mem_readers]
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact mem_wireParents.mp (Finset.mem_filter.mp hw).2
    · intro edge
      exact ⟨⟨v,next_in_range edge.1⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,mem_wireParents.mpr edge⟩,rfl⟩
  have live : u.val ∈ living n C := h.all_live.symm ▸ Finset.mem_range.mpr u.isLt
  change U.card = _
  rw [← Finset.card_map (f := embedding) (s := U), same]
  by_cases out : u.val = C.output
  · have eq : u = ⟨C.output,ho⟩ := Fin.ext out
    simp [eq, output_readers]
  · have neq : u ≠ ⟨C.output,ho⟩ := fun eq => out (congrArg Fin.val eq)
    rw [ite_eq_right neq]
    rcases fanout_cases h live with ⟨_,hb,hn⟩
    by_cases b : Branch n C u
    · rw [ite_eq_left (mem_branchCuts.mpr b)]
      exact hb b
    · rw [ite_eq_right (fun hc => b (mem_branchCuts.mp hc))]
      exact hn out b

end PlaneTightFanout
end

-- PlaneEqualityContext
section
namespace PlaneEqualityContext

open Plane2866Graph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Classical

-- Incidence geometry and the pair tests below are factored from linearLower in PR 7096,
-- whose incidence argument credits the accepted reduction in PR 5439.

abbrev L {N : ℕ} : Fin N → Fin (N+N) := Fin.castAdd N
abbrev R {N : ℕ} : Fin N → Fin (N+N) := Fin.natAdd N
theorem sides {N : ℕ} (p l : Fin N) : L p ≠ R l := by
  intro equal
  have val := congrArg Fin.val equal
  change p.val = N + l.val at val
  have inRange := p.isLt
  omega
theorem leftInjective {N : ℕ} : Function.Injective (@L N) := by
  intro a b eq
  have valuations : (L a).val = (L b).val := congrArg Fin.val eq
  exact Fin.ext valuations
theorem rightInjective {N : ℕ} : Function.Injective (@R N) := by
  intro a b eq
  have val := congrArg Fin.val eq
  change N + a.val = N + b.val at val
  exact Fin.ext (by omega)
def incidenceGraph {N : ℕ} (I : Fin N → Fin N → Prop) : SimpleGraph (Fin (N+N)) :=
  SimpleGraph.fromRel (fun x y => ∃ p l, x = L p ∧ y = R l ∧ I p l)
theorem adjEither {N : ℕ} (I : Fin N → Fin N → Prop) (x y : Fin (N+N)) :
    (incidenceGraph I).Adj x y ↔
      (∃ p l, x = L p ∧ y = R l ∧ I p l) ∨ (∃ p l, y = L p ∧ x = R l ∧ I p l) := by
  unfold incidenceGraph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · exact And.right
  · intro ok
    refine ⟨?_,ok⟩
    rintro rfl
    rcases ok with ⟨p,l,atP,atL,_⟩ | ⟨p,l,atP,atL,_⟩
    · exact sides p l (atP.symm.trans atL)
    · exact sides p l (atP.symm.trans atL)
theorem leftNeighbors {N : ℕ} (I : Fin N → Fin N → Prop) (p : Fin N) (y : Fin (N+N)) :
    (incidenceGraph I).Adj (L p) y ↔ ∃ l, y = R l ∧ I p l := by
  rw [adjEither]
  constructor
  · rintro (⟨p',l,atP,atL,inc⟩ | ⟨p',l,_,invalid,_⟩)
    · exact ⟨l, atL, (leftInjective atP).symm ▸ inc⟩
    · exact (sides p l invalid).elim
  · rintro ⟨l,eq,inc⟩
    exact Or.inl ⟨p,l,rfl,eq,inc⟩
theorem rightNeighbors {N : ℕ} (I : Fin N → Fin N → Prop) (l : Fin N) (y : Fin (N+N)) :
    (incidenceGraph I).Adj (R l) y ↔ ∃ p, y = L p ∧ I p l := by
  rw [adjEither]
  constructor
  · rintro (⟨p,l',invalid,_,_⟩ | ⟨p,l',atP,atL,inc⟩)
    · exact (sides p l invalid.symm).elim
    · exact ⟨p,atP,(rightInjective atL).symm ▸ inc⟩
  · rintro ⟨p,eq,inc⟩
    exact Or.inr ⟨p,l,eq,rfl,inc⟩
theorem leftRight {N : ℕ} (I : Fin N → Fin N → Prop) (p l : Fin N) :
    (incidenceGraph I).Adj (L p) (R l) ↔ I p l := by
  rw [leftNeighbors]
  constructor
  · rintro ⟨k,eq,inc⟩
    exact (rightInjective eq).symm ▸ inc
  · exact fun inc => ⟨l,rfl,inc⟩
theorem noFour {N : ℕ} (I : Fin N → Fin N → Prop)
    (unique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (u v a b : Fin (N+N)) (vertices : u ≠ v) (neighbors : a ≠ b)
    (ua : (incidenceGraph I).Adj u a) (ub : (incidenceGraph I).Adj u b)
    (va : (incidenceGraph I).Adj v a) (vb : (incidenceGraph I).Adj v b) : False := by
  have crosses (p l : Fin N) (otherP otherL : Fin (N+N))
      (differentP : L p ≠ otherP) (differentL : R l ≠ otherL)
      (pl : I p l) (pOther : (incidenceGraph I).Adj (L p) otherL)
      (otherL' : (incidenceGraph I).Adj otherP (R l)) (pair : (incidenceGraph I).Adj otherP otherL) : False := by
    obtain ⟨k, rfl, pk⟩ := (leftNeighbors I p otherL).mp pOther
    obtain ⟨r, rfl, rl⟩ := (rightNeighbors I l otherP).mp ((incidenceGraph I).adj_symm otherL')
    have rk := (leftRight I r k).mp pair
    have distinct : p ≠ r := fun eq => differentP (congrArg L eq)
    have same := (unique p r distinct).unique ⟨pl,rl⟩ ⟨pk,rk⟩
    exact differentL (congrArg R same)
  rcases (adjEither I u a).mp ua with ⟨p,l,rfl,rfl,pl⟩ | ⟨p,l,rfl,rfl,pl⟩
  · exact crosses p l v b vertices neighbors pl ub va vb
  · exact crosses p l b v neighbors vertices pl ((incidenceGraph I).adj_symm va) ((incidenceGraph I).adj_symm ub) ((incidenceGraph I).adj_symm vb)
theorem enoughNeighbors (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (big : 101 ≤ q) (order : N = q^2+q+1)
    (degree : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1)
    (unique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (v : Fin (N+N)) : ∃ a b, a ≠ b ∧ (incidenceGraph I).Adj v a ∧ (incidenceGraph I).Adj v b := by
  classical
  have roomy : q+1 < N := by rw [order]; nlinarith
  have pointsOn (l : Fin N) : (Finset.univ.filter fun p : Fin N => I p l).card = q+1 :=
    (Fintype.card_subtype (fun p => I p l)).symm.trans (degree l)
  have outside (l : Fin N) : ∃ p, ¬ I p l := by
    by_contra! every
    have full : (Finset.univ.filter fun p : Fin N => I p l) = Finset.univ := by ext p; simp [every]
    have count := pointsOn l
    rw [full] at count
    simp at count
    omega
  have twoPoints : ∃ a b : Fin N, a ≠ b := by
    obtain ⟨a,b,_,_,distinct⟩ := Finset.one_lt_card_iff.mp
      (show 1 < (Finset.univ : Finset (Fin N)).card from by simp; omega)
    exact ⟨a,b,distinct⟩
  refine Fin.addCases (fun p => ?_) (fun l => ?_) v
  · obtain ⟨a,b,distinct⟩ := twoPoints
    have other : ∃ r : Fin N, p ≠ r := by by_cases eq : p=a; exact ⟨b,eq ▸ distinct⟩; exact ⟨a,eq⟩
    obtain ⟨r,diff⟩ := other
    obtain ⟨l,onL,_⟩ := unique p r diff
    obtain ⟨z,off⟩ := outside l
    have newPoint : p ≠ z := fun eq => off (eq ▸ onL.1)
    obtain ⟨k,onK,_⟩ := unique p z newPoint
    have otherLine : l ≠ k := fun eq => off (eq ▸ onK.2)
    exact ⟨R l,R k,fun eq => otherLine (rightInjective eq),(leftRight I p l).mpr onL.1,
      (leftRight I p k).mpr onK.1⟩
  · obtain ⟨a,b,memA,memB,distinct⟩ := Finset.one_lt_card_iff.mp
      (show 1 < (Finset.univ.filter fun p : Fin N => I p l).card from by rw [pointsOn]; omega)
    exact ⟨L a,L b,fun eq => distinct (leftInjective eq),
      (incidenceGraph I).adj_symm ((leftRight I a l).mpr (Finset.mem_filter.mp memA).2),
      (incidenceGraph I).adj_symm ((leftRight I b l).mpr (Finset.mem_filter.mp memB).2)⟩
theorem pointDegree (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (positive : 0 < q) (order : N = q^2+q+1)
    (degrees : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1)
    (unique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (p : Fin N) : (Finset.univ.filter fun l : Fin N => I p l).card = q+1 := by
  classical
  let through := Finset.univ.filter (fun l : Fin N => I p l)
  let rest (l : Fin N) := Finset.univ.filter (fun r : Fin N => I r l ∧ r ≠ p)
  have count (l : Fin N) (hl : l ∈ through) : (rest l).card = q := by
    let full := Finset.univ.filter (fun r : Fin N => I r l)
    have same : rest l = full.erase p := by ext r; simp [rest,full,and_comm]
    have inFull : p ∈ full := Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hl).2⟩
    have cardFull : full.card = q+1 := (Fintype.card_subtype (fun r => I r l)).symm.trans (degrees l)
    rw [same,Finset.card_erase_of_mem inFull,cardFull]
    omega
  have disjoint : (↑through : Set (Fin N)).PairwiseDisjoint rest := by
    intro l other k more different
    refine Finset.disjoint_left.mpr ?_
    intro r here there
    have throughL : I p l := (Finset.mem_filter.mp other).2
    have throughK : I p k := (Finset.mem_filter.mp more).2
    obtain ⟨rl,diff⟩ := (Finset.mem_filter.mp here).2
    have rk := (Finset.mem_filter.mp there).2.1
    exact different ((unique p r (Ne.symm diff)).unique ⟨throughL,rl⟩ ⟨throughK,rk⟩)
  have together : through.biUnion rest = Finset.univ.erase p := by
    ext r
    constructor
    · intro seen
      obtain ⟨l,_,rl⟩ := Finset.mem_biUnion.mp seen
      exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp rl).2.2,Finset.mem_univ _⟩
    · intro seen
      have diff := (Finset.mem_erase.mp seen).1
      obtain ⟨l,⟨pl,rl⟩,_⟩ := unique p r (Ne.symm diff)
      exact Finset.mem_biUnion.mpr ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,pl⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,rl,diff⟩⟩
  have rightSize : (Finset.univ.erase p).card = (q+1)*q := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,Fintype.card_fin,order]
    rw [Nat.add_sub_cancel]
    ring
  have scale : through.card*q = (q+1)*q := by
    calc
      through.card*q = ∑ l ∈ through, q := by simp
      _ = ∑ l ∈ through, (rest l).card := Finset.sum_congr rfl (fun l hl => (count l hl).symm)
      _ = (through.biUnion rest).card := (Finset.card_biUnion disjoint).symm
      _ = (q+1)*q := by rw [together,rightSize]
  exact Nat.eq_of_mul_eq_mul_right positive scale
theorem coverBudget (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (rowDegree : ∀ p : Fin N, (Finset.univ.filter fun l : Fin N => I p l).card = q+1)
    (columnDegree : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1)
    (S : Finset (Fin (N+N))) (covers : ∀ p l, I p l → L p ∈ S ∨ R l ∈ S) : N ≤ S.card := by
  classical
  let edges := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)
  let rows (p : Fin N) := (Finset.univ.filter fun l : Fin N => I p l).image fun l => (p,l)
  let columns (l : Fin N) := (Finset.univ.filter fun p : Fin N => I p l).image fun p => (p,l)
  let star (v : Fin (N+N)) : Finset (Fin N × Fin N) := Fin.addCases rows columns v
  have rowSize (p : Fin N) : (rows p).card = q+1 := by
    dsimp only [rows]
    rw [Finset.card_image_of_injective _ (fun _ _ eq => congrArg Prod.snd eq),rowDegree]
  have columnSize (l : Fin N) : (columns l).card = q+1 := by
    dsimp only [columns]
    rw [Finset.card_image_of_injective _ (fun _ _ eq => congrArg Prod.fst eq),
      ← Fintype.card_subtype (fun p => I p l),columnDegree]
  have starSize (v : Fin (N+N)) : (star v).card = q+1 := by
    refine Fin.addCases (fun p => ?_) (fun l => ?_) v
    · simpa [star] using rowSize p
    · simpa only [star,Fin.addCases_right] using columnSize l
  have distinct : (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint columns := by
    intro l _ k _ different
    refine Finset.disjoint_left.mpr ?_
    intro e inL inK
    obtain ⟨p,_,left⟩ := Finset.mem_image.mp inL
    obtain ⟨r,_,right⟩ := Finset.mem_image.mp inK
    exact different (congrArg Prod.snd (left.trans right.symm))
  have edgeSize : edges.card = N*(q+1) := by
    have same : edges = Finset.univ.biUnion columns := by
      ext e
      rcases e with ⟨p,l⟩
      simp [edges,columns,Prod.mk.injEq]
    rw [same,Finset.card_biUnion distinct]
    simp [columnSize]
  have capture : edges ⊆ S.biUnion star := by
    rintro ⟨p,l⟩ good
    have relation := (Finset.mem_filter.mp good).2
    rcases covers p l relation with atP | atL
    · apply Finset.mem_biUnion.mpr
      refine ⟨L p,atP,?_⟩
      have inRow : (p,l) ∈ rows p := Finset.mem_image.mpr ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,relation⟩,rfl⟩
      simpa [star,L] using inRow
    · apply Finset.mem_biUnion.mpr
      refine ⟨R l,atL,?_⟩
      have inCol : (p,l) ∈ columns l := Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,relation⟩,rfl⟩
      simpa only [star,R,Fin.addCases_right] using inCol
  have budget : edges.card ≤ S.card*(q+1) :=
    (Finset.card_le_card capture).trans (Finset.card_biUnion_le.trans (by simp [starSize]))
  rw [edgeSize] at budget
  exact Nat.le_of_mul_le_mul_right budget (by omega)
theorem pairTests (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (big : 101 ≤ q) (C : Circuit)
    (positive : ∀ p l : Fin N, I p l →
      circuitFun (N+N) C (fun i => decide (i = L p ∨ i = R l)) = true)
    (negative : ∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (R l) = true} ≤ q →
      (¬∃ p l, I p l ∧ x (L p) = true ∧ x (R l) = true) → circuitFun (N+N) C x = false) :
    ∀ u v : Fin (N+N), C.eval (List.ofFn fun i : Fin (N+N) => decide (i = u ∨ i = v)) = true ↔
      (incidenceGraph I).Adj u v := by
  intro u v
  let x : Fin (N+N) → Bool := fun i => decide (i=u ∨ i=v)
  change circuitFun (N+N) C x = true ↔ (incidenceGraph I).Adj u v
  constructor
  · intro recognized
    by_contra missing
    let toPair (a : {l : Fin N // x (R l) = true}) : {v' : Fin (N+N) // v' ∈ ({u,v} : Finset _)} := by
      refine ⟨R a.val,?_⟩
      have sits : R a.val = u ∨ R a.val = v := of_decide_eq_true a.property
      simpa only [Finset.mem_insert,Finset.mem_singleton] using sits
    have injective : Function.Injective toPair := by
      intro a b equal
      apply Subtype.ext
      have same := congrArg (fun z : {j : Fin (N+N) // j ∈ ({u,v} : Finset _)} => z.val) equal
      change R a.val = R b.val at same
      exact rightInjective same
    have small : Fintype.card {l : Fin N // x (R l) = true} ≤ q := by
      apply (Fintype.card_le_of_injective toPair injective).trans
      rw [Fintype.card_of_subtype ({u,v} : Finset (Fin (N+N))) (fun _ => Iff.rfl)]
      have bound := Finset.card_insert_le (a := u) (s := ({v} : Finset (Fin (N+N))))
      simp only [Finset.card_singleton] at bound
      omega
    have cannot : ¬∃ p l, I p l ∧ x (L p) = true ∧ x (R l) = true := by
      rintro ⟨p,l,inc,onP,onL⟩
      have hereP : L p = u ∨ L p = v := of_decide_eq_true onP
      have hereL : R l = u ∨ R l = v := of_decide_eq_true onL
      rcases hereP with left | right <;> rcases hereL with first | second
      · exact sides p l (left.trans first.symm)
      · apply missing
        exact (adjEither I u v).mpr (Or.inl ⟨p,l,left.symm,second.symm,inc⟩)
      · apply missing
        exact (adjEither I u v).mpr (Or.inr ⟨p,l,right.symm,first.symm,inc⟩)
      · exact sides p l (right.trans second.symm)
    rw [negative x small cannot] at recognized
    contradiction
  · intro inc
    rcases (adjEither I u v).mp inc with ⟨p,l,rfl,rfl,hit⟩ | ⟨p,l,rfl,rfl,hit⟩
    · exact positive p l hit
    · have eq : x = (fun i => decide (i=L p ∨ i=R l)) := by funext i; simp [x,or_comm]
      rw [eq]
      exact positive p l hit

noncomputable def eligibleVertices (n : ℕ) (C : Circuit) : Finset (Fin (n+n)) :=
  Finset.univ.filter fun v => Eligible C v

noncomputable def liveBranches (n : ℕ) (C : Circuit) : Finset ℕ :=
  (living (n+n) C).filter (Branch (n+n) C)

noncomputable def first (n : ℕ) (C : Circuit) (v : Fin (n+n)) : ℕ :=
  if h : Eligible C v then firstBranch C v h else 0

@[simp] theorem mem_eligible {n : ℕ} {C : Circuit} {v : Fin (n+n)} :
    v ∈ eligibleVertices n C ↔ Eligible C v := by simp [eligibleVertices]

theorem first_eq {n : ℕ} {C : Circuit} {v : Fin (n+n)} (h : Eligible C v) :
    first n C v = firstBranch C v h := by simp [first,h]

structure Context (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I] (C : Circuit) : Prop where
  rows : ∀ p, (Finset.univ.bipartiteAbove I p).card = q+1
  cols : ∀ l, (Finset.univ.bipartiteBelow I l).card = q+1
  pairEval : GraphEval C (incidenceGraph I)
  degree : ∀ v, 2 ≤ ((incidenceGraph I).neighborSet v).ncard
  noTwins : ∀ v w, v ≠ w → ∃ a, ¬ ((incidenceGraph I).Adj v a ↔ (incidenceGraph I).Adj w a)
  edgeWitness : ∀ v w, (incidenceGraph I).Adj v w → ∃ a b,
    (incidenceGraph I).Adj v a ∧ a ≠ w ∧ (incidenceGraph I).Adj w b ∧ b ≠ v ∧
    (a = b ∨ ¬ (incidenceGraph I).Adj a b)
  covers : ∀ p l, I p l → Eligible C (L p) ∨ Eligible C (R l)
  minimum : ∀ S : Finset (Fin (n+n)), (∀ p l, I p l → L p ∈ S ∨ R l ∈ S) → n ≤ S.card
  outputBound : C.output < (n+n)+C.size
  injective : Set.InjOn (first n C) (eligibleVertices n C)
  image : (eligibleVertices n C).image (first n C) = liveBranches n C
  side : ((∀ p : Fin n, Eligible C (L p)) ∧ (∀ l : Fin n, ¬ Eligible C (R l))) ∨
         ((∀ p : Fin n, ¬ Eligible C (L p)) ∧ (∀ l : Fin n, Eligible C (R l)))
  sizeEligible : (eligibleVertices n C).card = n
  sizeBranches : (liveBranches n C).card = n
  budgetEq : (n+n) + (liveBranches n C).card = C.size+1
  tight : PlaneTightFanout.Tight (n+n) C

-- The graph witnesses and the injection follow the constructions in linearLower and pairLower.
theorem of_equality (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I] (C : Circuit)
    (big : 101 ≤ q) (order : n = q^2+q+1)
    (degrees : ∀ l, Fintype.card {p : Fin n // I p l} = q+1)
    (unique : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (hm : Monotone2 C)
    (positive : ∀ p l, I p l → circuitFun (n+n) C (fun i => decide (i=L p ∨ i=R l)) = true)
    (negative : ∀ x, Fintype.card {l : Fin n // x (R l) = true} ≤ q →
      (¬ ∃ p l, I p l ∧ x (L p) = true ∧ x (R l) = true) → circuitFun (n+n) C x = false)
    (saturated : C.size+1 = 3*n) : Context q n I C := by
  classical
  let G := incidenceGraph I
  have neighbors := enoughNeighbors q n I big order degrees unique
  have nb (v : Fin (n+n)) : ∃ w, G.Adj v w := by
    obtain ⟨a,_,_,ha,_⟩ := neighbors v
    exact ⟨a,ha⟩
  have atLeastTwo (v : Fin (n+n)) : 2 ≤ (G.neighborSet v).ncard := by
    obtain ⟨a,b,diff,va,vb⟩ := neighbors v
    have finite : (G.neighborSet v).Finite := Set.toFinite _
    rw [Set.ncard_eq_toFinset_card _ finite]
    exact Finset.one_lt_card_iff.mpr ⟨a,b,finite.mem_toFinset.mpr va,finite.mem_toFinset.mpr vb,diff⟩
  have noTwins (v w : Fin (n+n)) (different : v ≠ w) : ∃ a, ¬ (G.Adj v a ↔ G.Adj w a) := by
    by_contra! same
    obtain ⟨a,b,distinct,va,vb⟩ := neighbors v
    exact noFour I unique v w a b different distinct va vb ((same a).mp va) ((same b).mp vb)
  have other (v w : Fin (n+n)) : ∃ a, G.Adj v a ∧ a ≠ w := by
    obtain ⟨a,b,different,va,vb⟩ := neighbors v
    by_cases firstA : a = w
    · exact ⟨b,vb,fun second => different (firstA.trans second.symm)⟩
    · exact ⟨a,va,firstA⟩
  have adjacent (v w : Fin (n+n)) (edge : G.Adj v w) :
      ∃ a b, G.Adj v a ∧ a ≠ w ∧ G.Adj w b ∧ b ≠ v ∧ (a=b ∨ ¬G.Adj a b) := by
    obtain ⟨a,va,notW⟩ := other v w
    obtain ⟨b,wb,notV⟩ := other w v
    refine ⟨a,b,va,notW,wb,notV,Or.inr ?_⟩
    intro ab
    exact noFour I unique w a v b notW.symm notV.symm (G.adj_symm edge) wb (G.adj_symm va) ab
  have he : GraphEval C G := pairTests q n I big C positive negative
  have covers (p l : Fin n) (inc : I p l) : Eligible C (L p) ∨ Eligible C (R l) := by
    have edge := (leftRight I p l).mpr inc
    obtain ⟨a,b,h1,h2,h3,h4,h5⟩ := adjacent _ _ edge
    exact covers_edge hm he edge h1 h2 h3 h4 h5
  have rows := pointDegree q n I (by omega) order degrees unique
  have cols (l : Fin n) : (Finset.univ.bipartiteBelow I l).card = q+1 :=
    (Fintype.card_subtype (fun p => I p l)).symm.trans (degrees l)
  have coverMin := coverBudget q n I rows degrees
  have setCover (p l : Fin n) (inc : I p l) : L p ∈ eligibleVertices n C ∨ R l ∈ eligibleVertices n C :=
    (covers p l inc).imp mem_eligible.mpr mem_eligible.mpr
  have floor := coverMin (eligibleVertices n C) setCover
  let v0 : Fin (n+n) := ⟨0,by omega⟩
  obtain ⟨w0,hw0⟩ := nb v0
  have oBound := (edge_at_output he hw0).2
  have oLive : C.output ∈ living (n+n) C := mem_living.mpr ⟨oBound,.refl⟩
  have into (v : Fin (n+n)) (hv : v ∈ eligibleVertices n C) : first n C v ∈ liveBranches n C := by
    have ev := mem_eligible.mp hv
    rw [first_eq ev]
    have spec := firstBranch_spec v ev
    exact Finset.mem_filter.mpr ⟨mem_living.mpr ⟨(next_le spec.1).trans_lt oBound,spec.1⟩,spec.2.2⟩
  have inj : Set.InjOn (first n C) (eligibleVertices n C) := by
    intro v hv w hw eq
    have vE := mem_eligible.mp hv
    have wE := mem_eligible.mp hw
    rw [first_eq vE, first_eq wE] at eq
    exact branch_injective hm he (fun a b d _ _ _ => noTwins a b d) vE wE (atLeastTwo v) (atLeastTwo w) eq
  have budget : (n+n)+(liveBranches n C).card ≤ C.size+1 := branch_budget hm he nb oLive
  obtain ⟨image,side⟩ := planeBranchBudgetEquality I rows cols (fun p r ne => (unique p r ne).exists)
    (eligibleVertices n C) (liveBranches n C) (first n C) setCover floor into inj budget saturated
  have count : (eligibleVertices n C).card = (liveBranches n C).card := by
    rw [← image,Finset.card_image_of_injOn inj]
  have eqBudget : (n+n)+(liveBranches n C).card = C.size+1 := by omega
  exact ⟨rows,cols,he,atLeastTwo,noTwins,adjacent,covers,coverMin,oBound,inj,image,by
    simpa only [mem_eligible] using side,by omega,by omega,eqBudget,
    PlaneTightFanout.tight_of_budget hm he nb oLive eqBudget⟩

noncomputable def label (n : ℕ) (C : Circuit) (j : ℕ) : Option (Fin (n+n)) :=
  if h : ∃ v : Fin (n+n), ∃ hv : Eligible C v, j = firstBranch C v hv then some h.choose else none

theorem label_valid {n : ℕ} {C : Circuit} {j : ℕ} {v : Fin (n+n)}
    (hv : label n C j = some v) : ∃ ev : Eligible C v, j = firstBranch C v ev := by
  unfold label at hv
  split at hv
  next h =>
    cases Option.some.inj hv
    exact h.choose_spec
  next => contradiction

theorem Context.label_first {q n : ℕ} {I : Fin n → Fin n → Prop} [DecidableRel I] {C : Circuit}
    (h : Context q n I C) {v : Fin (n+n)} (ev : Eligible C v) :
    label n C (firstBranch C v ev) = some v := by
  have existsV : ∃ w : Fin (n+n), ∃ ew : Eligible C w, firstBranch C v ev = firstBranch C w ew :=
    ⟨v, ev, rfl⟩
  obtain ⟨ew,eq⟩ := existsV.choose_spec
  have same : existsV.choose = v := h.injective (mem_eligible.mpr ew) (mem_eligible.mpr ev)
    (by rw [first_eq ew,first_eq ev]; exact eq.symm)
  rw [label, dite_eq_left existsV, same]

theorem Context.perCut {q n : ℕ} {I : Fin n → Fin n → Prop} [DecidableRel I] {C : Circuit}
    (h : Context q n I C) (w : PlaneTightFanout.Wire (n+n) C) :
    w ∈ PlaneTightFanout.branchCuts (n+n) C ↔ ∃ v, label n C w.val = some v := by
  constructor
  · intro hw
    have live : w.val ∈ living (n+n) C := h.tight.all_live.symm ▸ Finset.mem_range.mpr w.isLt
    have mem : w.val ∈ liveBranches n C := Finset.mem_filter.mpr ⟨live,PlaneTightFanout.mem_branchCuts.mp hw⟩
    rw [← h.image] at mem
    obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp mem
    have ev := mem_eligible.mp hv
    rw [first_eq ev] at eq
    refine ⟨v, ?_⟩
    rw [← eq]
    exact h.label_first ev
  · rintro ⟨v,hv⟩
    obtain ⟨ev,eq⟩ := label_valid hv
    apply PlaneTightFanout.mem_branchCuts.mpr
    rw [eq]
    exact (firstBranch_spec v ev).2.2

end PlaneEqualityContext
end

-- PlaneBranchWitness
section
namespace PlaneBranchWitness

open Plane2866Graph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem branch_of_lit {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {v : Fin n} (hv : Eligible C v) {x : Fin n → Bool} (lit : x v = true) :
    val C x (firstBranch C v hv) = true := by
  apply acts_mono hm _ _ ((carries_iff hm).mp (firstBranch_spec v hv).2.1).1
  intro i hi
  have e : i = v := by simpa [point] using hi
  simpa only [e] using lit

theorem branch_of_pivot {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {v : Fin n} (hv : Eligible C v) {x : Fin n → Bool}
    (reject : val C x C.output = false)
    (neighbor : ∃ u, x u = true ∧ val C (point {v,u}) C.output = true) :
    val C x (firstBranch C v hv) = false := by
  classical
  obtain ⟨u,lit,hit⟩ := neighbor
  let y (i : Fin n) := if i = v then true else x i
  have hitY : val C y C.output = true := by
    apply acts_mono hm _ _ hit
    intro i hi
    have h : i = v ∨ i = u := by simpa [point] using hi
    rcases h with rfl | rfl <;> simp [y,lit]
  have bY : val C y (firstBranch C v hv) = true := branch_of_lit hm hv (by simp [y])
  cases h : val C x (firstBranch C v hv) with
  | false => rfl
  | true =>
    have same := value_at_branch hv (x:=x) (y:=y) (fun i hi => by simp [y,hi])
      (h.trans bY.symm)
    rw [reject,hitY] at same
    contradiction

def canonical {n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I] (T : Finset (Fin n)) :
    Fin (n+n) → Bool := Fin.addCases
      (fun p => decide (¬∃ l ∈ T, I p l)) (fun l => decide (l ∈ T))

theorem firstBranch_on_canonical {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    (I : Fin n → Fin n → Prop) [DecidableRel I] (T : Finset (Fin n))
    (fresh : ∀ l ∉ T, ∃ p, I p l ∧ ∀ k ∈ T, ¬ I p k)
    (positive : ∀ p l, I p l → val C (point {Fin.castAdd n p, Fin.natAdd n l}) C.output = true)
    (reject : val C (canonical I T) C.output = false)
    (v : Fin (n+n)) (hv : Eligible C v) :
    val C (canonical I T) (firstBranch C v hv) = canonical I T v := by
  classical
  have leftValue (p : Fin n) : canonical I T (Fin.castAdd n p) = decide (¬∃ l ∈ T, I p l) :=
    Fin.addCases_left _
  have rightValue (l : Fin n) : canonical I T (Fin.natAdd n l) = decide (l ∈ T) :=
    Fin.addCases_right _
  cases on : canonical I T v with
  | true => exact branch_of_lit hm hv on
  | false =>
    apply branch_of_pivot hm hv reject
    induction v using Fin.addCases with
    | left p =>
      have inside : ∃ l ∈ T, I p l := by
        simpa only [leftValue, decide_eq_false_iff_not, not_not] using on
      obtain ⟨l,hl,hpl⟩ := inside
      exact ⟨Fin.natAdd n l, (rightValue l).trans (decide_eq_true hl), positive p l hpl⟩
    | right l =>
      have outside : l ∉ T := by simpa only [rightValue, decide_eq_false_iff_not] using on
      obtain ⟨p,hpl,hp⟩ := fresh l outside
      have unhit : ¬∃ k ∈ T, I p k := by
        rintro ⟨k,hk,inc⟩
        exact hp k hk inc
      refine ⟨Fin.castAdd n p, (leftValue p).trans (decide_eq_true unhit), ?_⟩
      simpa only [Finset.pair_comm (Fin.natAdd n l) (Fin.castAdd n p)] using positive p l hpl

theorem empty_line_test {n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I] :
    (∀ p, canonical I ∅ (Fin.castAdd n p) = true) ∧
      (∀ l, canonical I ∅ (Fin.natAdd n l) = false) := by
  constructor
  · intro p
    rw [show canonical I ∅ (Fin.castAdd n p) = decide (¬∃ l ∈ (∅ : Finset (Fin n)), I p l) from
      Fin.addCases_left _]
    simp
  · intro l
    rw [show canonical I ∅ (Fin.natAdd n l) = decide (l ∈ (∅ : Finset (Fin n))) from
      Fin.addCases_right _]
    simp

theorem singleton_line_test {n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I] (l : Fin n) :
    (∀ p, canonical I {l} (Fin.castAdd n p) = decide (¬ I p l)) ∧
      (∀ k, canonical I {l} (Fin.natAdd n k) = decide (k = l)) := by
  constructor
  · intro p
    rw [show canonical I {l} (Fin.castAdd n p) = decide (¬∃ k ∈ ({l} : Finset (Fin n)), I p k) from
      Fin.addCases_left _]
    simp
  · intro k
    rw [show canonical I {l} (Fin.natAdd n k) = decide (k ∈ ({l} : Finset (Fin n))) from
      Fin.addCases_right _]
    simp

theorem distinct_coordinate_signatures {n : ℕ}
    (I : Fin n → Fin n → Prop) [DecidableRel I]
    (distinguish : ∀ p r, p ≠ r → ∃ l, I p l ∧ ¬ I r l) :
    Function.Injective (fun v : Fin (n+n) =>
      (canonical I ∅ v, fun l : Fin n => canonical I {l} v)) := by
  intro v w h
  have h₀ : canonical I ∅ v = canonical I ∅ w := congrArg Prod.fst h
  have h₁ (l : Fin n) : canonical I {l} v = canonical I {l} w :=
    congrFun (congrArg Prod.snd h) l
  clear h
  induction v using Fin.addCases with
  | left p =>
    induction w using Fin.addCases with
    | left r =>
      apply congrArg (Fin.castAdd n)
      by_contra ne
      obtain ⟨l,on,off⟩ := distinguish p r ne
      have impossible := h₁ l
      rw [(singleton_line_test I l).1 p,(singleton_line_test I l).1 r] at impossible
      simp [on, off] at impossible
    | right r =>
      rw [(empty_line_test I).1 p,(empty_line_test I).2 r] at h₀
      contradiction
  | right l =>
    induction w using Fin.addCases with
    | left p =>
      rw [(empty_line_test I).2 l,(empty_line_test I).1 p] at h₀
      contradiction
    | right k =>
      apply congrArg (Fin.natAdd n)
      have eqn := h₁ k
      rw [(singleton_line_test I k).2 l,(singleton_line_test I k).2 k] at eqn
      simpa using eqn

theorem unique_carrier_predecessor {n : ℕ} {C : Circuit}
    {v : Fin n} (hv : Eligible C v) {a i j : ℕ} (bound : a ≤ firstBranch C v hv)
    (hi : Carries C v i) (hj : Carries C v j)
    (ei : LNext n C i a) (ej : LNext n C j a) : i = j := by
  wlog order : i ≤ j generalizing i j
  · exact (this hj hi ej ei (by omega)).symm
  have pi := singleton_path (live_before ei.1 ei.2) hi
  have pj := singleton_path (live_before ej.1 ej.2) hj
  have unique (u k t : ℕ) (hu : u < i) (hc : Carries C v u)
      (hk : LNext n C u k) (ht : LNext n C u t) : k = t :=
    firstBranch_unique v hv u k t (by have := ei.1.1; omega) hc hk ht
  rcases align pi unique j pj with h | path
  · omega
  · rcases path.cases_head with equal | ⟨k, head, tail⟩
    · omega
    · have hka := firstBranch_unique v hv i k a (lt_of_lt_of_le ei.1.1 bound) hi head.2 ei
      have := trace_le tail
      have := ej.1.1
      omega

theorem or_on_firstBranch_path {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {v : Fin n} (hv : Eligible C v) {p : ℕ} {g : Gate} {i j : ℕ}
    (hg : C.gates[p]? = some g) (inputs : g.inputs = [i,j])
    (hi : i < n+p) (hj : j < n+p) (distinct : i ≠ j)
    (live : Live n C (n+p)) (before : n+p ≤ firstBranch C v hv)
    (carries : Carries C v (n+p))
    (zero : ∀ k, val C (point (∅ : Finset (Fin n))) k = false) :
    g.op = GateOp.or := by
  have ops := (hm g (List.mem_of_getElem? hg)).1
  rcases ops with op | op
  · have both := ((carries_iff hm).mp carries).1
    rw [val_gate C _ hg, inputs] at both
    simp [op, GateOp.eval, operand, hi, hj] at both
    have ci := (carries_iff hm).mpr ⟨both.1, zero i⟩
    have cj := (carries_iff hm).mpr ⟨both.2, zero j⟩
    exact (distinct (unique_carrier_predecessor hv before ci cj
      ⟨⟨hi,p,g,hg,rfl,by simp [inputs]⟩,live⟩
      ⟨⟨hj,p,g,hg,rfl,by simp [inputs]⟩,live⟩)).elim
  · exact op

def localValue {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (i : ℕ) (prev : ∀ j, j < i → Bool) : Bool :=
  if h : i < n then x ⟨i,h⟩ else
    match C.gates[i-n]? with
    | none => false
    | some g => g.op.eval (g.inputs.map fun j => if h : j < i then prev j h else false)

def cutValue {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (label : ℕ → Option (Fin n)) (i : ℕ) : Bool :=
  match label i with
  | some v => x v
  | none => localValue C x i fun j _ => cutValue C x label j
termination_by i

def cutBody {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (label : ℕ → Option (Fin n)) (i : ℕ) : Bool :=
  localValue C x i fun j _ => cutValue C x label j

theorem genuine_local_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) :
    localValue C x i (fun j _ => val C x j) = val C x i := by
  by_cases hin : i < n
  · simpa [localValue,hin] using (val_input C x ⟨i,hin⟩).symm
  by_cases ho : n+C.gates.length ≤ i
  · have missing : C.gates[i-n]? = none := List.getElem?_eq_none (by omega)
    simp [localValue,hin,missing,val_beyond C x ho]
  have h : i-n < C.gates.length := by omega
  let g := C.gates[i-n]
  have hg : C.gates[i-n]? = some g := List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩
  have hi : n+(i-n) = i := by omega
  have orig := (val_gate C x hg).symm
  rw [hi] at orig
  simp only [localValue,dite_eq_right hin,hg]
  exact orig

theorem cutBody_agrees {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (label : ℕ → Option (Fin n)) (i : ℕ)
    (agrees : ∀ j < i, ∀ v, label j = some v → val C x j = x v) :
    cutBody C x label i = val C x i := by
  suffices earlier : ∀ j < i, cutValue C x label j = val C x j by
    unfold cutBody
    calc
      _ = localValue C x i (fun j _ => val C x j) := by
        congr 1
        funext j h
        exact earlier j h
      _ = _ := genuine_local_value C x i
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    rw [cutValue]
    cases lab : label j with
    | some v => exact (agrees j hj v lab).symm
    | none =>
      change localValue C x j (fun k _ => cutValue C x label k) = _
      calc
        _ = localValue C x j (fun k _ => val C x k) := by
          congr 1
          funext k hk
          exact ih k hk (hk.trans hj)
        _ = _ := genuine_local_value C x j

theorem localValue_mono {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {x y : Fin n → Bool} (xy : ∀ v, x v = true → y v = true) (i : ℕ)
    (s t : ∀ j, j < i → Bool) (st : ∀ j h, s j h = true → t j h = true) :
    localValue C x i s = true → localValue C y i t = true := by
  by_cases h : i < n
  · simpa [localValue,h] using xy ⟨i,h⟩
  simp only [localValue,dite_eq_right h]
  cases hg : C.gates[i-n]? with
  | none => simp
  | some g =>
    have imp (a : ℕ) :
        (if ha : a < i then s a ha else false) = true →
          (if ha : a < i then t a ha else false) = true := by
      by_cases ha : a < i
      · simpa [ha] using st a ha
      · simp [ha]
    have ops := (hm g (List.mem_of_getElem? hg)).1
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops
    rcases ops with hor | hor
    · simp only [hor, GateOp.eval, List.all_map, Function.comp_apply, id, List.all_eq_true]
      exact fun all a ha => imp a (all a ha)
    · simp only [hor, GateOp.eval, List.any_map, Function.comp_apply, id, List.any_eq_true]
      rintro ⟨a,ha,on⟩
      exact ⟨a,ha,imp a on⟩

theorem cutValue_mono {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {x y : Fin n → Bool} (xy : ∀ v, x v = true → y v = true)
    (label : ℕ → Option (Fin n)) (i : ℕ) :
    cutValue C x label i = true → cutValue C y label i = true := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    rw [cutValue.eq_def C x label i,cutValue.eq_def C y label i]
    cases label i with
    | some v => exact xy v
    | none => exact localValue_mono hm xy i _ _ ih

theorem cutBody_mono {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {x y : Fin n → Bool} (xy : ∀ v, x v = true → y v = true)
    (label : ℕ → Option (Fin n)) (i : ℕ) :
    cutBody C x label i = true → cutBody C y label i = true :=
  localValue_mono hm xy i _ _ fun j _ => cutValue_mono hm xy label j

def LabelsFirst {n : ℕ} (C : Circuit) (label : ℕ → Option (Fin n)) : Prop :=
  ∀ j v, label j = some v → ∃ hv : Eligible C v, j = firstBranch C v hv

theorem cutBody_own_singleton {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {label : ℕ → Option (Fin n)} (valid : LabelsFirst C label)
    (zero : ∀ k, val C (point (∅ : Finset (Fin n))) k = false)
    {v : Fin n} (hv : Eligible C v) :
    cutBody C (point {v}) label (firstBranch C v hv) = true := by
  classical
  rw [cutBody_agrees]
  · exact ((carries_iff hm).mp (firstBranch_spec v hv).2.1).1
  · intro j hj u lab
    obtain ⟨hu, rfl⟩ := valid j u lab
    have uv : u ≠ v := by
      rintro rfl
      exact (Nat.lt_irrefl _) hj
    have no : val C (point {v}) (firstBranch C u hu) = false := by
      by_contra h
      have carry := (carries_iff hm).mpr ⟨Bool.eq_true_of_not_eq_false h, zero _⟩
      have spec := firstBranch_spec u hu
      have early : firstBranch C v hv ≤ firstBranch C u hu :=
        Nat.find_min' hv ⟨spec.1,carry,spec.2.2⟩
      omega
    simpa [point,uv] using no

def eraseBit {n : ℕ} (x : Fin n → Bool) (v : Fin n) (u : Fin n) : Bool :=
  if u = v then false else x u

theorem cutBody_split {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {label : ℕ → Option (Fin n)} (valid : LabelsFirst C label)
    (zero : ∀ k, val C (point (∅ : Finset (Fin n))) k = false)
    {v : Fin n} (hv : Eligible C v) (x : Fin n → Bool) :
    cutBody C x label (firstBranch C v hv) =
      (x v || cutBody C (eraseBit x v) label (firstBranch C v hv)) := by
  cases bit : x v with
  | false =>
    have e : eraseBit x v = x := by
      funext u
      by_cases eq : u = v <;> simp [eraseBit,eq,bit]
    simp [e]
  | true =>
    simp only [Bool.true_or]
    apply cutBody_mono hm _ label _ (cutBody_own_singleton hm valid zero hv)
    intro u hu
    have e : u = v := by simpa [point] using hu
    simpa only [e] using bit

theorem cutBody_le_actual {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {label : ℕ → Option (Fin n)} (valid : LabelsFirst C label)
    (x : Fin n → Bool) (i : ℕ) :
    cutBody C x label i = true → val C x i = true := by
  have aux (j : ℕ) : cutValue C x label j = true → val C x j = true := by
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      rw [cutValue]
      cases lab : label j with
      | some v =>
        obtain ⟨hv,e⟩ := valid j v lab
        rw [e]
        exact branch_of_lit hm hv
      | none =>
        rw [← genuine_local_value C x j]
        exact localValue_mono hm (fun _ h => h) j _ _ ih
  rw [← genuine_local_value C x i]
  exact localValue_mono hm (fun _ h => h) i _ _ fun j _ => aux j

theorem cut_positive {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {label : ℕ → Option (Fin n)} (valid : LabelsFirst C label)
    {x : Fin n → Bool} (hit : val C x C.output = true) :
    cutBody C x label C.output = true ∨
      ∃ j v, label j = some v ∧ cutBody C (eraseBit x v) label j = true := by
  classical
  let differs (j : ℕ) := ∃ v, label j = some v ∧ val C x j ≠ x v
  by_cases diff : ∃ j, differs j
  · right
    let j := Nat.find diff
    obtain ⟨v,lab,bad⟩ := Nat.find_spec diff
    change val C x j ≠ x v at bad
    change label j = some v at lab
    obtain ⟨hv,ej⟩ := valid j v lab
    have bound : x v = true → val C x j = true := ej ▸ branch_of_lit hm hv
    have off : x v = false := by cases h : x v <;> simp_all
    have on : val C x j = true := by cases h : val C x j <;> simp_all
    have erase : eraseBit x v = x := by
      funext u
      by_cases eq : u = v <;> simp [eraseBit,eq,off]
    refine ⟨j,v,lab,?_⟩
    rw [erase,cutBody_agrees, on]
    intro k hk w labk
    by_contra inequal
    exact (Nat.find_min diff hk) ⟨w,labk,inequal⟩
  · left
    rw [cutBody_agrees,hit]
    intro k _ v lab
    by_contra bad
    exact diff ⟨k,v,lab,bad⟩

theorem escaping_line {n q : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (degree : ∀ p, Fintype.card {l // I p l} = q+1)
    (join : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (X : Finset (Fin n)) (size : X.card ≤ q) (v : Fin n) (off : v ∉ X) :
    ∃ l, I v l ∧ ∀ p ∈ X, ¬ I p l := by
  classical
  by_contra missing
  have hit (l : {l // I v l}) : ∃ p : X, I p.val l.val := by
    by_contra h
    exact missing ⟨l.val,l.property,fun p hp inc => h ⟨⟨p,hp⟩,inc⟩⟩
  let f (l : {l // I v l}) : X := Classical.choose (hit l)
  have incident (l : {l // I v l}) : I (f l).val l.val := Classical.choose_spec (hit l)
  have inject : Function.Injective f := by
    intro l k same
    apply Subtype.ext
    have ne : v ≠ (f l).val := fun e => off (e ▸ (f l).property)
    have right : I (f l).val k.val := same ▸ incident k
    exact (join _ _ ne).unique ⟨l.property,incident l⟩ ⟨k.property,right⟩
  have count := Fintype.card_le_of_injective f inject
  rw [degree,Fintype.card_coe] at count
  omega

def probe {n : ℕ} (X Y : Finset (Fin n)) : Fin (n+n) → Bool :=
  Fin.addCases (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))

theorem extend_negative {n q : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (degree : ∀ p, Fintype.card {l // I p l} = q+1)
    (join : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (X Y : Finset (Fin n)) (sX : X.card ≤ q) (sY : Y.card < q)
    (apart : ∀ p ∈ X, ∀ l ∈ Y, ¬ I p l)
    (v : Fin (n+n)) (off : probe X Y v = false) :
    ∃ T : Finset (Fin n), T.card ≤ q ∧ canonical I T v = false ∧
      ∀ u, probe X Y u = true → canonical I T u = true := by
  classical
  have extension (T : Finset (Fin n)) (contains : Y ⊆ T)
      (avoids : ∀ p ∈ X, ∀ l ∈ T, ¬ I p l) (u : Fin (n+n)) :
      probe X Y u = true → canonical I T u = true := by
    induction u using Fin.addCases with
    | left p =>
      simp only [probe,canonical,Fin.addCases_left,decide_eq_true_eq]
      rintro hp ⟨l,hl,inc⟩
      exact avoids p hp l hl inc
    | right l =>
      simpa only [probe,canonical,Fin.addCases_right,decide_eq_true_eq] using
        (show l ∈ Y → l ∈ T from fun h => contains h)
  induction v using Fin.addCases with
  | left v =>
    have outside : v ∉ X := by simpa [probe] using off
    obtain ⟨k,hk,avoidsK⟩ := escaping_line I degree join X sX v outside
    refine ⟨insert k Y, (Finset.card_insert_le k Y).trans (by omega),?_,?_⟩
    · simp only [canonical,Fin.addCases_left,decide_eq_false_iff_not,not_not]
      exact ⟨k,Finset.mem_insert_self _ _,hk⟩
    · apply extension _ (Finset.subset_insert _ _)
      intro p hp l hl
      rcases Finset.mem_insert.mp hl with rfl | hy
      · exact avoidsK p hp
      · exact apart p hp l hy
  | right l =>
    have a : probe X Y (Fin.natAdd n l) = decide (l ∈ Y) := Fin.addCases_right _
    have b : canonical I Y (Fin.natAdd n l) = decide (l ∈ Y) := Fin.addCases_right _
    exact ⟨Y,sY.le,b.trans (a.symm.trans off),extension Y (fun _ h => h) apart⟩

theorem cut_residual_rejects {n q : ℕ} {C : Circuit} (hm : Monotone2 C)
    {label : ℕ → Option (Fin (n+n))} (valid : LabelsFirst C label)
    (I : Fin n → Fin n → Prop) [DecidableRel I]
    (degree : ∀ p, Fintype.card {l // I p l} = q+1)
    (join : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (fresh : ∀ T : Finset (Fin n), T.card ≤ q → ∀ l ∉ T, ∃ p, I p l ∧ ∀ k ∈ T, ¬ I p k)
    (positive : ∀ p l, I p l → val C (point {Fin.castAdd n p, Fin.natAdd n l}) C.output = true)
    (reject : ∀ T : Finset (Fin n), T.card ≤ q → val C (canonical I T) C.output = false)
    (X Y : Finset (Fin n)) (sX : X.card ≤ q) (sY : Y.card < q)
    (apart : ∀ p ∈ X, ∀ l ∈ Y, ¬ I p l) (v : Fin (n+n)) (hv : Eligible C v) :
    cutBody C (eraseBit (probe X Y) v) label (firstBranch C v hv) = false := by
  classical
  let X' := X.filter fun p => Fin.castAdd n p ≠ v
  let Y' := Y.filter fun l => Fin.natAdd n l ≠ v
  have subX : X' ⊆ X := Finset.filter_subset _ _
  have subY : Y' ⊆ Y := Finset.filter_subset _ _
  have e : eraseBit (probe X Y) v = probe X' Y' := by
    funext u
    induction u using Fin.addCases with
    | left p =>
      simp only [eraseBit,probe,Fin.addCases_left,X',Finset.mem_filter]
      by_cases h : Fin.castAdd n p = v <;> simp [h]
    | right l =>
      simp only [eraseBit,probe,Fin.addCases_right,Y',Finset.mem_filter]
      simp [Bool.and_comm]
  have off : probe X' Y' v = false := by rw [← e]; simp [eraseBit]
  obtain ⟨T,small,absent,dominates⟩ := extend_negative I degree join X' Y'
    ((Finset.card_le_card subX).trans sX) (lt_of_le_of_lt (Finset.card_le_card subY) sY)
    (fun p hp l hl => apart p (subX hp) l (subY hl)) v off
  rw [e]
  cases h : cutBody C (probe X' Y') label (firstBranch C v hv) with
  | false => rfl
  | true =>
    have actual := cutBody_le_actual hm valid _ _
      (cutBody_mono hm dominates label (firstBranch C v hv) h)
    rw [firstBranch_on_canonical hm I T (fresh T small) positive (reject T small) v hv,absent] at actual
    contradiction

def readFormula {n i : ℕ} (prev : ∀ j, j < i → PlaneFormula (Fin n)) (j : ℕ) :
    PlaneFormula (Fin n) := if h : j < i then prev j h else .bot

def localFormula (n : ℕ) (C : Circuit) (i : ℕ) (prev : ∀ j, j < i → PlaneFormula (Fin n)) :
    PlaneFormula (Fin n) :=
  if h : i < n then .leaf ⟨i,h⟩ else
    match C.gates[i-n]? with
    | some g =>
      match g.inputs with
      | [a,b] =>
        match g.op with
        | GateOp.and => .and (readFormula prev a) (readFormula prev b)
        | _ => .or (readFormula prev a) (readFormula prev b)
      | _ => .bot
    | none => .bot

def cutFormula {n : ℕ} (C : Circuit) (label : ℕ → Option (Fin n)) (i : ℕ) : PlaneFormula (Fin n) :=
  match label i with
  | some v => .leaf v
  | none => localFormula n C i fun j _ => cutFormula C label j
termination_by i

def bodyFormula {n : ℕ} (C : Circuit) (label : ℕ → Option (Fin n)) (i : ℕ) : PlaneFormula (Fin n) :=
  localFormula n C i fun j _ => cutFormula C label j

def BinaryInputs (C : Circuit) : Prop :=
  ∀ (p : ℕ) (g : Gate), C.gates[p]? = some g → ∃ i j, g.inputs = [i,j]

theorem eval_localFormula {n : ℕ} {C : Circuit} (hm : Monotone2 C) (bin : BinaryInputs C)
    (x : Fin n → Bool) (i : ℕ) (prev : ∀ j, j < i → PlaneFormula (Fin n)) :
    PlaneFormula.eval x (localFormula n C i prev) =
      localValue C x i (fun j h => PlaneFormula.eval x (prev j h)) := by
  have read (j : ℕ) : PlaneFormula.eval x (readFormula prev j) =
      if h : j < i then PlaneFormula.eval x (prev j h) else false := by
    by_cases h : j < i <;> simp [readFormula,h,PlaneFormula.eval]
  by_cases hi : i < n
  · simp [localFormula,localValue,hi,PlaneFormula.eval]
  simp only [localFormula,localValue,dite_eq_right hi]
  cases hg : C.gates[i-n]? with
  | none => rfl
  | some g =>
    obtain ⟨a,b,inputs⟩ := bin _ _ hg
    have op := (hm g (List.mem_of_getElem? hg)).1
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op
    rcases op with andOp | orOp
    · simp [inputs,andOp,PlaneFormula.eval,read,GateOp.eval]
    · simp [inputs,orOp,PlaneFormula.eval,read,GateOp.eval]

theorem eval_cutFormula {n : ℕ} {C : Circuit} (hm : Monotone2 C) (bin : BinaryInputs C)
    (x : Fin n → Bool) (label : ℕ → Option (Fin n)) (i : ℕ) :
    PlaneFormula.eval x (cutFormula C label i) = cutValue C x label i := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    rw [cutFormula.eq_def C label i,cutValue.eq_def C x label i]
    cases label i with
    | some v => rfl
    | none =>
      change PlaneFormula.eval x (localFormula n C i _) = localValue C x i _
      rw [eval_localFormula hm bin]
      congr 1
      funext j h
      exact ih j h

theorem eval_bodyFormula {n : ℕ} {C : Circuit} (hm : Monotone2 C) (bin : BinaryInputs C)
    (x : Fin n → Bool) (label : ℕ → Option (Fin n)) (i : ℕ) :
    PlaneFormula.eval x (bodyFormula C label i) = cutBody C x label i := by
  rw [bodyFormula,cutBody,eval_localFormula hm bin]
  congr 1
  funext j _
  exact eval_cutFormula hm bin x label j

def eraseLeaf {n : ℕ} (v : Fin n) : PlaneFormula (Fin n) → PlaneFormula (Fin n)
  | .leaf u => if u = v then .bot else .leaf u
  | .bot => .bot
  | .or a b => .or (eraseLeaf v a) (eraseLeaf v b)
  | .and a b => .and (eraseLeaf v a) (eraseLeaf v b)

theorem eval_eraseLeaf {n : ℕ} (x : Fin n → Bool) (v : Fin n) (F : PlaneFormula (Fin n)) :
    PlaneFormula.eval x (eraseLeaf v F) = PlaneFormula.eval (eraseBit x v) F := by
  induction F with
  | leaf u => by_cases e : u = v <;> simp [eraseLeaf,PlaneFormula.eval,eraseBit,e]
  | bot => rfl
  | or a b ha hb | and a b ha hb => simp [eraseLeaf,PlaneFormula.eval,ha,hb]

theorem leaves_eraseLeaf {n : ℕ} (v : Fin n) (F : PlaneFormula (Fin n)) :
    (eraseLeaf v F).leaves = F.leaves.filter (· != v) := by
  induction F with
  | leaf u => by_cases e : u = v <;> simp [eraseLeaf,PlaneFormula.leaves,e]
  | bot => rfl
  | or a b ha hb | and a b ha hb => simp [eraseLeaf,PlaneFormula.leaves,ha,hb]

def residualFormula {n : ℕ} (C : Circuit) (label : ℕ → Option (Fin n)) (j : ℕ) :
    PlaneFormula (Fin n) :=
  match label j with
  | some v => eraseLeaf v (bodyFormula C label j)
  | none => .bot

noncomputable def cutForest {W : Type} {n : ℕ} (C : Circuit) (label : ℕ → Option (Fin n))
    (wire : W → ℕ) (cuts : Finset W) : PlaneFormula (Fin n) :=
  cuts.toList.foldr (fun w rest => .or (residualFormula C label (wire w)) rest)
    (bodyFormula C label C.output)

theorem eval_cutForest {W : Type} {n : ℕ} (C : Circuit) (label : ℕ → Option (Fin n))
    (wire : W → ℕ) (cuts : Finset W) (x : Fin n → Bool) :
    PlaneFormula.eval x (cutForest C label wire cuts) = true ↔
      PlaneFormula.eval x (bodyFormula C label C.output) = true ∨
      ∃ w ∈ cuts, PlaneFormula.eval x (residualFormula C label (wire w)) = true := by
  have aux (ws : List W) :
      PlaneFormula.eval x (ws.foldr (fun w rest => PlaneFormula.or
        (residualFormula C label (wire w)) rest) (bodyFormula C label C.output)) = true ↔
      PlaneFormula.eval x (bodyFormula C label C.output) = true ∨
        ∃ w ∈ ws, PlaneFormula.eval x (residualFormula C label (wire w)) = true := by
    induction ws with
    | nil => simp
    | cons w ws ih => simp [PlaneFormula.eval,ih]; tauto
  simpa [cutForest] using aux cuts.toList

theorem count_cutForest {W : Type} {n : ℕ} (C : Circuit) (label : ℕ → Option (Fin n))
    (wire : W → ℕ) (cuts : Finset W) (v : Fin n) :
    (cutForest C label wire cuts).leaves.count v = (bodyFormula C label C.output).leaves.count v +
      ∑ w ∈ cuts, (residualFormula C label (wire w)).leaves.count v := by
  have aux (ws : List W) :
      (ws.foldr (fun w rest => PlaneFormula.or
        (residualFormula C label (wire w)) rest) (bodyFormula C label C.output)).leaves.count v =
        (bodyFormula C label C.output).leaves.count v +
          (ws.map (fun w => (residualFormula C label (wire w)).leaves.count v)).sum := by
    induction ws with
    | nil => simp
    | cons w ws ih => simp [PlaneFormula.leaves,ih]; omega
  simpa [cutForest] using aux cuts.toList

theorem forest_positive {W : Type} {n : ℕ} {C : Circuit} (hm : Monotone2 C) (bin : BinaryInputs C)
    {label : ℕ → Option (Fin n)} (valid : LabelsFirst C label) (wire : W → ℕ) (cuts : Finset W)
    (cover : ∀ j v, label j = some v → ∃ w ∈ cuts, wire w = j)
    {x : Fin n → Bool} (hit : val C x C.output = true) :
    PlaneFormula.eval x (cutForest C label wire cuts) = true := by
  apply (eval_cutForest C label wire cuts x).mpr
  rcases cut_positive hm valid hit with root | ⟨j,v,lab,jhit⟩
  · left
    rwa [eval_bodyFormula hm bin]
  · right
    obtain ⟨w,hw,rfl⟩ := cover j v lab
    exact ⟨w,hw,by simpa [residualFormula,lab,eval_eraseLeaf,eval_bodyFormula hm bin] using jhit⟩

theorem forest_rejects {W : Type} {n q : ℕ} {C : Circuit} (hm : Monotone2 C) (bin : BinaryInputs C)
    {label : ℕ → Option (Fin (n+n))} (valid : LabelsFirst C label) (wire : W → ℕ) (cuts : Finset W)
    (I : Fin n → Fin n → Prop) [DecidableRel I]
    (degree : ∀ p, Fintype.card {l // I p l} = q+1)
    (join : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (fresh : ∀ T : Finset (Fin n), T.card ≤ q → ∀ l ∉ T, ∃ p, I p l ∧ ∀ k ∈ T, ¬ I p k)
    (positive : ∀ p l, I p l → val C (point {Fin.castAdd n p, Fin.natAdd n l}) C.output = true)
    (reject : ∀ T : Finset (Fin n), T.card ≤ q → val C (canonical I T) C.output = false)
    (X Y : Finset (Fin n)) (sX : X.card ≤ q) (sY : Y.card < q)
    (apart : ∀ p ∈ X, ∀ l ∈ Y, ¬ I p l) :
    PlaneFormula.eval (probe X Y) (cutForest C label wire cuts) = false := by
  apply Bool.eq_false_iff.mpr
  intro yes
  rcases (eval_cutForest C label wire cuts _).mp yes with on | ⟨w,_,on⟩
  · rw [eval_bodyFormula hm bin] at on
    have bound (u : Fin (n+n)) : probe X Y u = true → canonical I Y u = true := by
      induction u using Fin.addCases with
      | left p =>
        simp only [probe,canonical,Fin.addCases_left,decide_eq_true_eq]
        rintro hp ⟨l,hl,inc⟩
        exact apart p hp l hl inc
      | right l => simp only [probe,canonical,Fin.addCases_right,imp_self]
    have no := acts_mono hm bound C.output (cutBody_le_actual hm valid _ _ on)
    rw [reject Y sY.le] at no
    contradiction
  · cases lab : label (wire w) with
    | none => simp [residualFormula,lab,PlaneFormula.eval] at on
    | some v =>
      obtain ⟨hv,e⟩ := valid _ _ lab
      simp only [residualFormula,lab,eval_eraseLeaf,eval_bodyFormula hm bin] at on
      rw [e] at on
      rw [cut_residual_rejects hm valid I degree join fresh positive reject X Y sX sY apart v hv] at on
      contradiction

theorem bodyFormula_input {n : ℕ} (C : Circuit) (label : ℕ → Option (Fin n))
    (i : Fin n) : bodyFormula C label i.val = .leaf i := by
  simp [bodyFormula,localFormula,i.isLt]

theorem leaves_bodyFormula_gate {n : ℕ} {C : Circuit} (label : ℕ → Option (Fin n))
    {p i j : ℕ} {g : Gate} (hg : C.gates[p]? = some g) (ports : g.inputs = [i,j])
    (hi : i < n+p) (hj : j < n+p) :
    (bodyFormula C label (n+p)).leaves =
      (cutFormula C label i).leaves ++ (cutFormula C label j).leaves := by
  have h : ¬n+p < n := by omega
  cases op : g.op <;>
    simp [bodyFormula,localFormula,h,hg,ports,op,readFormula,hi,hj,PlaneFormula.leaves]

theorem count_cutFormula {n : ℕ} (C : Circuit) (label : ℕ → Option (Fin n))
    (i : ℕ) (v : Fin n) : (cutFormula C label i).leaves.count v =
      match label i with
      | none => (bodyFormula C label i).leaves.count v
      | some u => if u = v then 1 else 0 := by
  rw [cutFormula.eq_def]
  cases label i with
  | none => rfl
  | some u => by_cases h : u = v <;> simp [PlaneFormula.leaves,h]

theorem mem_of_own_singleton {n : ℕ} (v : Fin n) (F : PlaneFormula (Fin n)) :
    PlaneFormula.eval (point {v}) F = true → v ∈ F.leaves := by
  induction F with
  | leaf u => simp [PlaneFormula.eval,point,PlaneFormula.leaves,eq_comm]
  | bot => simp [PlaneFormula.eval]
  | or a b ha hb =>
    simp only [PlaneFormula.eval,Bool.or_eq_true,PlaneFormula.leaves,List.mem_append]
    exact Or.imp ha hb
  | and a b ha _ =>
    simp only [PlaneFormula.eval,Bool.and_eq_true,PlaneFormula.leaves,List.mem_append]
    exact fun h => Or.inl (ha h.1)

theorem residual_saves_own {n : ℕ} {C : Circuit} (hm : Monotone2 C) (bin : BinaryInputs C)
    {label : ℕ → Option (Fin n)} (valid : LabelsFirst C label)
    (zero : ∀ k, val C (point (∅ : Finset (Fin n))) k = false)
    {i : ℕ} {u : Fin n} (lab : label i = some u) (v : Fin n) :
    (residualFormula C label i).leaves.count v + (if u = v then 1 else 0) ≤
      (bodyFormula C label i).leaves.count v := by
  rw [residualFormula,lab,leaves_eraseLeaf]
  by_cases eq : u = v
  · subst v
    obtain ⟨hv,rfl⟩ := valid i u lab
    have on := cutBody_own_singleton hm valid zero hv
    rw [← eval_bodyFormula hm bin] at on
    have positive := List.count_pos_iff.mpr (mem_of_own_singleton u _ on)
    have cleared : ((bodyFormula C label (firstBranch C u hv)).leaves.filter (· != u)).count u = 0 :=
      List.count_eq_zero.mpr (by simp)
    rw [cleared,ite_eq_left rfl,Nat.zero_add]
    exact positive
  · have pass : (v != u) = true := by simpa [ne_comm] using eq
    rw [ite_eq_right eq,Nat.add_zero,List.count_filter (p := fun a => a != u) pass]

open PlaneTightFanout

theorem binary_of_tight {n : ℕ} {C : Circuit} (hm : Monotone2 C) (h : Tight n C) : BinaryInputs C := by
  intro p g hg
  obtain ⟨i,j,ins,_⟩ := (gate_inputs hm h hg).2
  exact ⟨i,j,ins⟩

theorem cover_first_labels {n : ℕ} {C : Circuit} {label : ℕ → Option (Fin n)}
    (valid : LabelsFirst C label) (ho : C.output < n+C.size) :
    ∀ j v, label j = some v → ∃ w ∈ branchCuts n C, (w : ℕ) = j := by
  intro j v lab
  obtain ⟨hv,rfl⟩ := valid j v lab
  have spec := firstBranch_spec v hv
  exact ⟨⟨_,(next_le spec.1).trans_lt ho⟩,mem_branchCuts.mpr spec.2.2,rfl⟩

open Classical in
theorem tight_forest_budget {n : ℕ} {C : Circuit} (hm : Monotone2 C) (tight : Tight n C)
    (ho : C.output < n+C.size) {label : ℕ → Option (Fin n)} (valid : LabelsFirst C label)
    (saturated : ∀ w ∈ branchCuts n C, ∃ u, label w.val = some u) (v : Fin n) :
    (cutForest C label Fin.val (branchCuts n C)).leaves.count v ≤
      1 + (if Eligible C v then 1 else 0 : ℕ) := by
  classical
  let root : Wire n C := ⟨C.output,ho⟩
  let cuts := branchCuts n C
  let parent := wireParents n C
  let before (w : Wire n C) := (bodyFormula C label w.val).leaves.count v
  let after (w : Wire n C) := (cutFormula C label w.val).leaves.count v
  let seed (w : Wire n C) := if label w.val = some v then 1 else 0
  let raw (w : Wire n C) := if w.val = v.val then 1 else 0
  have build (w : Wire n C) : before w = raw w + ∑ u ∈ parent w, after u := by
    by_cases input : w.val < n
    · let u : Fin n := ⟨w.val,input⟩
      have body : bodyFormula C label w.val = .leaf u := bodyFormula_input C label u
      have par : parent w = ∅ := wireParents_input input
      rw [par]
      change (bodyFormula C label w.val).leaves.count v = _
      rw [body]
      by_cases eq : w.val = v.val
      · have same : u = v := Fin.ext eq
        simp [raw,same,eq,PlaneFormula.leaves]
      · have ne : u ≠ v := fun e => eq (congrArg Fin.val e)
        simp [raw,ne,eq,PlaneFormula.leaves]
    · let p := w.val-n
      have hw : w.val=n+p := by dsimp [p]; omega
      have hp : p < C.gates.length := by
        have := w.isLt
        change w.val < n+C.gates.length at this
        omega
      let g := C.gates[p]
      have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.mpr ⟨hp,rfl⟩
      obtain ⟨i,j,ins,ne,hi,hj⟩ := (gate_inputs hm tight hg).2
      let a : Wire n C := ⟨i,by have := w.isLt; omega⟩
      let b : Wire n C := ⟨j,by have := w.isLt; omega⟩
      have ab : a ≠ b := fun eq => ne (congrArg Fin.val eq)
      have par : parent w = {a,b} := wireParents_gate tight hg hw ins (hw ▸ hi) (hw ▸ hj)
      have form := leaves_bodyFormula_gate label hg ins hi hj
      have notV : w.val ≠ v.val := by have := v.isLt; omega
      rw [par,Finset.sum_pair ab]
      simp only [raw,ite_eq_right notV,Nat.zero_add]
      simp only [before,hw,form,List.count_append]
      rfl
  have cut (w : Wire n C) : after w = if w ∈ cuts then seed w else before w := by
    change (cutFormula C label w.val).leaves.count v = _
    rw [count_cutFormula]
    by_cases hit : w ∈ cuts
    · obtain ⟨u,lab⟩ := saturated w hit
      simp [hit,seed,lab]
    · have missing : label w.val = none := by
        cases eq : label w.val with
        | none => rfl
        | some u =>
          obtain ⟨hu,ea⟩ := valid _ _ eq
          exact (hit (mem_branchCuts.mpr (ea ▸ (firstBranch_spec u hu).2.2))).elim
      simp [missing,hit,before]
  let vw : Wire n C := ⟨v.val,by have := v.isLt; omega⟩
  have rawOne : ∑ w, raw w = 1 := by
    have er (w : Wire n C) : raw w = if w = vw then 1 else 0 := by
      simp only [raw,Fin.ext_iff,vw]
    simp [er]
  have cardSeed : ∑ w ∈ cuts, seed w = (cuts.filter fun w => label w.val = some v).card := by
    simp [seed]
  have seedBound : (∑ w ∈ cuts, seed w) ≤ (if Eligible C v then 1 else 0 : ℕ) := by
    rw [cardSeed]
    by_cases hv : Eligible C v
    · rw [ite_eq_left hv]
      apply Finset.card_le_one_iff.mpr
      intro a b ha hb
      obtain ⟨_,ea⟩ := valid _ _ (Finset.mem_filter.mp ha).2
      obtain ⟨_,eb⟩ := valid _ _ (Finset.mem_filter.mp hb).2
      exact Fin.ext (ea.trans eb.symm)
    · rw [ite_eq_right hv]
      have empty : (cuts.filter fun w => label w.val = some v) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro w hw
        exact hv (valid _ _ (Finset.mem_filter.mp hw).2).choose
      simp [empty]
  have balance := cutForestLeafCount root cuts parent raw seed before after (root_not_cut ho)
    build cut (wire_fanout tight ho)
  rw [rawOne] at balance
  let residual (w : Wire n C) := (residualFormula C label w.val).leaves.count v
  have remove (w : Wire n C) (hw : w ∈ cuts) : residual w + seed w ≤ before w := by
    obtain ⟨u,lab⟩ := saturated w hw
    simpa [residual,before,seed,lab] using
      residual_saves_own hm (binary_of_tight hm tight) valid (all_zero hm tight) lab v
  have total := cutForestResidualBudget cuts (before root) before residual seed balance remove
  rw [count_cutForest]
  exact total.trans (Nat.add_le_add_left seedBound 1)

theorem forest_plane_samples {n q : ℕ} {C : Circuit} (hm : Monotone2 C) (tight : Tight (n+n) C)
    (ho : C.output < (n+n)+C.size) {label : ℕ → Option (Fin (n+n))} (valid : LabelsFirst C label)
    (I : Fin n → Fin n → Prop) [DecidableRel I] (q2 : 2 ≤ q)
    (degree : ∀ p, Fintype.card {l // I p l} = q+1)
    (join : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (fresh : ∀ T : Finset (Fin n), T.card ≤ q → ∀ l ∉ T, ∃ p, I p l ∧ ∀ k ∈ T, ¬ I p k)
    (positive : ∀ p l, I p l → val C (point {Fin.castAdd n p, Fin.natAdd n l}) C.output = true)
    (reject : ∀ T : Finset (Fin n), T.card ≤ q → val C (canonical I T) C.output = false) :
    let F := cutForest C label Fin.val (branchCuts (n+n) C)
    (∀ p : Fin n, F.eval (fun v => decide (v = Fin.castAdd n p)) = false) ∧
    (∀ l : Fin n, F.eval (fun v => decide (v = Fin.natAdd n l)) = false) ∧
    (∀ p l : Fin n, F.eval (fun v => decide (v = Fin.castAdd n p ∨ v = Fin.natAdd n l)) = true ↔ I p l) := by
  classical
  let cuts := branchCuts (n+n) C
  have neg := forest_rejects hm (binary_of_tight hm tight) valid Fin.val cuts I degree join
    fresh positive reject
  have separate (p l : Fin n) : Fin.castAdd n p ≠ Fin.natAdd n l := by
    intro e
    have h := congrArg Fin.val e
    change p.val = n+l.val at h
    omega
  have eqP (p : Fin n) : (fun v => decide (v = Fin.castAdd n p)) = probe {p} ∅ := by
    funext v
    induction v using Fin.addCases with
    | left u => simp only [probe,Fin.addCases_left,Fin.castAdd_inj,Finset.mem_singleton]
    | right u => simp only [probe,Fin.addCases_right,(separate p u).symm,Finset.notMem_empty]
  have eqL (l : Fin n) : (fun v => decide (v = Fin.natAdd n l)) = probe ∅ {l} := by
    funext v
    induction v using Fin.addCases with
    | left u => simp only [probe,Fin.addCases_left,separate u l,Finset.notMem_empty]
    | right u => simp only [probe,Fin.addCases_right,Fin.natAdd_inj,Finset.mem_singleton]
  have eqPair (p l : Fin n) : (fun v => decide (v = Fin.castAdd n p ∨ v = Fin.natAdd n l)) =
      probe {p} {l} := by
    funext v
    induction v using Fin.addCases with
    | left u => simp only [probe,Fin.addCases_left,separate u l,Fin.castAdd_inj,or_false,Finset.mem_singleton]
    | right u => simp only [probe,Fin.addCases_right,(separate p u).symm,Fin.natAdd_inj,false_or,Finset.mem_singleton]
  refine ⟨fun p => ?_,fun l => ?_,fun p l => ?_⟩
  · rw [eqP]
    exact neg {p} ∅ (by simp; omega) (by simp; omega) (by simp)
  · rw [eqL]
    exact neg ∅ {l} (by simp) (by simp; omega) (by simp)
  · constructor
    · intro yes
      by_contra no
      rw [eqPair] at yes
      have off := neg {p} {l} (by simp; omega) (by simp; omega) (by simpa using no)
      rw [off] at yes
      contradiction
    · intro edge
      have hit := forest_positive hm (binary_of_tight hm tight) valid Fin.val cuts
        (cover_first_labels valid ho) (positive p l edge)
      have eq : point {Fin.castAdd n p,Fin.natAdd n l} =
          (fun v => decide (v = Fin.castAdd n p ∨ v = Fin.natAdd n l)) := by
        funext v
        simp only [point,Finset.mem_insert,Finset.mem_singleton]
      rw [eq] at hit
      exact hit

end PlaneBranchWitness
end

-- PlaneStrictLower
section
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PlaneBranchWitness PlaneTightFanout PlaneEqualityContext

theorem freshForForest {q n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (cols : ∀ l, Fintype.card {p // I p l} = q+1)
    (join : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (T : Finset (Fin n)) (few : T.card ≤ q) (l : Fin n) (outside : l ∉ T) :
    ∃ p, I p l ∧ ∀ k ∈ T, ¬ I p k := by
  classical
  by_contra missing
  have pick (p : {p // I p l}) : ∃ k : T, I p.val k.val := by
    by_contra absent
    exact missing ⟨p.val, p.property, fun k hk inc => absent ⟨⟨k,hk⟩,inc⟩⟩
  let f (p : {p // I p l}) := (pick p).choose
  have mem (p : {p // I p l}) : I p.val (f p).val := (pick p).choose_spec
  have inj : Function.Injective f := by
    intro p r same
    apply Subtype.ext
    by_contra diff
    have both : I r.val (f p).val := same ▸ mem r
    have idLine := (join p.val r.val diff).unique ⟨mem p,both⟩ ⟨p.property,r.property⟩
    exact outside (idLine ▸ (f p).property)
  have cap := Fintype.card_le_of_injective f inj
  rw [cols l,Fintype.card_coe] at cap
  omega

theorem strictPlaneSize (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I] (C : Circuit)
    (big : 101 ≤ q) (order : n = q^2+q+1)
    (cols : ∀ l, Fintype.card {p // I p l} = q+1)
    (join : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (hm : Monotone2 C)
    (yes : ∀ p l, I p l → circuitFun (n+n) C (fun i => decide (i=L p ∨ i=R l)) = true)
    (no : ∀ x : Fin (n+n) → Bool, Fintype.card {l : Fin n // x (R l) = true} ≤ q →
      (¬∃ p l, I p l ∧ x (L p) = true ∧ x (R l) = true) → circuitFun (n+n) C x = false) :
    3*n ≤ C.size := by
  classical
  by_contra fail
  have previous := linearLower q n I C big order cols join hm yes no
  have eqn : C.size+1 = 3*n := by omega
  have ctx := of_equality q n I C big order cols join hm yes no eqn
  let labelAt := label n C
  have valid : LabelsFirst C labelAt := fun _ _ h => label_valid h
  have rows (p : Fin n) : Fintype.card {l // I p l} = q+1 :=
    (Fintype.card_subtype (I p)).trans (ctx.rows p)
  have pos (p l : Fin n) (edge : I p l) :
      Plane2866Graph.val C (Plane2866Graph.point {L p, R l}) C.output = true :=
    (Plane2866Graph.point_pair ctx.pairEval (L p) (R l)).mpr ((leftRight I p l).mpr edge)
  have neg (T : Finset (Fin n)) (few : T.card ≤ q) :
      Plane2866Graph.val C (canonical I T) C.output = false := by
    apply no (canonical I T)
    · have colValue (l : Fin n) : canonical I T (R l) = decide (l ∈ T) := Fin.addCases_right _
      simpa only [colValue,decide_eq_true_eq,Fintype.card_coe] using few
    · rintro ⟨p,l,inc,hp,hl⟩
      have pointValue : canonical I T (L p) = decide (¬∃ k ∈ T, I p k) := Fin.addCases_left _
      have lineValue : canonical I T (R l) = decide (l ∈ T) := Fin.addCases_right _
      rw [pointValue] at hp
      rw [lineValue] at hl
      exact (of_decide_eq_true hp) ⟨l,of_decide_eq_true hl,inc⟩
  let forest := cutForest C labelAt Fin.val (branchCuts (n+n) C)
  obtain ⟨offP,offL,pairs⟩ := forest_plane_samples hm ctx.tight ctx.outputBound valid I
    (show 2 ≤ q by omega) rows join (freshForForest I cols join) pos neg
  have counts (v : Fin (n+n)) := tight_forest_budget hm ctx.tight ctx.outputBound valid
    (fun w hw => (ctx.perCut w).mp hw) v
  apply twoShoresImpossible (n := n) (q := q) (by omega) (by omega) I forest rows cols join
  · intro v
    induction v using Fin.addCases with
    | left p => exact offP p
    | right l => exact offL l
  · exact pairs
  · rcases ctx.side with ⟨ps,ls⟩ | ⟨ps,ls⟩
    · exact Or.inl ⟨fun p => by simpa only [ite_eq_left (ps p)] using counts (L p),
        fun l => by simpa only [ite_eq_right (ls l)] using counts (R l)⟩
    · exact Or.inr ⟨fun p => by simpa only [ite_eq_right (ps p)] using counts (L p),
        fun l => by simpa only [ite_eq_left (ls l)] using counts (R l)⟩
end

-- PlaneThrough300
section
theorem postedPlaneThrough300 : have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.false)).getD x4 Bool.false ≠ (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.true)).getD x4 Bool.false) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x6)).getD x4 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x6)).getD x4 Bool.false); ∀ (x2 x3 : ℕ) (x4 : Fin x3 → Fin x3 → Prop) [x5 : DecidableRel x4] (x6 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x2 → x2 ≤ 300 → x3 = x2 ^ (2 : ℕ) + x2 + (1 : ℕ) → (∀ (x9 : Fin x3), Fintype.card { x10 : Fin x3 // x4 x10 x9 } = x2 + (1 : ℕ)) → (∀ (x10 x11 : Fin x3), x10 ≠ x11 → ∃! x13 : Fin x3, x4 x10 x13 ∧ x4 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x6 → x6.output < x3 + x3 + x6.size → (∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x13]? = Option.some x14 → ∃ (x16 : ℕ) (x17 : ℕ), x14.inputs = [x16, x17] ∧ x16 < x17 ∧ x17 < x3 + x3 + x13) → (∀ (x14 x15 : Fin x3), x4 x14 x15 → (PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 fun (x17 : Fin (x3 + x3)) => Decidable.decide (x17 = Fin.castAdd x3 x14 ∨ x17 = Fin.natAdd x3 x15)) = Bool.true) → (∀ (x15 : Fin (x3 + x3) → Bool), Fintype.card { x16 : Fin x3 // x15 (Fin.natAdd x3 x16) = Bool.true } ≤ x2 → (¬∃ (x17 : Fin x3) (x18 : Fin x3), x4 x17 x18 ∧ x15 (Fin.castAdd x3 x17) = Bool.true ∧ x15 (Fin.natAdd x3 x18) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 x15 = Bool.false) → ∀ x16 ⊆ Finset.range x6.size, (1 : ℕ) ≤ x16.card → (∀ (x19 : ℕ) (x20 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x19]? = Option.some x20 → (x19 ∈ x16 ↔ x1 x3 x6 x20)) → (100 : ℕ) * x16.card < x3 * x2 → x3 * x2 ≤ (100 : ℕ) * x6.size := by

  dsimp only
  intro q n I inst C lo hi order cols join hm _ _ yes no _ _ _ _ _
  have bound := strictPlaneSize q n I C (by omega) order cols join hm yes no
  have scaled := Nat.mul_le_mul_left n hi
  omega

#print axioms strictPlaneSize
#print axioms postedPlaneThrough300
end
