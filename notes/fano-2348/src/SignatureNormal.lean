import Mathlib

namespace SignatureNormal

variable {α : Type} [DecidableEq α]

/-- A binary instruction with the signatures of its two operands and its result. -/
structure Gate (α : Type) where
  left : α
  right : α
  out : α

abbrev Pool (α : Type) := α → ℕ

def add (P : Pool α) (x : α) : Pool α := fun v => P v + if v=x then 1 else 0

def available (P : Pool α) (u v : α) : Prop :=
  0 < P u ∧ 0 < P v ∧ (u=v → 2 ≤ P u)

def run (legal : Gate α → Prop) (goal : α) (P : Pool α) : List (Gate α) → Prop
  | [] => 0 < P goal
  | g::gs => legal g ∧ available P g.left g.right ∧ run legal goal (add P g.out) gs

def shortest (legal : Gate α → Prop) (goal : α) (P : Pool α) (gs : List (Gate α)) : Prop :=
  run legal goal P gs ∧ ∀ alt, run legal goal P alt → gs.length ≤ alt.length

theorem add_swap (P : Pool α) (x y : α) : add (add P x) y = add (add P y) x := by
  funext v
  simp [add,Nat.add_right_comm]

theorem tail_shortest {legal : Gate α → Prop} {goal : α} {P : Pool α} {g : Gate α} {gs : List (Gate α)}
    (h : shortest legal goal P (g::gs)) : shortest legal goal (add P g.out) gs := by
  refine ⟨h.1.2.2,fun alt good => ?_⟩
  have le := h.2 (g::alt) ⟨h.1.1,h.1.2.1,good⟩
  simpa using le

/-- Redirect an extra wire to another available copy. When only one copy remains,
    this is valid if no later instruction requests two copies simultaneously. -/
theorem discard {legal : Gate α → Prop} {goal x : α} {P : Pool α} {gs : List (Gate α)}
    (one : 0 < P x)
    (safe : 2 ≤ P x ∨ ∀ g ∈ gs, ¬(g.left=x ∧ g.right=x))
    (ok : run legal goal (add P x) gs) : run legal goal P gs := by
  induction gs generalizing P with
  | nil =>
    change 0 < P goal
    change 0 < add P x goal at ok
    by_cases eq : goal=x
    · simpa [eq] using one
    · simpa [add,eq] using ok
  | cons g gs ih =>
    obtain ⟨rule,⟨l,r,both⟩,tail⟩ := ok
    have nonzero (v : α) (hv : 0 < add P x v) : 0 < P v := by
      by_cases eq : v=x
      · simpa [eq] using one
      · simpa [add,eq] using hv
    refine ⟨rule,⟨nonzero _ l,nonzero _ r,?_⟩,?_⟩
    · intro lr
      by_cases lx : g.left=x
      · rw [lx]
        exact safe.elim id (fun never => (never g (by simp) ⟨lx,lr ▸ lx⟩).elim)
      · simpa [add,lx] using both lr
    · rw [add_swap] at tail
      apply ih (P := add P g.out) _ _ tail
      · simp only [add]
        omega
      · exact safe.imp (fun two => two.trans (Nat.le_add_right ..))
          (fun never h hg => never h (List.mem_cons_of_mem _ hg))

theorem cannot_make_third {legal : Gate α → Prop} {goal : α} {P : Pool α} {g : Gate α}
    {gs : List (Gate α)} (short : shortest legal goal P (g::gs)) : P g.out ≤ 1 := by
  by_contra! two
  have shorter := short.2 gs (discard (by omega) (Or.inl two) short.1.2.2)
  simp at shorter

/-- A later instruction must actually need both copies. -/
theorem duplicate_needs_pair {legal : Gate α → Prop} {goal : α} {P : Pool α}
    {g : Gate α} {gs : List (Gate α)} (short : shortest legal goal P (g::gs))
    (old : 0 < P g.out) : ∃ h ∈ gs, h.left=g.out ∧ h.right=g.out := by
  classical
  by_contra none
  have shorter := short.2 gs (discard old (Or.inr (fun h hm same => none ⟨h,hm,same⟩)) short.1.2.2)
  simp at shorter

def finish (P : Pool α) : List (Gate α) → Pool α
  | [] => P
  | g::gs => finish (add P g.out) gs

theorem finish_count (P : Pool α) (gs : List (Gate α)) (x : α) :
    finish P gs x = P x + (gs.map Gate.out).count x := by
  induction gs generalizing P with
  | nil => simp [finish]
  | cons g gs ih =>
    simp only [finish,ih,add,List.map_cons,List.count_cons]
    by_cases same : g.out=x
    · simp [same]
      omega
    · simp [same,Ne.symm same]

theorem at_most_two {legal : Gate α → Prop} {goal : α} {P : Pool α} {gs : List (Gate α)}
    (start : ∀ x, P x ≤ 2) (short : shortest legal goal P gs) : ∀ x, finish P gs x ≤ 2 := by
  induction gs generalizing P with
  | nil => exact start
  | cons g gs ih =>
    apply ih _ (tail_shortest short)
    intro x
    by_cases same : x=g.out
    · have le := cannot_make_third short
      simp [add,same,le]
    · simpa [add,same] using start x

theorem duplicate_needs_new_result {legal : Gate α → Prop} {goal : α} {P : Pool α}
    {g : Gate α} {gs : List (Gate α)} (start : ∀ x, P x ≤ 2)
    (short : shortest legal goal P (g::gs)) (old : 0 < P g.out) :
    ∃ h ∈ gs, h.left=g.out ∧ h.right=g.out ∧ h.out≠g.out := by
  obtain ⟨h,hm,left,right⟩ := duplicate_needs_pair short old
  refine ⟨h,hm,left,right,?_⟩
  intro eq
  have hm' : g.out ∈ gs.map Gate.out := List.mem_map.mpr ⟨h,hm,eq⟩
  have extra := List.count_pos_iff.mpr hm'
  have bound := at_most_two start short g.out
  change finish (add P g.out) gs g.out ≤ 2 at bound
  rw [finish_count] at bound
  simp [add] at bound
  omega

def slots (w : List α) (v : α) : Finset (Fin w.length) := Finset.univ.filter fun i => w[i.val]=v

theorem slots_card (w : List α) (v : α) : (slots w v).card = w.count v := by
  have sums (s : List α) : (∑ i : Fin s.length, if s[i.val]=v then 1 else 0) = s.count v := by
    induction s with
    | nil => simp
    | cons a s ih =>
      change (∑ i : Fin (s.length+1), if (a::s)[i.val]=v then 1 else 0) = _
      rw [Fin.sum_univ_succ]
      by_cases eq : a=v <;> simp [List.count_cons,eq,ih,Nat.add_comm]
  simpa [slots] using sums w

/-- Readability by signature counts is exactly readability at two different
    physical indices, including when both requested signatures coincide. -/
theorem available_iff_indices (w : List α) (u v : α) :
    available (fun a => w.count a) u v ↔
      ∃ i j : Fin w.length, i ≠ j ∧ w[i.val]=u ∧ w[j.val]=v := by
  have mem (a : α) (i : Fin w.length) : i ∈ slots w a ↔ w[i.val]=a := by simp [slots]
  change (0 < w.count u ∧ 0 < w.count v ∧ (u=v → 2 ≤ w.count u)) ↔ _
  constructor
  · rintro ⟨l,r,pair⟩
    by_cases same : u=v
    · subst v
      have cap : 1 < (slots w u).card := (slots_card w u) ▸ pair rfl
      obtain ⟨i,j,hi,hj,diff⟩ := Finset.one_lt_card_iff.mp cap
      exact ⟨i,j,diff,(mem _ _).mp hi,(mem _ _).mp hj⟩
    · obtain ⟨i,hi⟩ := Finset.card_pos.mp ((slots_card w u) ▸ l)
      obtain ⟨j,hj⟩ := Finset.card_pos.mp ((slots_card w v) ▸ r)
      have ei := (mem _ _).mp hi
      have ej := (mem _ _).mp hj
      exact ⟨i,j,fun eq => same (ei.symm.trans (eq ▸ ej)),ei,ej⟩
  · rintro ⟨i,j,diff,hi,hj⟩
    refine ⟨?_,?_,?_⟩
    · rw [← slots_card]
      exact Finset.card_pos.mpr ⟨i,(mem _ _).mpr hi⟩
    · rw [← slots_card]
      exact Finset.card_pos.mpr ⟨j,(mem _ _).mpr hj⟩
    · rintro rfl
      rw [← slots_card]
      exact Finset.one_lt_card_iff.mpr ⟨i,j,(mem _ _).mpr hi,(mem _ _).mpr hj,diff⟩

def indexed (legal : Gate α → Prop) (goal : α) (w : List α) : List (Gate α) → Prop
  | [] => goal ∈ w
  | g::gs => legal g ∧ (∃ i j : Fin w.length, i ≠ j ∧ w[i.val]=g.left ∧ w[j.val]=g.right) ∧
      indexed legal goal (w++[g.out]) gs

theorem run_iff_indexed (legal : Gate α → Prop) (goal : α) (w : List α) (gs : List (Gate α)) :
    run legal goal (fun a => w.count a) gs ↔ indexed legal goal w gs := by
  induction gs generalizing w with
  | nil => exact List.count_pos_iff
  | cons g gs ih =>
    have nxt : add (fun a => w.count a) g.out = (fun a => (w++[g.out]).count a) := by
      funext a
      by_cases eq : a=g.out
      · simp [add,eq]
      · simp [add,eq,Ne.symm eq,List.count_cons]
    rw [run,indexed,available_iff_indices,nxt,ih]

theorem shortened_prefix {legal : Gate α → Prop} {goal : α} (P : Pool α) (pre tail : List (Gate α))
    (short : shortest legal goal P (pre++tail)) : shortest legal goal (finish P pre) tail := by
  induction pre generalizing P with
  | nil => exact short
  | cons g gs ih => exact ih (add P g.out) (tail_shortest short)

end SignatureNormal
