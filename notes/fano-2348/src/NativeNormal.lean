import DeskNormal

namespace FanoDeskNormal

open SignatureNormal

def zero : Sig := fun _ => false

/-- The tail gate clauses from the posted obstruction, with the first OR already
    present in the prefix. Indices in each lookup address the concatenated list. -/
def native (w s : List Sig) : Prop :=
  target ∈ w++s ∧ ∀ j < s.length, ∃ a b : ℕ, a ≠ b ∧ a < w.length+j ∧ b < w.length+j ∧
    legal ⟨(w++s).getD a zero,(w++s).getD b zero,s.getD j zero⟩

private theorem prefix_var (w rest : List Sig) (i : Fin w.length) :
    (w++rest).getD i.val zero = w[i.val] := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_append_left i.isLt]

private theorem native_cons (w : List Sig) (v : Sig) (s : List Sig) :
    native w (v::s) ↔
      (∃ i j : Fin w.length, i≠j ∧ legal ⟨w[i.val],w[j.val],v⟩) ∧ native (w++[v]) s := by
  constructor
  · rintro ⟨goal,steps⟩
    obtain ⟨a,b,ab,ha,hb,rule⟩ := steps 0 (by simp)
    let i : Fin w.length := ⟨a,by simpa using ha⟩
    let j : Fin w.length := ⟨b,by simpa using hb⟩
    have ar := prefix_var w (v::s) i
    have br := prefix_var w (v::s) j
    change (w++v::s).getD a zero = _ at ar
    change (w++v::s).getD b zero = _ at br
    rw [ar,br] at rule
    refine ⟨⟨i,j,fun eq => ab (congrArg Fin.val eq),rule⟩,?_,?_⟩
    · simpa [List.append_assoc] using goal
    · intro k hk
      obtain ⟨aa,bb,ne,h1,h2,yes⟩ := steps (k+1) (by simpa using hk)
      refine ⟨aa,bb,ne,by simp; omega,by simp; omega,?_⟩
      simpa [List.append_assoc,List.getD_eq_getElem?_getD] using yes
  · rintro ⟨⟨i,j,ij,yes⟩,goal,steps⟩
    refine ⟨by simpa [List.append_assoc] using goal,?_⟩
    intro k hk
    cases k with
    | zero =>
      refine ⟨i.val,j.val,fun eq => ij (Fin.ext eq),by simp,by simp,?_⟩
      rw [prefix_var w (v::s) i,prefix_var w (v::s) j]
      simpa [List.getD_eq_getElem?_getD] using yes
    | succ k =>
      obtain ⟨aa,bb,ne,h1,h2,yes⟩ := steps k (by simpa using hk)
      refine ⟨aa,bb,ne,by simp at h1; omega,by simp at h2; omega,?_⟩
      simpa [List.append_assoc,List.getD_eq_getElem?_getD] using yes

theorem native_iff (w s : List Sig) :
    native w s ↔ ∃ gs : List (Gate Sig), gs.map Gate.out=s ∧ indexed legal target w gs := by
  induction s generalizing w with
  | nil =>
    constructor
    · intro h
      exact ⟨[],rfl,by simpa [indexed] using h.1⟩
    · rintro ⟨gs,eq,ok⟩
      have empty : gs=[] := List.map_eq_nil_iff.mp eq
      subst gs
      exact ⟨by simpa [indexed] using ok,by simp⟩
  | cons v vs ih =>
    rw [native_cons]
    constructor
    · rintro ⟨⟨i,j,ij,rule⟩,rest⟩
      obtain ⟨gs,rfl,ok⟩ := (ih _).mp rest
      exact ⟨⟨w[i.val],w[j.val],v⟩::gs,rfl,rule,⟨i,j,ij,rfl,rfl⟩,ok⟩
    · rintro ⟨gs,eq,ok⟩
      cases gs with
      | nil => simp at eq
      | cons g gs =>
        obtain ⟨out,tail⟩ := List.cons.inj eq
        subst v
        subst vs
        obtain ⟨rule,⟨i,j,ne,l,r⟩,rest⟩ := ok
        exact ⟨⟨i,j,ne,by simpa [l,r] using rule⟩,(ih _).mpr ⟨gs,rfl,rest⟩⟩

theorem shortest_reification {first : Sig} {s : List Sig}
    (yes : native (seed++[first]) s)
    (minimal : ∀ other, native (seed++[first]) other → s.length ≤ other.length) :
    ∃ gs : List (Gate Sig), gs.map Gate.out=s ∧ shortestTail first gs := by
  obtain ⟨gs,outputs,ok⟩ := (native_iff _ _).mp yes
  refine ⟨gs,outputs,ok,?_⟩
  intro alt altOK
  have least := minimal (alt.map Gate.out) ((native_iff _ _).mpr ⟨alt,rfl,altOK⟩)
  simpa only [←outputs,List.length_map] using least

theorem native_count {first : Sig} {s : List Sig} (yes : native (seed++[first]) s)
    (minimal : ∀ other, native (seed++[first]) other → s.length ≤ other.length) :
    ∀ x : Sig, (seed++[first]++s).count x ≤ 2 := by
  obtain ⟨gs,rfl,short⟩ := shortest_reification yes minimal
  exact whole_count short

/-- Exactly the gate and output clauses of the 62-row obstruction. The independent
    length cap can be imposed after taking a shortest witness. -/
def posted (s : List Sig) : Prop :=
  target ∈ s ∧ ∀ j < s.length, ∃ a b : ℕ, a≠b ∧ a<14+j ∧ b<14+j ∧
    let A := (seed++s).getD a zero
    let B := (seed++s).getD b zero
    s.getD j zero = disj A B ∨ 0 < j ∧ s.getD j zero = conj A B

def firstOR (v : Sig) : Prop :=
  ∃ a b : Fin seed.length, a≠b ∧ v=disj seed[a.val] seed[b.val]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem first_disjunction_fresh :
    ∀ a b : Fin seed.length, a≠b → disj seed[a.val] seed[b.val] ∉ seed := by decide

theorem posted_cons (v : Sig) (s : List Sig) :
    posted (v::s) ↔ firstOR v ∧ native (seed++[v]) s := by
  have len : seed.length=14 := rfl
  have head : (v::s).getD 0 zero = v := by simp [List.getD_eq_getElem?_getD]
  constructor
  · rintro ⟨goal,rule⟩
    have yes : native seed (v::s) := by
      refine ⟨List.mem_append_right _ goal,?_⟩
      intro k hk
      obtain ⟨a,b,ne,ha,hb,ok⟩ := rule k hk
      exact ⟨a,b,ne,len ▸ ha,len ▸ hb,ok.imp_right And.right⟩
    obtain ⟨aa,bb,ne,ha,hb,ok⟩ := rule 0 (by simp)
    let a : Fin seed.length := ⟨aa,by omega⟩
    let b : Fin seed.length := ⟨bb,by omega⟩
    have yesOR := ok.resolve_right (fun impossible => (Nat.lt_irrefl _ impossible.1).elim)
    change (v::s).getD 0 zero = disj ((seed++v::s).getD a.val zero) ((seed++v::s).getD b.val zero) at yesOR
    rw [head,prefix_var seed _ a,prefix_var seed _ b] at yesOR
    exact ⟨⟨a,b,fun eq => ne (congrArg Fin.val eq),yesOR⟩,((native_cons _ _ _).mp yes).2⟩
  · rintro ⟨⟨a,b,ne,first⟩,tail⟩
    have yes := (native_cons seed v s).mpr ⟨⟨a,b,ne,Or.inl first⟩,tail⟩
    refine ⟨(List.mem_append.mp yes.1).resolve_left target_not_raw,?_⟩
    intro k hk
    by_cases beginning : k=0
    · subst k
      refine ⟨a.val,b.val,fun eq => ne (Fin.ext eq),by rw [←len]; simp,by rw [←len]; simp,Or.inl ?_⟩
      rw [head,prefix_var seed _ a,prefix_var seed _ b]
      exact first
    · obtain ⟨i,j,ij,hi,hj,law⟩ := yes.2 k hk
      exact ⟨i,j,ij,len ▸ hi,len ▸ hj,law.imp_right (fun ok => ⟨by omega,ok⟩)⟩

theorem posted_count (v : Sig) (s : List Sig) (yes : posted (v::s))
    (minimal : ∀ alt, posted alt → (v::s).length ≤ alt.length) :
    ∀ x : Sig, (seed++v::s).count x ≤ 2 := by
  obtain ⟨keep,ok⟩ := (posted_cons _ _).mp yes
  have bound := native_count ok (fun alt proof => by
    have le := minimal (v::alt) ((posted_cons _ _).mpr ⟨keep,proof⟩)
    simpa using le)
  simpa [List.append_assoc] using bound

/-- A bounded witness admits a shortest tail of no greater length while retaining
    the same first OR. Its reified gates also obey the forced-AND theorem. -/
theorem normalize (first : Sig) (s : List Sig) (yes : posted (first::s)) :
    ∃ t : List Sig, t.length ≤ s.length ∧ posted (first::t) ∧
      (∀ x : Sig, (seed++first::t).count x ≤ 2) ∧
      ∃ gs : List (Gate Sig), gs.map Gate.out=t ∧ shortestTail first gs := by
  classical
  obtain ⟨firstOK,tailOK⟩ := (posted_cons _ _).mp yes
  let P (k : ℕ) := ∃ t : List Sig, native (seed++[first]) t ∧ t.length=k
  have nonempty : ∃ k, P k := ⟨s.length,s,tailOK,rfl⟩
  obtain ⟨t,ok,length⟩ := Nat.find_spec nonempty
  have minTail (u : List Sig) (hu : native (seed++[first]) u) : t.length ≤ u.length :=
    length.trans_le (Nat.find_min' nonempty ⟨u,hu,rfl⟩)
  exact ⟨t,minTail s tailOK,(posted_cons _ _).mpr ⟨firstOK,ok⟩,
    by simpa [List.append_assoc] using native_count ok minTail,shortest_reification ok minTail⟩

end FanoDeskNormal
