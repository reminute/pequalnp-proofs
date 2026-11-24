import SignatureNormal

namespace FanoDeskNormal

open SignatureNormal

abbrev Sig := Fin 62 → Bool

def seedMasks : List ℕ :=
  [2594090156585648135,15270196031782968,58150373818816,94946423956573696,
   54820275478360064,3870282840506368,133412159488,1911954591369396745,
   218716039641305168,189725234880873600,156548607028504576,229736628137050114,
   270286071509155872,288160007408582916]

def seed : List Sig := seedMasks.map fun w t => w.testBit t.val
def target : Sig := fun t => decide (t.val < 21)
def disj (a b : Sig) : Sig := fun t => a t || b t
def conj (a b : Sig) : Sig := fun t =>
  if t=60 then (a 58 && b 60) || (a 60 && b 58)
  else if t=61 then (a 59 && b 61) || (a 61 && b 59)
  else a t && b t

def legal (g : Gate Sig) : Prop := g.out=disj g.left g.right ∨ g.out=conj g.left g.right

set_option maxRecDepth 12000 in
theorem seed_nodup : seed.Nodup := by decide

set_option maxRecDepth 12000 in
theorem target_not_raw : target ∉ seed := by decide

theorem initial_cap (first : Sig) : ∀ x, (seed++[first]).count x ≤ 2 := by
  intro x
  have cap := List.nodup_iff_count_le_one.mp seed_nodup x
  by_cases h : first=x <;> simp [h] <;> omega

def shortestTail (first : Sig) (gs : List (Gate Sig)) : Prop :=
  indexed legal target (seed++[first]) gs ∧
    ∀ alt, indexed legal target (seed++[first]) alt → gs.length ≤ alt.length

theorem tail_as_pool {first : Sig} {gs : List (Gate Sig)} (h : shortestTail first gs) :
    shortest legal target (fun x => (seed++[first]).count x) gs :=
  ⟨(run_iff_indexed ..).mpr h.1,fun alt good => h.2 alt ((run_iff_indexed ..).mp good)⟩

/-- Holds for every fixed first OR, and also when only its opcode is prescribed:
    global minimality implies minimality while keeping that entire gate fixed. -/
theorem whole_count {first : Sig} {gs : List (Gate Sig)} (h : shortestTail first gs) (x : Sig) :
    ((seed++[first])++gs.map Gate.out).count x ≤ 2 := by
  have bound := at_most_two (initial_cap first) (tail_as_pool h) x
  simpa only [finish_count,List.count_append] using bound

theorem trace_loss {x : Sig} (different : conj x x ≠ x) :
    (x 60=true ∧ x 58=false) ∨ (x 61=true ∧ x 59=false) := by
  by_contra bad
  apply different
  funext t
  by_cases a : t=60
  · subst t
    cases h : x 60 <;> cases k : x 58 <;> simp_all [conj]
  by_cases b : t=61
  · subst t
    cases h : x 61 <;> cases k : x 59 <;> simp_all [conj]
  simp [conj,a,b]

theorem every_legal {P : Pool Sig} (gs : List (Gate Sig)) (h : run legal target P gs) :
    ∀ q ∈ gs, legal q := by
  induction gs generalizing P with
  | nil => simp
  | cons g gs ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | mem
    · exact h.1
    · exact ih h.2.2 q mem

theorem necessary_AND {first : Sig} (pre : List (Gate Sig)) (g : Gate Sig) (rest : List (Gate Sig))
    (h : shortestTail first (pre++g::rest))
    (before : 0 < (seed++[first]++pre.map Gate.out).count g.out) :
    (∃ use ∈ rest, use.left=g.out ∧ use.right=g.out ∧
      use.out=conj g.out g.out ∧ use.out≠g.out) ∧
    ((g.out 60=true ∧ g.out 58=false) ∨ (g.out 61=true ∧ g.out 59=false)) := by
  let P := finish (fun x => (seed++[first]).count x) pre
  have here : shortest legal target P (g::rest) := shortened_prefix _ _ _ (tail_as_pool h)
  have cap (x : Sig) : P x ≤ 2 := by
    have all := whole_count h x
    simp only [List.map_append,List.count_append] at all
    change finish _ _ _ ≤ 2
    simp only [finish_count,List.count_append]
    omega
  have old : 0 < P g.out := by simpa only [P,finish_count,List.count_append] using before
  obtain ⟨use,mem,l,r,different⟩ := duplicate_needs_new_result cap here old
  have law := every_legal rest here.1.2.2 use mem
  unfold legal at law
  rw [l,r] at law
  have idOR : disj g.out g.out = g.out := by funext i; simp [disj]
  have isAnd := law.resolve_left (fun impossible => different (impossible.trans idOR))
  exact ⟨⟨use,mem,l,r,isAnd,different⟩,trace_loss (fun eq => different (isAnd.trans eq))⟩

end FanoDeskNormal
