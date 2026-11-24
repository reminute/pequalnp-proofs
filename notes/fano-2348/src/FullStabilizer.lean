import FlagOrbits

namespace FanoFlag

def seed : List V := [0,7,1,2]
def expanded : List V := [0,7,1,2,3,8,9,11,12,13]

-- Fixed vertices determine equality and adjacency on this list of landmarks.
def looks (landmarks : List V) (a b : V) : Prop :=
  ∀ z ∈ landmarks, (a=z ↔ b=z) ∧ adj a z=adj b z

instance (l : List V) (a b : V) : Decidable (looks l a b) :=
  inferInstanceAs (Decidable (∀ z ∈ l, (a=z ↔ b=z) ∧ adj a z=adj b z))

theorem first_layer : ∀ a ∈ expanded, ∀ b : V, looks seed a b → a=b := by decide +kernel
theorem second_layer : ∀ a b : V, looks expanded a b → a=b := by decide +kernel

theorem fixed_looks {f : V → V} (injective : Function.Injective f)
    (preserve : ∀ x y, adj (f x) (f y)=adj x y) {l : List V} (fixed : ∀ z ∈ l, f z=z) (a : V) :
    looks l a (f a) := by
  intro z mem
  have hz := fixed z mem
  exact ⟨⟨fun e => e ▸ hz,fun e => injective (e.trans hz.symm)⟩,
    (preserve a z).symm.trans (congrArg (adj (f a)) hz)⟩

theorem four_determine {f : V → V} (injective : Function.Injective f)
    (preserve : ∀ x y, adj (f x) (f y)=adj x y)
    (f0 : f 0=0) (f7 : f 7=7) (f1 : f 1=1) (f2 : f 2=2) (a : V) : f a=a := by
  have base : ∀ z ∈ seed, f z=z := by
    intro z hz
    simp only [seed,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> assumption
  have mid : ∀ z ∈ expanded, f z=z :=
    fun z hz => (first_layer z hz _ (fixed_looks injective preserve base z)).symm
  exact (second_layer a _ (fixed_looks injective preserve mid a)).symm

def basePoint (swap : Bool) : V := if swap then 7 else 0
def baseLine (swap : Bool) : V := if swap then 0 else 7

-- An image of the labelled point 1 is a neighbor of the image of line 0.
-- The image of point 2 is not such a neighbor. It shares a neighbor with
-- the image of point 0, which places it in that point's shore.
theorem basis_covered : ∀ (swap : Bool) (c d : V),
    c≠basePoint swap → adj c (baseLine swap)=true →
    d≠basePoint swap → adj d (baseLine swap)=false →
    (∃ z : V, adj d z=true ∧ adj (basePoint swap) z=true) →
    ∃ g : G, perm g 0=basePoint swap ∧ perm g 7=baseLine swap ∧ perm g 1=c ∧ perm g 2=d := by
  decide +kernel

-- Every adjacency-preserving injection stabilizing {0,7} is in the
-- displayed group. This includes permutations interchanging points and lines.
theorem all_automorphisms {f : V → V} (injective : Function.Injective f)
    (preserve : ∀ x y, adj (f x) (f y)=adj x y)
    (flag : (f 0=0 ∧ f 7=7) ∨ (f 0=7 ∧ f 7=0)) :
    ∃ g : G, ∀ x : V, f x=perm g x := by
  have c : f 1≠f 0 := injective.ne (by decide)
  have d : f 2≠f 0 := injective.ne (by decide)
  have on : adj (f 1) (f 7)=true := (preserve 1 7).trans (by decide)
  have off : adj (f 2) (f 7)=false := (preserve 2 7).trans (by decide)
  have common : ∃ z : V, adj (f 2) z=true ∧ adj (f 0) z=true :=
    ⟨f 13,(preserve 2 13).trans (by decide),(preserve 0 13).trans (by decide)⟩
  obtain ⟨swap,s0,s7⟩ : ∃ s, f 0=basePoint s ∧ f 7=baseLine s := by
    rcases flag with ⟨h,k⟩ | ⟨h,k⟩
    · exact ⟨false,h,k⟩
    · exact ⟨true,h,k⟩
  rw [s0] at c d common
  rw [s7] at on off
  obtain ⟨g,a0,a7,a1,a2⟩ := basis_covered swap _ _ c on d off common
  let back := perm (inv g) ∘ f
  have bi : Function.Injective back := (perm_injective (inv g)).comp injective
  have bp (x y : V) : adj (back x) (back y)=adj x y :=
    (preserves_adj _ _ _).trans (preserve x y)
  have cancel (x : V) (e : f x=perm g x) : back x=x :=
    (congrArg (perm (inv g)) e).trans (left_inv g x)
  have fixed (x : V) : back x=x := four_determine bi bp
    (cancel 0 (s0.trans a0.symm)) (cancel 7 (s7.trans a7.symm))
    (cancel 1 a1.symm) (cancel 2 a2.symm) x
  exact ⟨g,fun x => (right_inv g (f x)).symm.trans (congrArg (perm g) (fixed x))⟩

end FanoFlag

#print axioms FanoFlag.all_automorphisms
