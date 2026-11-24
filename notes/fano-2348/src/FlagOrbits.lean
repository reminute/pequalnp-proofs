import PEqualNP.Defs

namespace FanoFlag

abbrev V := Fin 14
abbrev G := Fin 16
abbrev R := Fin 14

abbrev incident (p l : Fin 7) : Prop := p=l ∨ p=l+1 ∨ p=l+3
def adj (a b : V) : Bool :=
  if a.val<7 then
    if b.val<7 then false else decide (incident (Fin.ofNat 7 a.val) (Fin.ofNat 7 b.val))
  else if b.val<7 then decide (incident (Fin.ofNat 7 b.val) (Fin.ofNat 7 a.val)) else false

def ReceiptF (x : V → Bool) : Prop :=
  ∃ p l : Fin 7, incident p l ∧ x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true

def samePair (a b c d : V) : Prop := (a=c ∧ b=d) ∨ (a=d ∧ b=c)
instance (a b c d : V) : Decidable (samePair a b c d) := inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))

-- Rows 0–7 preserve both shores; rows 8–15 compose each of those with
-- the duality p ↦ line(−p), line(l) ↦ point(−l).
def images : List (List V) := [
  [0,1,2,3,4,5,6,7,8,9,10,11,12,13],
  [0,1,4,3,2,6,5,7,8,10,9,13,12,11],
  [0,1,5,3,6,2,4,7,12,9,10,13,8,11],
  [0,1,6,3,5,4,2,7,12,10,9,11,8,13],
  [0,3,2,1,5,4,6,7,9,8,12,11,10,13],
  [0,3,4,1,6,2,5,7,10,8,12,13,9,11],
  [0,3,5,1,2,6,4,7,9,12,8,13,10,11],
  [0,3,6,1,4,5,2,7,10,12,8,11,9,13],
  [7,13,12,11,10,9,8,0,6,5,4,3,2,1],
  [7,13,10,11,12,8,9,0,6,4,5,1,2,3],
  [7,13,9,11,8,12,10,0,2,5,4,1,6,3],
  [7,13,8,11,9,10,12,0,2,4,5,3,6,1],
  [7,11,12,13,9,10,8,0,5,6,2,3,4,1],
  [7,11,10,13,8,12,9,0,4,6,2,1,5,3],
  [7,11,9,13,12,8,10,0,5,2,6,1,4,3],
  [7,11,8,13,10,9,12,0,4,2,6,3,5,1]]
def perm (g : G) (x : V) : V := (images.getD g.val []).getD x.val 0

def inv (g : G) : G := ([0,1,2,3,4,6,5,7,8,12,15,11,9,13,14,10] : List G).getD g.val 0
theorem left_inv : ∀ (g : G) (x : V), perm (inv g) (perm g x)=x := by decide +kernel
theorem right_inv : ∀ (g : G) (x : V), perm g (perm (inv g) x)=x := by decide +kernel
theorem perm_injective (g : G) : Function.Injective (perm g) := Function.LeftInverse.injective (left_inv g)
theorem preserves_adj : ∀ (g : G) (x y : V), adj (perm g x) (perm g y)=adj x y := by decide +kernel
theorem fixes_flag (g : G) : (perm g 0=0 ∧ perm g 7=7) ∨ (perm g 0=7 ∧ perm g 7=0) := by
  revert g; decide +kernel
theorem distinct_rows : ∀ (g h : G), (∀ x : V, perm g x=perm h x) → g=h := by decide +kernel

def words : List (List G) := [
  [],
  [1],
  [8,1,8,1,8,1,8],
  [1,8,1,8,1,8,1,8],
  [8,1,8],
  [8,1,8,1],
  [1,8,1,8],
  [1,8,1,8,1],
  [8],
  [1,8],
  [8,1,8,1,8,1],
  [1,8,1,8,1,8,1],
  [8,1],
  [8,1,8,1,8],
  [1,8,1],
  [1,8,1,8,1,8]]
theorem two_generators : ∀ (g : G), let w := words.getD g.val [];
    (∀ v ∈ w, v=1 ∨ v=8) ∧ ∀ x : V, w.foldl (fun i k => perm k i) x=perm g x := by decide +kernel

-- Map the ordered flags in the receipt to undirected graph edges.
set_option maxHeartbeats 2000000 in
theorem realized : ∀ a b : V, adj a b=true ↔ ∃ p l : Fin 7, incident p l ∧
    samePair a b (Fin.castAdd 7 p) (Fin.natAdd 7 l) := by decide +kernel

theorem graph_spec (x : V → Bool) : ReceiptF x ↔ ∃ a b : V, adj a b=true ∧ x a=true ∧ x b=true := by
  constructor
  · rintro ⟨p,l,e,px,lx⟩
    exact ⟨_,_,(realized _ _).mpr ⟨p,l,e,Or.inl ⟨rfl,rfl⟩⟩,px,lx⟩
  · rintro ⟨a,b,e,ax,bx⟩
    obtain ⟨p,l,e2,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (realized a b).mp e
    · exact ⟨p,l,e2,ax,bx⟩
    · exact ⟨p,l,e2,bx,ax⟩

theorem keeps_incidence (g : G) (x : V → Bool) : ReceiptF (x ∘ perm g) ↔ ReceiptF x := by
  rw [graph_spec,graph_spec]
  constructor
  · rintro ⟨a,b,e,u,v⟩
    exact ⟨perm g a,perm g b,(preserves_adj g a b).trans e,u,v⟩
  · rintro ⟨a,b,e,u,v⟩
    refine ⟨perm (inv g) a,perm (inv g) b,(preserves_adj _ a b).trans e,?_,?_⟩ <;>
      simpa only [Function.comp_apply,right_inv] using ‹_›

def rep (i : R) : V × V := ([(0,1),(0,2),(0,7),(0,8),(0,11),(1,2),(1,3),(1,8),(1,9),(1,11),(2,4),(2,6),(2,8),(2,10)] : List (V × V)).getD i.val (0,0)
def counts : List Nat := [4,8,1,8,4,16,2,8,8,4,8,4,8,8]
-- Certificate for each ordered input pair: its representative index and
-- a group element taking the pair there. The diagonal entries are unused.
def witnesses : List (List (R × G)) := [
  [(0,0),(0,0),(1,0),(0,4),(1,1),(1,2),(1,3),(2,0),(3,0),(3,4),(3,6),(4,0),(3,2),(4,1)],
  [(0,0),(0,0),(5,0),(6,0),(5,1),(5,2),(5,3),(4,12),(7,0),(8,0),(8,1),(9,0),(7,2),(9,1)],
  [(1,0),(5,0),(0,0),(5,4),(10,0),(10,4),(11,0),(3,11),(12,0),(12,4),(13,0),(8,10),(13,4),(7,11)],
  [(0,4),(6,0),(5,4),(0,0),(5,6),(5,5),(5,7),(4,8),(8,4),(7,4),(7,6),(9,4),(8,5),(9,5)],
  [(1,1),(5,1),(10,0),(5,6),(0,0),(11,1),(10,6),(3,10),(12,1),(13,1),(12,6),(7,10),(13,6),(8,11)],
  [(1,2),(5,2),(10,4),(5,5),(11,1),(0,0),(10,2),(3,9),(13,5),(12,5),(13,2),(7,9),(12,2),(8,8)],
  [(1,3),(5,3),(11,0),(5,7),(10,6),(10,2),(0,0),(3,8),(13,7),(13,3),(12,7),(8,9),(12,3),(7,8)],
  [(2,0),(4,12),(3,11),(4,8),(3,10),(3,9),(3,8),(0,0),(1,10),(1,14),(1,12),(0,9),(1,8),(0,8)],
  [(3,0),(7,0),(12,0),(8,4),(12,1),(13,5),(13,7),(1,10),(0,0),(10,11),(10,10),(5,10),(11,8),(5,11)],
  [(3,4),(8,0),(12,4),(7,4),(13,1),(12,5),(13,3),(1,14),(10,11),(0,0),(11,12),(5,14),(10,9),(5,15)],
  [(3,6),(8,1),(13,0),(7,6),(12,6),(13,2),(12,7),(1,12),(10,10),(11,12),(0,0),(5,13),(10,8),(5,12)],
  [(4,0),(9,0),(8,10),(9,4),(7,10),(7,9),(8,9),(0,9),(5,10),(5,14),(5,13),(0,0),(5,9),(6,8)],
  [(3,2),(7,2),(13,4),(8,5),(13,6),(12,2),(12,3),(1,8),(11,8),(10,9),(10,8),(5,9),(0,0),(5,8)],
  [(4,1),(9,1),(7,11),(9,5),(8,11),(8,8),(7,8),(0,8),(5,11),(5,15),(5,12),(6,8),(5,8),(0,0)]]
def witness (a b : V) : R × G := (witnesses.getD a.val []).getD b.val (0,0)

theorem cover_data : ∀ a b : V, a≠b → let c := witness a b
    samePair (perm c.2 a) (perm c.2 b) (rep c.1).1 (rep c.1).2 := by decide +kernel

theorem cover (a b : V) (ne : a≠b) : ∃ (g : G) (i : R), samePair (perm g a) (perm g b) (rep i).1 (rep i).2 :=
  ⟨(witness a b).2,(witness a b).1,cover_data a b ne⟩

theorem separated : ∀ (i j : R) (g : G),
    samePair (perm g (rep i).1) (perm g (rep i).2) (rep j).1 (rep j).2 → i=j := by decide +kernel

def pairs : List (V × V) := (List.finRange 14).flatMap fun a =>
  ((List.finRange 14).filter fun b => decide (a<b)).map fun b => (a,b)

theorem orbit_counts : ∀ i : R, pairs.countP (fun ab => decide ((witness ab.1 ab.2).1=i))=counts.getD i.val 0 := by decide +kernel
theorem pair_count : pairs.length=91 := by decide +kernel

end FanoFlag

#print axioms FanoFlag.cover
#print axioms FanoFlag.keeps_incidence
