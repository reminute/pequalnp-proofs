import ColumnMasks
import GraphTransfer
import Mathlib

namespace Rect4123.SampleLift

open PEqualNP.MetaComplexity GraphTransfer ColumnMasks GirthEdgeNegatives

abbrev Input (n : ℕ) := Fin n → Bool

def row {n : ℕ} (a b : Fin n) : Input n := fun i => decide (i=a ∨ i=b)

def raiseRow {n : ℕ} (a b : Fin n) : Option (Fin n) → Input n
  | none => row a b
  | some v => Function.update (row a b) v true

noncomputable def column {n : ℕ} (H : SimpleGraph (Fin n)) (c d : Fin n) : Input n := by
  classical
  exact fun i => decide (blocked H c d i)

private theorem col_true {n : ℕ} (H : SimpleGraph (Fin n)) (c d i : Fin n) :
    column H c d i = true ↔ blocked H c d i := by classical simp [column]

noncomputable def mark {n : ℕ} (H : SimpleGraph (Fin n)) (D : Finset (Fin n)) (c d : Fin n) :
    Option (Fin n) := by
  classical
  exact if h : ∃ i, i ∈ D ∧ blocked H c d i then some h.choose else none

private theorem selected {n : ℕ} (H : SimpleGraph (Fin n)) (D : Finset (Fin n))
    (sep : Separated H D) {c d i : Fin n} (shape : c=d ∨ H.Adj c d) :
    mark H D c d = some i ↔ i ∈ D ∧ blocked H c d i := by
  classical
  unfold mark
  split_ifs with h
  · rw [Option.some.injEq]
    constructor
    · rintro rfl
      exact h.choose_spec
    · intro hit
      exact (Finset.card_le_one.mp (card_mask_le_one sep shape)) _
        (mem_masked.mpr h.choose_spec) _ (mem_masked.mpr hit)
  · exact ⟨fun e => by contradiction,fun hi => (h ⟨i,hi⟩).elim⟩

private noncomputable def project {n : ℕ} (F : Finset (Fin n)) :
    Option (Fin n) → Option ↥F
  | none => none
  | some v => if h : v ∈ F then some ⟨v,h⟩ else none

private theorem pad {n m : ℕ} (H : SimpleGraph (Fin n)) (fallback : Fin n) {J : Type}
    [Fintype J] (R S : J → Fin n → Fin n → Prop) (lab : J → Fin n)
    (h : ∀ a b c d, H.Adj a b → c=d ∨ H.Adj c d →
      (∃! j, R j a b ∧ S j c d) ∧ ∀ j, R j a b → S j c d →
        (lab j=a ∨ lab j=b) ∧ ¬blocked H c d (lab j))
    (bound : Fintype.card J ≤ m) : Rectangles H m := by
  classical
  let e := (Fintype.equivFin J).toEmbedding.trans (Fin.castLEEmb bound)
  let L (i : Fin m) := if h : ∃ s, e s=i then lab h.choose else fallback
  refine ⟨fun i a b => ∃ s, e s=i ∧ R s a b, fun i c d => ∃ s, e s=i ∧ S s c d,L,?_⟩
  intro a b c d edge shape
  obtain ⟨⟨j,⟨r,s⟩,one⟩,legal⟩ := h a b c d edge shape
  constructor
  · refine ⟨e j,⟨⟨j,rfl,r⟩,⟨j,rfl,s⟩⟩,?_⟩
    rintro _ ⟨⟨l,rfl,r'⟩,⟨t,eq,s'⟩⟩
    cases e.injective eq
    exact congrArg e (one l ⟨r',s'⟩)
  · rintro _ ⟨l,rfl,r'⟩ ⟨t,eq,s'⟩
    cases e.injective eq
    have hit : ∃ u, e u=e l := ⟨l,rfl⟩
    simpa only [L,dite_eq_left hit,e.injective hit.choose_spec,blocked] using legal l r' s'

abbrev SignedTests {n k : ℕ} (H : SimpleGraph (Fin n)) (D : Finset (Fin n))
    (A B : Fin k → Input n → Bool) (pos : Fin k → ℕ) (sign : Fin k → Bool) : Prop :=
  ∀ a b c d, H.Adj a b → c=d ∨ H.Adj c d →
    let x := raiseRow a b (mark H D c d)
    let y := column H c d
    (∃! j, A j x = true ∧ B j y = true) ∧
    ∀ j, A j x = true → B j y = true →
       ∃ i : Fin n, pos j=i.val ∧ x i=sign j ∧ y i≠sign j

/-- The column only tests a singleton or an edge. Among separated negative
    coordinates it blocks at most one. The marked coordinate is raised in the
    accepting row; each positive rectangle duplicates only its charged cases. -/
theorem of_samples {n k m : ℕ} (H : SimpleGraph (Fin n)) (fallback : Fin n)
    (A B : Fin k → Input n → Bool) (pos : Fin k → ℕ) (sign : Fin k → Bool)
    (D : Finset (Fin n)) (sep : Separated H D) (tests : SignedTests H D A B pos sign)
    (neg : ∀ j, sign j=false → ∃ v ∈ D, pos j=v.val)
    (F : Fin k → Finset (Fin n))
    (stable : ∀ j, sign j=true → ∀ v ∈ D, v ∉ F j → ∀ a b, H.Adj a b →
      A j (Function.update (row a b) v true) = A j (row a b))
    (budget : (∑ j : {j : Fin k // sign j = true}, (1 + (F j.val).card)) ≤ m) :
    Rectangles H m := by
  classical
  let J := (j : {j : Fin k // sign j=true}) × Option ↥(F j.val)
  let toRaw (s : J) : Option (Fin n) := s.2.map Subtype.val
  let R (s : J) (a b : Fin n) := A s.1.val (raiseRow a b (toRaw s)) = true
  let S (s : J) (c d : Fin n) := B s.1.val (column H c d) = true ∧
    s.2 = project (F s.1.val) (mark H D c d)
  let lab (s : J) : Fin n := if h : pos s.1.val<n then ⟨pos s.1.val,h⟩ else fallback
  apply pad H fallback R S lab _ (by simpa [J,Fintype.card_sigma,Nat.add_comm] using budget)
  intro a b c d edge shape
  let q := mark H D c d
  let x := raiseRow a b q
  let y := column H c d
  have member (v : Fin n) : q=some v ↔ v∈D ∧ blocked H c d v := selected H D sep shape
  have value (j : {j : Fin k // sign j = true}) :
      A j.val (raiseRow a b ((project (F j.val) q).map Subtype.val)) = A j.val x := by
    cases hv : q with
    | none => simp [x,hv,project]
    | some v =>
      by_cases inside : v ∈ F j.val
      · simp [x,hv,project,inside]
      · simpa [x,hv,project,inside,raiseRow] using
          (stable j.val j.property v ((member v).mp hv).1 inside a b edge).symm
  obtain ⟨cover,labels⟩ := tests a b c d edge shape
  obtain ⟨j,⟨hx,hy⟩,one⟩ := cover
  have positive : sign j=true := by
    cases sgn : sign j with
    | true => rfl
    | false =>
      obtain ⟨i,pi,low,high⟩ := labels j hx hy
      change x i = sign j at low
      change y i ≠ sign j at high
      obtain ⟨v,inD,pv⟩ := neg j sgn
      have eq : i=v := Fin.ext (pi.symm.trans pv)
      subst i
      have onV : y v=true := by cases e : y v <;> simp_all
      have blockedV : blocked H c d v := (col_true H c d v).mp onV
      have chosen := (member v).mpr ⟨inD,blockedV⟩
      simp [x,chosen,raiseRow,sgn] at low
  let jj : {j : Fin k // sign j=true} := ⟨j,positive⟩
  let s : J := ⟨jj,project (F j) q⟩
  have liftHit (t : J) (rr : R t a b) (ss : S t c d) : A t.1.val x=true := by
    change A t.1.val (raiseRow a b (t.2.map Subtype.val))=true at rr
    rw [ss.2] at rr
    exact (value t.1).symm.trans rr
  constructor
  · refine ⟨s,⟨(value jj).trans hx,hy,rfl⟩,?_⟩
    rintro ⟨p,b'⟩ ⟨pr,pc⟩
    have eq : p=jj := Subtype.ext (one _ ⟨liftHit _ pr pc,pc.1⟩)
    subst p
    exact congrArg (Sigma.mk jj) pc.2
  · intro t pr pc
    obtain ⟨i,pi,yes,absent⟩ := labels t.1.val (liftHit t pr pc) pc.1
    change x i = sign t.1.val at yes
    change y i ≠ sign t.1.val at absent
    rw [t.1.property] at yes absent
    have equal : lab t=i := by
      have bound : pos t.1.val<n := pi ▸ i.isLt
      exact Fin.ext (by simpa [lab,bound] using pi)
    rw [equal]
    have legal : ¬blocked H c d i := fun h => absent ((col_true H c d i).mpr h)
    refine ⟨?_,legal⟩
    cases h : q with
    | none => simpa [x,h,raiseRow,row] using yes
    | some v =>
      have ne : i≠v := fun e => legal (e ▸ ((member v).mp h).2)
      simpa [x,h,raiseRow,Function.update_of_ne ne,row] using yes

private theorem test_values {n : ℕ} (H : SimpleGraph (Fin n)) (f : Input n → Bool)
    (girth : GirthFive H) (spec : Spec H f) (D : Finset (Fin n)) :
    ∀ a b c d, H.Adj a b → c=d ∨ H.Adj c d →
      f (raiseRow a b (mark H D c d))=true ∧ f (column H c d)=false := by
  intro a b c d edge shape
  let q := mark H D c d
  let x := raiseRow a b q
  let y := column H c d
  have rowOn : f (row a b)=true := (spec _).mpr ⟨a,b,edge,by simp [row],by simp [row]⟩
  have on : f x=true := by
    cases h : q with
    | none => simpa [x,h,raiseRow] using rowOn
    | some v => simpa [x,h,raiseRow] using raise_preserves H f spec v _ rowOn
  have off : f y=false := by
    apply Bool.eq_false_iff.mpr
    intro high
    obtain ⟨i,l,il,hi,hl⟩ := (spec y).mp high
    obtain ⟨z,hz,law⟩ := Cell.cell H girth il shape
    rcases hz with rfl | rfl
    · exact law ((col_true H c d _).mp hi)
    · exact law ((col_true H c d _).mp hl)
  exact ⟨on,off⟩

theorem signed_tests {n k : ℕ} (H : SimpleGraph (Fin n)) (f : Input n → Bool)
    (girth : GirthFive H) (spec : Spec H f) (D : Finset (Fin n))
    {A B : Fin k → Input n → Bool} {pos : Fin k → ℕ} {sign : Fin k → Bool}
    (part : IsLiteralPartition n f k A B pos sign) : SignedTests H D A B pos sign := by
  intro a b c d edge shape
  obtain ⟨on,off⟩ := test_values H f girth spec D a b c d edge shape
  exact ⟨part.2.2.2 _ _ on off,fun j => part.2.2.1 j _ _⟩

theorem of_signed {n k m : ℕ} (H : SimpleGraph (Fin n)) (fallback : Fin n)
    (f : Input n → Bool) (girth : GirthFive H) (spec : Spec H f)
    (A B : Fin k → Input n → Bool) (pos : Fin k → ℕ) (sign : Fin k → Bool)
    (part : IsLiteralPartition n f k A B pos sign) (D : Finset (Fin n)) (sep : Separated H D)
    (neg : ∀ j, sign j=false → ∃ v ∈ D, pos j=v.val)
    (F : Fin k → Finset (Fin n))
    (stable : ∀ j, sign j=true → ∀ v ∈ D, v ∉ F j → ∀ a b, H.Adj a b →
      A j (Function.update (row a b) v true) = A j (row a b))
    (budget : (∑ j : {j : Fin k // sign j = true}, (1 + (F j.val).card)) ≤ m) :
    Rectangles H m :=
  of_samples H fallback A B pos sign D sep (signed_tests H f girth spec D part) neg F stable budget

/-- A different function may accept extra inputs containing two marked
    coordinates. Such inputs cannot be rejecting test columns for the original graph. -/
theorem of_extension {n k m : ℕ} (H : SimpleGraph (Fin n)) (fallback : Fin n)
    (f h : Input n → Bool) (girth : GirthFive H) (spec : Spec H f)
    (A B : Fin k → Input n → Bool) (pos : Fin k → ℕ) (sign : Fin k → Bool)
    (part : IsLiteralPartition n h k A B pos sign) (D : Finset (Fin n)) (sep : Separated H D)
    (accepting : ∀ x, f x=true → h x=true)
    (extra : ∀ x, h x=true → f x=true ∨
      ∃ u ∈ D, ∃ w ∈ D, u≠w ∧ x u=true ∧ x w=true)
    (neg : ∀ j, sign j=false → ∃ v ∈ D, pos j=v.val)
    (F : Fin k → Finset (Fin n))
    (stable : ∀ j, sign j=true → ∀ v ∈ D, v ∉ F j → ∀ a b, H.Adj a b →
      A j (Function.update (row a b) v true) = A j (row a b))
    (budget : (∑ j : {j : Fin k // sign j = true}, (1 + (F j.val).card)) ≤ m) :
    Rectangles H m := by
  apply of_samples H fallback A B pos sign D sep _ neg F stable budget
  intro a b c d edge shape
  obtain ⟨on,off⟩ := test_values H f girth spec D a b c d edge shape
  have no : h (column H c d)=false := by
    apply Bool.eq_false_iff.mpr
    intro bad
    rcases extra _ bad with hit | ⟨u,du,w,dw,neq,hu,hw⟩
    · exact Bool.noConfusion (off.symm.trans hit)
    · exact sep u du w dw neq (short_walk shape ((col_true H c d u).mp hu) ((col_true H c d w).mp hw))
  exact ⟨part.2.2.2 _ _ (accepting _ on) no,fun j => part.2.2.1 j _ _⟩

end Rect4123.SampleLift

#print axioms Rect4123.SampleLift.of_signed
#print axioms Rect4123.SampleLift.of_samples
#print axioms Rect4123.SampleLift.of_extension
