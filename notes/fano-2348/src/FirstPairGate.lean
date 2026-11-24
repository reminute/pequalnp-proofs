import DeskCertificates

namespace Fano2348

open PEqualNP.CircuitLowerBounds FanoCert

/-- Cut a selected proof tree whenever it first touches wire 14. The three
    counters track raw point leaves, raw line leaves and touches of wire 14. -/
inductive Cut (C : Circuit) : ℕ → ℕ → ℕ → ℕ → ℕ → Prop
  | point : Cut C 0 1 0 0 0
  | line : Cut C 7 0 1 0 0
  | first : Cut C 14 0 0 1 0
  | left {j a b P L Z d} (later : 0 < j) (g : C.gates[j]?=some ⟨.or,[a,b]⟩)
      (ha : a < 14+j) (hb : b < 14+j) (t : Cut C a P L Z d) : Cut C (14+j) P L Z d
  | right {j a b P L Z d} (later : 0 < j) (g : C.gates[j]?=some ⟨.or,[a,b]⟩)
      (ha : a < 14+j) (hb : b < 14+j) (t : Cut C b P L Z d) : Cut C (14+j) P L Z d
  | both {j a b P L Z d Q M W e} (later : 0 < j) (g : C.gates[j]?=some ⟨.and,[a,b]⟩)
      (ha : a < 14+j) (hb : b < 14+j) (t : Cut C a P L Z d) (u : Cut C b Q M W e) :
      Cut C (14+j) (P+Q) (L+M) (Z+W) (max d e+1)

def markedFirst (C : Circuit) : Prop := C.gates[0]?=some ⟨.or,[0,7]⟩ ∨ C.gates[0]?=some ⟨.or,[7,0]⟩

theorem expand {C : Circuit} (first : markedFirst C) {w P L Z d : ℕ} (c : Cut C w P L Z d) :
    Cert 14 C 0 7 w (P+Z) L d ∧ Cert 14 C 0 7 w P (L+Z) d := by
  induction c with
  | point => exact ⟨.point,.point⟩
  | line => exact ⟨.line,.line⟩
  | first =>
    rcases first with g | g
    · exact ⟨.left g (by decide) (by decide) .point,.right g (by decide) (by decide) .line⟩
    · exact ⟨.right g (by decide) (by decide) .point,.left g (by decide) (by decide) .line⟩
  | left _ g a b _ h => exact ⟨.left g a b h.1,.left g a b h.2⟩
  | right _ g a b _ h => exact ⟨.right g a b h.1,.right g a b h.2⟩
  | both _ g a b _ _ h k =>
    constructor
    · convert Cert.both g a b h.1 k.1 using 1
      omega
    · convert Cert.both g a b h.2 k.2 using 1
      omega

theorem cut_exists {C : Circuit} (first : markedFirst C) {w P L d : ℕ} (c : Cert 14 C 0 7 w P L d) :
    ∃ A B Z, Cut C w A B Z d ∧ A+B+Z = P+L := by
  have rawDepth {w A B e : ℕ} (h : Cert 14 C 0 7 w A B e) (raw : w < 14) : e=0 ∧ A+B=1 := by
    cases h <;> omega
  induction c with
  | point => exact ⟨1,0,0,.point,rfl⟩
  | line => exact ⟨0,1,0,.line,rfl⟩
  | @left j a b P L d g ha hb t ih =>
    by_cases z : j=0
    · subst j
      obtain ⟨rfl,h⟩ := rawDepth t (by simpa using ha)
      exact ⟨0,0,1,.first,h.symm⟩
    · obtain ⟨A,B,Z,c,h⟩ := ih
      exact ⟨A,B,Z,.left (Nat.pos_of_ne_zero z) g ha hb c,h⟩
  | @right j a b P L d g ha hb t ih =>
    by_cases z : j=0
    · subst j
      obtain ⟨rfl,h⟩ := rawDepth t (by simpa using hb)
      exact ⟨0,0,1,.first,h.symm⟩
    · obtain ⟨A,B,Z,c,h⟩ := ih
      exact ⟨A,B,Z,.right (Nat.pos_of_ne_zero z) g ha hb c,h⟩
  | @both j a b P L d Q M e g ha hb t u ih jh =>
    have pos : 0 < j := by
      by_contra! impossible
      obtain rfl : j=0 := by omega
      rcases first with eq | eq <;> simp [eq] at g
    obtain ⟨A,B,Z,c,h⟩ := ih
    obtain ⟨A',B',Z',c',h'⟩ := jh
    exact ⟨_,_,_,.both pos g ha hb c c',by omega⟩

/-- When the first OR reads precisely the marked pair, expanding every use
    toward the other endpoint shows that each endpoint must appear at least
    twice *outside* that OR. A certificate using that wire has depth ≥3. -/
theorem first_pair_obstruction {C : Circuit} (first : markedFirst C) (correct : spec C) (tr : trace C)
    {P L Z d : ℕ} (c : Cut C C.output P L Z d) : 2 ≤ P ∧ 2 ≤ L ∧ (0 < Z → 3 ≤ d) := by
  obtain ⟨towardPoint,towardLine⟩ := expand first c
  have Praw := (all_certs_heavy correct tr towardLine).1
  have Lraw := (all_certs_heavy correct tr towardPoint).2
  refine ⟨Praw,Lraw,?_⟩
  intro used
  by_contra! shallow
  have h := (leaves_le towardPoint).trans (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : d ≤ 2))
  norm_num at h
  omega

end Fano2348

#print axioms Fano2348.first_pair_obstruction
#print axioms Fano2348.cut_exists
