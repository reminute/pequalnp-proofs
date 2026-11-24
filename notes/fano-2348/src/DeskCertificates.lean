import FlagCertificates

namespace Fano2348

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_1490 FanoCert

def spec (C : Circuit) := ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
  ∃ p l : Fin 7, (p=l ∨ p=l+1 ∨ p=l+3) ∧ x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true

def anchor (s : Bool) : Fin 14 := if s=true then 0 else 7
def direction (s : Bool) : ℕ := if s=true then 7 else 0
def single (i : Fin 14) := List.ofFn (fun v : Fin 14 => decide (v=i))

def trace (C : Circuit) := ∀ s : Bool, ∃ d : ℕ → Bool,
  let xs := C.wires (single (anchor s))
  (∀ i < 14, d i = decide (i=direction s)) ∧
  (∀ j < C.size, let g := gateAt C j
    let a := opnd C j 0; let b := opnd C j 1
    (g.op=.and → d (14+j) = ((xs.getD a false && d b) || (d a && xs.getD b false))) ∧
    (g.op=.or → d (14+j) = (d a || d b))) ∧ d C.output=false

theorem lookup {C : Circuit} {j : ℕ} {g : Gate} (found : C.gates[j]? = some g) :
    j < C.gates.length ∧ gateAt C j = g := by
  constructor
  · by_contra! bad
    simp [List.getElem?_eq_none bad] at found
  · simp [gateAt,List.getD_eq_getElem?_getD,found]

theorem normal {C : Circuit} (ao : IsAO2 14 C) : ∀ j g, C.gates[j]? = some g →
    (g.op=.and ∨ g.op=.or) ∧ ∃ a b : ℕ, g.inputs=[a,b] ∧ a<14+j ∧ b<14+j := by
  intro j g found
  obtain ⟨valid,same⟩ := lookup found
  have mem : g ∈ C.gates := same ▸ gateAt_mem valid
  refine ⟨ao.1 g mem,?_⟩
  obtain ⟨a,b,inputs⟩ := List.length_eq_two.mp (ao.2.2 g mem)
  exact ⟨a,b,inputs,ao.2.1 j valid a (by simp [same,inputs]),ao.2.1 j valid b (by simp [same,inputs])⟩

theorem singleton_raw (C : Circuit) (p i : Fin 14) : val C (single p) i.val = decide (i=p) := by
  unfold single
  rw [val_input (List.length_ofFn (f := fun v : Fin 14 => decide (v=p))) i.isLt]
  rw [List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]

theorem singleton_off {C : Circuit} (correct : spec C) (s : Fin 14) : val C (single s) C.output=false := by
  change C.eval (single s) = false
  cases yes : C.eval (single s) with
  | false => rfl
  | true =>
    obtain ⟨u,t,_,hu,ht⟩ := (correct (fun v => decide (v=s))).mp yes
    have bad := (of_decide_eq_true hu).trans (of_decide_eq_true ht).symm
    have disjoint : ∀ a b : Fin 7, Fin.castAdd 7 a ≠ Fin.natAdd 7 b := by decide
    exact (disjoint u t bad).elim

theorem pair_on {C : Circuit} (correct : spec C) :
    val C (List.ofFn (fun v : Fin 14 => decide (v=0 ∨ v=7))) C.output=true :=
  (correct _).mpr ⟨0,0,Or.inl rfl,by decide,by decide⟩

theorem run_of_trace {C : Circuit} (tr : trace C) (s : Bool) :
    ∃ d : ℕ → Bool, LinearRun 14 C (val C (single (anchor s))) d ∧
      (∀ i < 14, d i = decide (i=direction s)) ∧ d C.output=false := by
  obtain ⟨d,raw,gates,off⟩ := tr s
  refine ⟨d,of_derivative (List.length_ofFn (f := fun v : Fin 14 => decide (v=anchor s))) d ?_,raw,off⟩
  intro j g a b found ins
  obtain ⟨valid,same⟩ := lookup found
  have left : opnd C j 0 = a := by simp [opnd,same,ins]
  have right : opnd C j 1 = b := by simp [opnd,same,ins]
  simpa only [same,left,right,val,single] using gates j valid

theorem all_certs_heavy {C : Circuit} (correct : spec C) (tr : trace C)
    {P L d : ℕ} (c : Cert 14 C 0 7 C.output P L d) : 2≤P ∧ 2≤L := by
  obtain ⟨dl,xy,rl,ol⟩ := run_of_trace tr true
  obtain ⟨dp,yx,rp,op⟩ := run_of_trace tr false
  exact multiplicity c xy yx
    (by simpa [anchor] using singleton_raw C 0 0) (by simpa [anchor] using singleton_raw C 7 7)
    (by simpa [direction] using rp 0 (by decide)) (by simpa [direction] using rl 7 (by decide))
    (singleton_off correct _) (singleton_off correct _) op ol

theorem active_deep {C : Circuit} (ao : IsAO2 14 C) (correct : spec C) (tr : trace C) :
    ∃ P L d, Cert 14 C 0 7 C.output P L d ∧ 2≤P ∧ 2≤L ∧ 2≤d := by
  obtain ⟨P,L,d,c⟩ := cert_of_true C 0 7 (normal ao) C.output (pair_on correct)
  obtain ⟨a,b⟩ := all_certs_heavy correct tr c
  refine ⟨P,L,d,c,a,b,?_⟩
  by_contra! shallow
  have h := (leaves_le c).trans (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : d ≤ 1))
  norm_num at h
  omega

end Fano2348

#print axioms Fano2348.all_certs_heavy
#print axioms Fano2348.active_deep
