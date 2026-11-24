import DeskCertificates
import LinearScanBase

namespace Fano2348

open FanoCert PEqualNP.ReadK PEqualNP.TopForm PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_1490 PEqualNP.Outside.L_meta_2462

def side (s : Bool) (i : ℕ) := if s then decide (7 ≤ i) else !(decide (7 ≤ i))
def pairBits := (List.range 14).map (fun i => i == 0 || i == 7)
def init (s : Bool) := pairBits.zipIdx.map fun (b,i) => if side s i then (false,b) else (b,false)
def part (C : Circuit) (s : Bool) (w : ℕ) := (linearParts C (side s) pairBits).getD w (false,false)

theorem initLen : ∀ s : Bool, (init s).length = 14 := by decide
theorem initBase : ∀ s : Bool, (init s).map (·.1) = single (anchor s) := by decide
theorem initDirection : ∀ (s : Bool) (i : Fin 14), ((init s).getD i.val (false,false)).2 =
    decide (i.val=direction s) := by decide

theorem part_base {C : Circuit} (ao : IsAO2 14 C) (s : Bool) (w : ℕ) :
    (part C s w).1 = val C (single (anchor s)) w := by
  change ((scan linStep C.gates (init s)).getD w (false,false)).1 =
    (scan boolStep C.gates (single (anchor s))).getD w false
  rw [← getD_map_fst,scan_lin_fst C.gates ao.1,initBase]

theorem part_raw (C : Circuit) (s : Bool) (i : ℕ) (hi : i < 14) :
    (part C s i).2 = decide (i=direction s) := by
  change ((scan linStep C.gates (init s)).getD i (false,false)).2 = _
  rw [scan_prefix _ _ _ _ _ (by simpa [initLen] using hi)]
  exact initDirection s ⟨i,hi⟩

theorem part_gate {C : Circuit} (ao : IsAO2 14 C) (s : Bool) {j : ℕ} (valid : j<C.size) :
    part C s (14+j) = linStep (linearParts C (side s) pairBits) (gateAt C j) := by
  change (scan linStep C.gates (init s)).getD (14+j) (false,false) = linStep (scan linStep C.gates (init s)) _
  rw [gateAt_eq_getElem valid]
  conv_lhs => rw [← initLen s]
  apply scan_gate
  intro a b agree
  have eq : C.gates[j].inputs.map (fun i => a.getD i (false,false)) =
      C.gates[j].inputs.map (fun i => b.getD i (false,false)) := List.map_congr_left fun i mem =>
    agree i (by rw [initLen]; exact ao.2.1 j valid i (by rwa [gateAt_eq_getElem valid]))
  simp only [linStep,eq]

theorem packed_rules {C : Circuit} (ao : IsAO2 14 C) (s : Bool) (j : ℕ) (valid : j<C.size) :
    let base := val C (single (anchor s))
    let a := opnd C j 0; let b := opnd C j 1
    ((gateAt C j).op = .and → (part C s (14+j)).2 = ((base a && (part C s b).2) || ((part C s a).2 && base b))) ∧
    ((gateAt C j).op = .or → (part C s (14+j)).2 = ((part C s a).2 || (part C s b).2)) := by
  dsimp only
  rw [part_gate ao s valid]
  obtain ⟨_,inputs,_,_⟩ := ao2_gate_props ao valid
  constructor <;> intro op <;> simp only [linStep,op,inputs,List.map_cons,List.map_nil,List.foldl_cons,
    List.foldl_nil,List.any_cons,List.any_nil,Bool.true_and,Bool.false_and,Bool.or_false]
  rw [← part_base ao s,← part_base ao s]
  rfl
  rfl

theorem actual_run {C : Circuit} (ao : IsAO2 14 C) (s : Bool) :
    LinearRun 14 C (val C (single (anchor s))) (fun w => (part C s w).2) := by
  apply of_derivative (n := 14) (show (single (anchor s)).length = 14 from List.length_ofFn) _
  intro j g a b found ins
  obtain ⟨valid,same⟩ := lookup found
  have left : opnd C j 0 = a := by simp [opnd,same,ins]
  have right : opnd C j 1 = b := by simp [opnd,same,ins]
  simpa only [same,left,right] using packed_rules ao s j valid

theorem output_valid {C : Circuit} (correct : spec C) : C.output < 14+C.gates.length := by
  by_contra! bad
  have off := val_ge (C := C) (x := List.ofFn (fun v : Fin 14 => decide (v=0 ∨ v=7))) List.length_ofFn bad
  exact Bool.noConfusion (off.symm.trans (pair_on correct))

theorem part_one {C : Circuit} (ao : IsAO2 14 C) (correct : spec C) (s : Bool) :
    (part C s C.output).2 = true ↔ ∃ P d,
      Cert 14 C (anchor s) (anchor (!s)) C.output P 1 d := by
  apply derivative_iff C (anchor s) (anchor (!s)) (actual_run ao s) (singleton_raw C (anchor s))
  · intro i
    rw [part_raw C s i.val i.isLt]
    have tab : ∀ (t : Bool) (v : Fin 14), decide (v.val=direction t) = decide (v=anchor (!t)) := by decide
    exact tab s i
  · exact normal ao
  · exact output_valid correct

theorem trace_iff_heavy {C : Circuit} (ao : IsAO2 14 C) (correct : spec C) :
    trace C ↔ ∀ P L d, Cert 14 C 0 7 C.output P L d → 2≤P ∧ 2≤L := by
  constructor
  · exact fun tr _ _ _ c => all_certs_heavy correct tr c
  · intro heavy s
    refine ⟨fun w => (part C s w).2,part_raw C s,fun j v => packed_rules ao s j v,?_⟩
    cases h : (part C s C.output).2 with
    | false => exact h
    | true =>
      obtain ⟨P,d,c⟩ := (part_one ao correct s).mp h
      cases s
      · have bad := (heavy _ _ _ (flip c)).1
        omega
      · have bad := (heavy _ _ _ c).2
        omega

theorem trace_iff_double_reread {C : Circuit} (ao : IsAO2 14 C) (correct : spec C) :
    trace C ↔ (0,7) ∈ doubleReread C 14 (fun i => decide (7 ≤ i)) [(0,7)] := by
  have read : ((0,7) ∈ doubleReread C 14 (fun i => decide (7 ≤ i)) [(0,7)]) ↔
      (part C true C.output).2=false ∧ (part C false C.output).2=false := by
    simp [doubleReread,lineSingle,part,pairBits]
    rfl
  rw [read]
  constructor
  · intro tr
    have heavy := (trace_iff_heavy ao correct).mp tr
    constructor <;> apply Bool.eq_false_iff.mpr <;> intro on
    · obtain ⟨P,d,c⟩ := (part_one ao correct true).mp on
      have bad := (heavy _ _ _ c).2
      omega
    · obtain ⟨P,d,c⟩ := (part_one ao correct false).mp on
      have bad := (heavy _ _ _ (flip c)).1
      omega
  · intro off s
    exact ⟨fun w => (part C s w).2,part_raw C s,fun j v => packed_rules ao s j v,by cases s; exact off.2; exact off.1⟩

end Fano2348

#print axioms Fano2348.trace_iff_heavy
#print axioms Fano2348.trace_iff_double_reread
