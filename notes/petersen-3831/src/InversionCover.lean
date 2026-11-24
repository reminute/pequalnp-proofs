import SignedPath
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Enumerative.InclusionExclusion

namespace Petersen3831.InversionCover

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1490 Petersen3831.RawPartner
open scoped BigOperators

def rows : Finset Nat :=
  {2,10,16,18,20,32,34,36,40,42,48,50,52,80,84,96,100,104,112,116,130,
   138,144,146,208,258,272,274,276,386,400,402}

private theorem row_cert : rows.card=32 ∧ ∀ m ∈ rows, m<512 ∧ sensitive m := by decide

def gates (C : Circuit) (k : Nat) : Finset Nat :=
  (Finset.range C.gates.length).filter (fun j => k < j ∧ 9+j ≤ C.output ∧
    (gateAt C j).op.eval [true] = false)

def covered (C : Circuit) (j : Nat) : Finset Nat :=
  rows.filter fun m => val C (List.ofFn (row m false)) (9+j) = true ∧
    val C (List.ofFn (row m true)) (9+j) = false

theorem coverage (C : Circuit) (fan : FanInTwo C) {k a : Nat} (uq : unique C)
    (hk : k < C.gates.length) (args : (gateAt C k).inputs = [0,a])
    (op : (gateAt C k).op = .and ∨ (gateAt C k).op = .or)
    (correct : ∀ x : Input, circuitFun 9 C (RawPartner.flip x) = graph x) :
    32 ≤ ∑ j ∈ gates C k, (covered C j).card := by
  have sub : rows ⊆ (gates C k).biUnion (covered C) := by
    intro m hm
    obtain ⟨small, sens⟩ := row_cert.2 m hm
    obtain ⟨j, valid, later, live, neg, up, down⟩ :=
      SignedPath.post_reader_not C fan uq hk args op correct ⟨m,small⟩ sens
    exact Finset.mem_biUnion.mpr ⟨j,
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr valid,later,live,by simp [neg,GateOp.eval]⟩,
      Finset.mem_filter.mpr ⟨hm,up,down⟩⟩
  rw [←row_cert.1]
  exact (Finset.card_le_card sub).trans Finset.card_biUnion_le

theorem three_rows (C : Circuit) (fan : FanInTwo C) (size : C.size ≤ 14) {k a : Nat}
    (uq : unique C) (hk : k < C.gates.length) (args : (gateAt C k).inputs = [0,a])
    (op : (gateAt C k).op = .and ∨ (gateAt C k).op = .or)
    (correct : ∀ x : Input, circuitFun 9 C (RawPartner.flip x) = graph x) :
    ∃ j ∈ gates C k, (gateAt C j).op = .not ∧ 3 ≤ (covered C j).card := by
  have sum := coverage C fan uq hk args op correct
  have small : (gates C k).card ≤ 14 := by
    unfold gates
    calc
      _ ≤ (Finset.range C.gates.length).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = C.gates.length := Finset.card_range _
      _ ≤ 14 := size
  by_contra! no
  have limited (j) (hj : j ∈ gates C k) : (covered C j).card ≤ 2 := by
    obtain ⟨jr, _, _, inv⟩ := Finset.mem_filter.mp hj
    have valid := Finset.mem_range.mp jr
    have ops := (fan (gateAt C j) (gateAt_mem valid)).1
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops
    rcases ops with h | h | h
    · simp [h,GateOp.eval] at inv
    · simp [h,GateOp.eval] at inv
    · have := no j hj h
      omega
  have lim := Finset.sum_le_sum limited
  simp only [Finset.sum_const, smul_eq_mul] at lim
  omega

end Petersen3831.InversionCover

#print axioms Petersen3831.InversionCover.three_rows
