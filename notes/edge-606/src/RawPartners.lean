import Sensitivity
import TwinReads
import ReaderCore

namespace Edge606.RawPartners

open Finset SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Cubic1971.PartnerCertificate
open GraphDensity (edgeFunction)

variable {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

def readIds (C : Circuit) (v : Fin n) : Finset (Fin C.gates.length) :=
  univ.filter fun j => v.val ∈ (C.gates.get j).inputs

noncomputable def side (C : Circuit) (v : Fin n) (p : Fin C.gates.length → Fin n)
    (op : GateOp) : Finset (Fin n) := by
  classical exact ((readIds C v).filter fun j => (C.gates.get j).op = op).image p

theorem mem_side {C : Circuit} {v w : Fin n} {p : Fin C.gates.length → Fin n} {op : GateOp} :
    w ∈ side C v p op ↔ ∃ j ∈ readIds C v, (C.gates.get j).op = op ∧ p j = w := by
  classical
  simp [side, and_assoc]

/-- Too few distinct raw partners cannot mask all changes to v unless the
    requested absorbing values conflict or the OR partners already contain an edge. -/
theorem obstruction (girth : GirthEdgeNegatives.GirthFive G) (C : Circuit)
    (mono : Monotone2 C) (computes : circuitFun n C = edgeFunction G) (v : Fin n)
    (p : Fin C.gates.length → Fin n)
    (raw : ∀ j ∈ readIds C v, p j ≠ v ∧
      ((C.gates.get j).inputs = [v.val,(p j).val] ∨ (C.gates.get j).inputs = [(p j).val,v.val]))
    (few : ((readIds C v).image p).card < G.degree v) :
    (∃ w ∈ side C v p .or, w ∈ side C v p .and) ∨
      (∃ a ∈ side C v p .or, ∃ b ∈ side C v p .or, G.Adj a b) := by
  classical
  by_contra denied
  let P := side C v p .or
  let Z := side C v p .and
  have away : v ∉ P := by
    intro mem
    obtain ⟨j,read,_,eq⟩ := mem_side.mp mem
    exact (raw j read).1 eq
  have apart : Disjoint P Z := disjoint_left.mpr fun w hp hz => denied (Or.inl ⟨w,hp,hz⟩)
  have independent : free G P := fun a ha b hb ab => denied (Or.inr ⟨a,ha,b,hb,ab⟩)
  have covered : P ∪ Z ⊆ (readIds C v).image p := by
    intro w hw
    rcases mem_union.mp hw with hp | hz
    · obtain ⟨j,r,_,eq⟩ := mem_side.mp hp
      exact mem_image.mpr ⟨j,r,eq⟩
    · obtain ⟨j,r,_,eq⟩ := mem_side.mp hz
      exact mem_image.mpr ⟨j,r,eq⟩
  obtain ⟨S, keep, avoid, senses⟩ := Sensitivity.complete_input girth P Z away apart independent
    ((card_le_card covered).trans_lt few)
  have values := (toggle (by simp) senses.1).mp senses
  have same := TwinReads.masked_many (v := v) C (TwinReads.output_ne computes v)
    (bits S) (bits (insert v S)) (fun i ne => by simp [bits,ne]) (by
      intro j hj
      have mem : j ∈ readIds C v := mem_filter.mpr ⟨mem_univ _,hj⟩
      refine ⟨p j,(raw j mem).1,(raw j mem).2,?_⟩
      have op := (mono _ (List.get_mem _ j)).1
      change (C.gates.get j).op = GateOp.and ∨ (C.gates.get j).op = GateOp.or at op
      rcases op with h | h
      · have hz : p j ∈ Z := mem_side.mpr ⟨j,mem,h,rfl⟩
        exact Or.inl ⟨h, by simp [bits, show p j ∉ S from fun inside => disjoint_left.mp avoid inside hz]⟩
      · have hp : p j ∈ P := mem_side.mpr ⟨j,mem,h,rfl⟩
        exact Or.inr ⟨h, by simp [bits, keep hp]⟩)
  rw [computes,Sensitivity.bit_edge,Sensitivity.bit_edge,values.1,values.2] at same
  contradiction

/-- The other operand of a unique binary reader cannot be a different raw
    input when v has at least two neighbors. The other input may be read elsewhere. -/
theorem no_raw_partner (girth : GirthEdgeNegatives.GirthFive G) (C : Circuit)
    (mono : Monotone2 C) (computes : circuitFun n C = edgeFunction G)
    (v w : Fin n) (other : v ≠ w) (degree : 1 < G.degree v)
    (single : WeightedPin.readers C v ≤ 1) (j : Fin C.gates.length)
    (args : (C.gates.get j).inputs = [v.val,w.val] ∨ (C.gates.get j).inputs = [w.val,v.val]) :
    False := by
  classical
  have hj : j ∈ readIds C v := by
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    rcases args with h | h <;> rw [h] <;> simp
  have only (i : Fin C.gates.length) (h : v.val ∈ (C.gates.get i).inputs) : i = j :=
    (Finset.card_le_one.mp (show (readIds C v).card ≤ 1 from single))
      i (mem_filter.mpr ⟨mem_univ _,h⟩) j hj
  let b := decide ((C.gates.get j).op = GateOp.or)
  obtain ⟨x,y,xb,_,agree,off,on⟩ := Sensitivity.one_fixed girth degree w other b
  have eq := TwinReads.masked C other (TwinReads.output_ne computes v) x y agree (by
    intro i hi
    rw [only i hi]
    refine ⟨args,?_⟩
    have op := (mono _ (List.get_mem _ j)).1
    change (C.gates.get j).op = GateOp.and ∨ (C.gates.get j).op = GateOp.or at op
    rcases op with h | h
    · exact Or.inl ⟨h,xb.trans (by unfold b; rw [h]; simp)⟩
    · exact Or.inr ⟨h,xb.trans (by unfold b; rw [h]; simp)⟩)
  rw [computes,off,on] at eq
  contradiction

/-- At degrees at most 2k in the remaining graph class, a proper second
    operand has a computed-wire index. Invalid wire indices are allowed by the model. -/
theorem internal_index (girth : GirthEdgeNegatives.GirthFive G) (C : Circuit)
    (mono : Monotone2 C) (computes : circuitFun n C = edgeFunction G) (v : Fin n)
    (k : Nat) (positive : 0 < k) (sparse : ReaderCore.sparseReads k G C)
    (active : 0 < G.degree v) (small : G.degree v ≤ 2*k)
    (j : Fin C.gates.length) (wire : Nat) (different : wire ≠ v.val)
    (args : (C.gates.get j).inputs = [v.val,wire] ∨ (C.gates.get j).inputs = [wire,v.val]) :
    n ≤ wire := by
  have count := sparse v active
  have one : WeightedPin.readers C v ≤ 1 := by
    by_contra! many
    have double := Nat.mul_le_mul_left k (show 2 ≤ WeightedPin.readers C v by omega)
    omega
  have degree := ReaderCore.high_degree G C computes sparse v active
  by_contra! raw
  exact no_raw_partner girth C mono computes v ⟨wire,raw⟩
    (fun eq => different (congrArg Fin.val eq.symm)) (lt_of_le_of_lt positive degree) one j args

end Edge606.RawPartners

#print axioms Edge606.RawPartners.obstruction
#print axioms Edge606.RawPartners.no_raw_partner
#print axioms Edge606.RawPartners.internal_index
