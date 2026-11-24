import ReadKBridge
import FirstOrBypass
import Canonical

namespace FanoSolved

open Fano2348 PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open FanoRename FanoCanonical FanoFlag

theorem privateBoth {D : Circuit} (ao : IsAO2 14 D) (correct : spec D)
    (diff : ∀ j<D.size, opnd D j 0 ≠ opnd D j 1) (gateOr : (gateAt D 0).op=.or) :
    ∀ s : Fin 2, ∃ j : Fin D.gates.length, 0<j.val ∧
      ∀ t : Fin 2, opnd D 0 t ∈ (gateAt D j.val).inputs ↔ t=s := by
  have pos : 0<D.size := size_pos correct
  let a : Fin 14 := ⟨opnd D 0 0,first_raw ao pos 0⟩
  let b : Fin 14 := ⟨opnd D 0 1,first_raw ao pos 1⟩
  have ne : a≠b := fun h => diff 0 pos (congrArg Fin.val h)
  let g := D.gates[0]
  have found : D.gates[0]?=some g := List.getElem?_eq_getElem pos
  obtain ⟨_,u,v,ins,_,_⟩ := normal ao 0 g found
  have same := (lookup found).2
  have inputs : g.inputs = [a.val,b.val] := by simp [a,b,opnd,same,ins]
  have shaped (s : Gate) (op : s.op=.or) (args : s.inputs=[a.val,b.val]) : s=⟨.or,[a.val,b.val]⟩ := by cases s; simp_all
  have actual : D.gates[0]?=some ⟨.or,[a.val,b.val]⟩ := found.trans (congrArg some (shaped g (same ▸ gateOr) inputs))
  obtain ⟨j,k,_,jr,kr⟩ := different_private_readers ao correct a b ne (Or.inl actual)
  have witnesses (s : Fin 2) : (s=0 ∨ s=1) := by fin_cases s <;> simp
  intro s
  rcases witnesses s with rfl | rfl
  · refine ⟨⟨j,jr.2.1⟩,jr.1,?_⟩
    intro t
    rcases witnesses t with rfl | rfl
    · exact iff_of_true jr.2.2.1 rfl
    · exact iff_of_false jr.2.2.2 (by decide)
  · refine ⟨⟨k,kr.2.1⟩,kr.1,?_⟩
    intro t
    rcases witnesses t with rfl | rfl
    · exact iff_of_false kr.2.2.2 (by decide)
    · exact iff_of_true kr.2.2.1 rfl

theorem closed_one : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →     (∀ (x3 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (7 : ℕ)) ∨ x4 = x5 + (3 : Fin (7 : ℕ))) ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true) →       (∀ (x4 : Bool),           ∃ (x5 : ℕ → Bool),             have x6 : List Bool := x1.wires (List.ofFn fun (x6 : Fin (14 : ℕ)) => Decidable.decide (x6 = if x4 = Bool.true then (0 : Fin (14 : ℕ)) else (7 : Fin (14 : ℕ))));             (∀ x7 < (14 : ℕ), x5 x7 = Decidable.decide (x7 = if x4 = Bool.true then (7 : ℕ) else (0 : ℕ))) ∧               (∀ x7 < x1.size,                   have x9 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x1 x7;                   have x10 : ℕ := PEqualNP.TopForm.opnd x1 x7 (0 : Fin (2 : ℕ));                   have x11 : ℕ := PEqualNP.TopForm.opnd x1 x7 (1 : Fin (2 : ℕ));                   (x9.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((14 : ℕ) + x7) = (x6.getD x10 Bool.false && x5 x11 || x5 x10 && x6.getD x11 Bool.false)) ∧ (x9.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((14 : ℕ) + x7) = (x5 x10 || x5 x11))) ∧                 x5 x1.output = Bool.false) →         ((0 : ℕ), (7 : ℕ)) ∈ PEqualNP.ReadK.doubleReread x1 (14 : ℕ) (fun (x5 : ℕ) => Decidable.decide ((7 : ℕ) ≤ x5)) [((0 : ℕ), (7 : ℕ))] := by
  intro C ao correct tr
  exact (trace_iff_double_reread ao correct).mp tr

theorem closed_two : have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => x1.size ≤ (27 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧ (∀ x2 < x1.size, PEqualNP.TopForm.opnd x1 x2 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x2 (1 : Fin (2 : ℕ))) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧ ((0 : ℕ), (7 : ℕ)) ∈ PEqualNP.ReadK.doubleReread x1 (14 : ℕ) (fun (x2 : ℕ) => Decidable.decide ((7 : ℕ) ≤ x2)) [((0 : ℕ), (7 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x1 x2 →     ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit),       x1 x4 ∧         have x5 : ℕ := PEqualNP.TopForm.opnd x4 (0 : ℕ) (0 : Fin (2 : ℕ));         have x6 : ℕ := PEqualNP.TopForm.opnd x4 (0 : ℕ) (1 : Fin (2 : ℕ));         Nat.testBit (365118556550 : ℕ) ((14 : ℕ) * Min.min x5 x6 + Max.max x5 x6) = Bool.true ∧ ∀ (x7 : Fin (2 : ℕ)), ∃ (x8 : Fin x4.gates.length), (0 : ℕ) < ↑x8 ∧ ∀ (x9 : Fin (2 : ℕ)), PEqualNP.TopForm.opnd x4 (0 : ℕ) x9 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 ↑x8).inputs ↔ x9 = x7 := by
  intro W C h
  obtain ⟨cap,ao,diff,first,correct,flag⟩ := h
  have tr := (trace_iff_double_reread ao correct).mpr flag
  have w : Witness C := ⟨cap,ao,diff,first,correct,tr true,tr false⟩
  obtain ⟨g,i,wd,atRep⟩ := canonicalize w
  let D := acted g C
  change First D i at atRep
  obtain ⟨capD,aoD,diffD,firstD,correctD,forw,back⟩ := wd
  have trD : trace D := by intro side; cases side; exact back; exact forw
  have flagged := (trace_iff_double_reread aoD correctD).mp trD
  have bits : ∀ r : R, (365118556550 : ℕ).testBit (14*min (rep r).1.val (rep r).2.val + max (rep r).1.val (rep r).2.val)=true := by decide +kernel
  refine ⟨D,⟨capD,aoD,diffD,firstD,correctD,flagged⟩,?_,privateBoth aoD correctD diffD firstD⟩
  rcases atRep with ⟨u,v⟩ | ⟨u,v⟩
  · rw [u,v]
    exact bits i
  · rw [u,v,min_comm,max_comm]
    exact bits i

end FanoSolved

#print axioms FanoSolved.closed_one
#print axioms FanoSolved.closed_two
