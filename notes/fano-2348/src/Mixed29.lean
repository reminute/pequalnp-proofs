import FlagTransport
import Mathlib.Tactic

namespace FanoMixed29

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm FanoFlag FanoRename

set_option maxRecDepth 32000
set_option maxHeartbeats 4000000

deriving instance DecidableEq for GateOp

def C : Circuit := ⟨[
  ⟨.or,[0,13]⟩,
  ⟨.or,[7,11]⟩,
  ⟨.or,[13,15]⟩,
  ⟨.and,[0,16]⟩,
  ⟨.and,[14,16]⟩,
  ⟨.or,[2,17]⟩,
  ⟨.or,[9,18]⟩,
  ⟨.or,[8,20]⟩,
  ⟨.and,[19,21]⟩,
  ⟨.or,[8,7]⟩,
  ⟨.or,[23,12]⟩,
  ⟨.and,[1,24]⟩,
  ⟨.or,[22,25]⟩,
  ⟨.or,[10,9]⟩,
  ⟨.or,[27,7]⟩,
  ⟨.and,[3,28]⟩,
  ⟨.or,[26,29]⟩,
  ⟨.or,[11,10]⟩,
  ⟨.or,[31,8]⟩,
  ⟨.and,[4,32]⟩,
  ⟨.or,[30,33]⟩,
  ⟨.or,[12,11]⟩,
  ⟨.or,[35,9]⟩,
  ⟨.and,[5,36]⟩,
  ⟨.or,[34,37]⟩,
  ⟨.or,[13,12]⟩,
  ⟨.or,[39,10]⟩,
  ⟨.and,[6,40]⟩,
  ⟨.or,[38,41]⟩],42⟩

private def rows : List (Fin 7 × Fin 7) := [(0,0),(0,6),(0,4),(1,1),(1,0),(1,5),(2,2),(2,1),(2,6),(3,3),(3,2),(3,0),(4,4),(4,3),(4,1),(5,5),(5,4),(5,2),(6,6),(6,5),(6,3)]
private theorem rows_complete : ∀ p l : Fin 7, (p,l) ∈ rows ↔ incident p l := by decide +kernel

private def expression (x : V → Bool) : Bool :=
  let v14 := x 0 || x 13
  let v15 := x 7 || x 11
  let v16 := x 13 || v15
  let v17 := x 0 && v16
  let v18 := v14 && v16
  let v19 := x 2 || v17
  let v20 := x 9 || v18
  let v21 := x 8 || v20
  let v22 := v19 && v21
  let v23 := x 8 || x 7
  let v24 := v23 || x 12
  let v25 := x 1 && v24
  let v26 := v22 || v25
  let v27 := x 10 || x 9
  let v28 := v27 || x 7
  let v29 := x 3 && v28
  let v30 := v26 || v29
  let v31 := x 11 || x 10
  let v32 := v31 || x 8
  let v33 := x 4 && v32
  let v34 := v30 || v33
  let v35 := x 12 || x 11
  let v36 := v35 || x 9
  let v37 := x 5 && v36
  let v38 := v34 || v37
  let v39 := x 13 || x 12
  let v40 := v39 || x 10
  let v41 := x 6 && v40
  let v42 := v38 || v41
  v42

private theorem run_expr (x : V → Bool) : C.eval (List.ofFn x) = expression x := by
  have inputs : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13] := rfl
  rw [inputs]
  simp [Circuit.eval,Circuit.wires,C,GateOp.eval,expression,List.getD_eq_getElem?_getD]

private theorem algebra (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 : Bool) :
    (((((((z2 || (z0 && (z13 || (z7 || z11)))) && (z8 || (z9 || ((z0 || z13) && (z13 || (z7 || z11)))))) || (z1 && ((z8 || z7) || z12))) || (z3 && ((z10 || z9) || z7))) || (z4 && ((z11 || z10) || z8))) || (z5 && ((z12 || z11) || z9))) || (z6 && ((z13 || z12) || z10))) =
    ((z0 && z7) || ((z0 && z13) || ((z0 && z11) || ((z1 && z8) || ((z1 && z7) || ((z1 && z12) || ((z2 && z9) || ((z2 && z8) || ((z2 && z13) || ((z3 && z10) || ((z3 && z9) || ((z3 && z7) || ((z4 && z11) || ((z4 && z10) || ((z4 && z8) || ((z5 && z12) || ((z5 && z11) || ((z5 && z9) || ((z6 && z13) || ((z6 && z12) || ((z6 && z10) || false))))))))))))))))))))) := by
  revert z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13
  decide +kernel

private theorem correct (x : V → Bool) : C.eval (List.ofFn x)=true ↔ ReceiptF x := by
  let sat (r : Fin 7 × Fin 7) := x (Fin.castAdd 7 r.1) && x (Fin.natAdd 7 r.2)
  have truth : rows.any sat=true ↔ ReceiptF x := by
    rw [List.any_eq_true]
    constructor
    · rintro ⟨⟨p,l⟩,mem,bits⟩
      exact ⟨p,l,(rows_complete p l).mp mem,(Bool.and_eq_true_iff.mp bits).1,(Bool.and_eq_true_iff.mp bits).2⟩
    · rintro ⟨p,l,edge,pt,line⟩
      exact ⟨(p,l),(rows_complete p l).mpr edge,Bool.and_eq_true_iff.mpr ⟨pt,line⟩⟩
  rw [←truth,run_expr]
  have eq : expression x = rows.any sat := by
    change expression x = ((x 0 && x 7) || ((x 0 && x 13) || ((x 0 && x 11) || ((x 1 && x 8) || ((x 1 && x 7) || ((x 1 && x 12) || ((x 2 && x 9) || ((x 2 && x 8) || ((x 2 && x 13) || ((x 3 && x 10) || ((x 3 && x 9) || ((x 3 && x 7) || ((x 4 && x 11) || ((x 4 && x 10) || ((x 4 && x 8) || ((x 5 && x 12) || ((x 5 && x 11) || ((x 5 && x 9) || ((x 6 && x 13) || ((x 6 && x 12) || ((x 6 && x 10) || false)))))))))))))))))))))
    exact algebra (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) (x 12) (x 13)
  rw [eq]

private theorem direction (a b : V) (trace : ℕ → Bool)
    (input : ∀ i : Fin 14, trace i.val=decide (i.val=b.val))
    (run : ∀ j : Fin 29, let w := C.wires (List.ofFn (singletonBits a))
      let g := gateAt C j; let u := opnd C j 0; let v := opnd C j 1
      (g.op=.and → trace (14+j.val)=((w.getD u false && trace v) || (trace u && w.getD v false))) ∧
      (g.op=.or → trace (14+j.val)=(trace u || trace v))) (last : trace 42=false) : Dir C a b :=
  ⟨trace,fun i hi => input ⟨i,hi⟩,fun j hj => run ⟨j,hj⟩,last⟩

theorem checked : C.size=29 ∧ IsAO2 14 C ∧ (∀ j<C.size, opnd C j 0 ≠ opnd C j 1) ∧
    C.gates[0]?=some ⟨.or,[0,13]⟩ ∧ (∀ x, C.eval (List.ofFn x)=true ↔ ReceiptF x) ∧
    Dir C (0 : V) 7 ∧ Dir C (7 : V) 0 := by
  have distinct : ∀ j : Fin 29, opnd C j.val 0 ≠ opnd C j.val 1 := by decide +kernel
  refine ⟨rfl,by decide +kernel,fun j hj => distinct ⟨j,hj⟩,rfl,correct,?_,?_⟩
  · apply direction _ _ (fun w => decide (w ∈ ([7,15,16,17,18,19,20,21,23,24,28] : List ℕ))) <;> decide +kernel
  · apply direction _ _ (fun w => decide (w ∈ ([0,14,17,18,19,20,21] : List ℕ))) <;> decide +kernel

/-- Both ways of pinning the first gate change an observable output. -/
def pinned (value : Bool) : Circuit :=
  { C with gates := ⟨if value then .and else .or, []⟩ :: C.gates.tail }

theorem first_essential :
    let input (mask : ℕ) := List.ofFn (fun i : V => mask.testBit i.val)
    C.eval (input 129)=true ∧ (pinned false).eval (input 129)=false ∧
    C.eval (input 132)=false ∧ (pinned true).eval (input 132)=true := by decide +kernel

end FanoMixed29

#print axioms FanoMixed29.checked
#print axioms FanoMixed29.first_essential
