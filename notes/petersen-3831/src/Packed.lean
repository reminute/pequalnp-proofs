import InversionCover

namespace Petersen3831.Packed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open RawPartner InversionCover
open PEqualNP.Outside.L_meta_1490

def bits (m : Nat) := List.ofFn fun i : Fin 9 => m.testBit i.val
def v (C : Circuit) (w m : Nat) := (C.wires (bits m)).getD w false
def g (m : Nat) := ([3,6,12,24,17,33,66,132,264,160,320,288] : List Nat).any
  (fun e => e &&& m == e)
def ok (C : Circuit) := ∀ m : Fin 512, v C C.output (m.val ^^^ 1) = g m.val
def S := (List.range 256).filter fun m =>
  (([366204442379749154,1099511628578,1794,770] : List Nat).getD (m/64) 0).testBit (m%64)
def expensive (C : Circuit) (k : Nat) := ∃ j < C.gates.length, k < j ∧
  (gateAt C j).op = GateOp.not ∧ 3 ≤ (S.filter (fun m =>
    v C (9+j) (2*m) && !v C (9+j) (2*m+1))).length

private theorem decoded (x : Input) :
    (fun i : Fin 9 => (encode x).testBit i.val) = x := by
  funext i
  change (BitVec.ofBoolListLE (List.ofFn x)).getLsbD i.val = x i
  rw [BitVec.getLsbD_ofBoolListLE]
  have bound : i.val < (List.ofFn x).length := by simp
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem bound,Option.getD_some,List.getElem_ofFn]

private theorem packing (m : Fin 512) :
    bits (m.val ^^^ 1) = List.ofFn (RawPartner.flip (fun i => m.val.testBit i.val)) ∧
    g m.val = graph (fun i => m.val.testBit i.val) := by
  exact (by decide +kernel : ∀ z : Fin 512, bits (z.val ^^^ 1) =
    List.ofFn (RawPartner.flip (fun i => z.val.testBit i.val)) ∧
    g z.val = graph (fun i => z.val.testBit i.val)) m

theorem correct {C : Circuit} (h : ok C) (x : Input) :
    circuitFun 9 C (RawPartner.flip x) = graph x := by
  have small : encode x < 512 := by
    simpa [encode] using (BitVec.ofBoolListLE (List.ofFn x)).isLt
  let m : Fin 512 := ⟨encode x,small⟩
  have ⟨a,b⟩ := packing m
  have eq := h m
  unfold v at eq
  rw [a,b,show (fun i : Fin 9 => m.val.testBit i.val) = x from decoded x] at eq
  exact eq

private theorem compression :
    ∀ m ∈ rows, m/2 ∈ S ∧ 2*(m/2)=m ∧
      bits (2*(m/2)) = List.ofFn (row m false) ∧
      bits (2*(m/2)+1) = List.ofFn (row m true) := by decide +kernel

theorem normalization {C : Circuit} {k a : Nat} (fan : FanInTwo C) (size : C.size ≤ 14)
    (once : unique C) (hk : k<C.gates.length) (positive : 0<a) (_back : a<9+k)
    (op : (gateAt C k).op=.and ∨ (gateAt C k).op=.or) (inputs : (gateAt C k).inputs=[0,a])
    (h : ok C) : 9 ≤ a ∧ expensive C k := by
  constructor
  · by_contra! raw
    obtain ⟨x,hx⟩ := raw_partner C k a once hk positive raw op inputs
    exact hx (correct h x)
  obtain ⟨j,hj,neg,three⟩ := three_rows C fan size once hk inputs op (correct h)
  obtain ⟨bound,later,_,_⟩ := Finset.mem_filter.mp hj
  refine ⟨j,Finset.mem_range.mp bound,later,neg,?_⟩
  let good := S.filter (fun m => v C (9+j) (2*m) && !v C (9+j) (2*m+1))
  have inject : (covered C j).card ≤ good.toFinset.card := by
    apply Finset.card_le_card_of_injOn (fun m => m/2)
    · intro m hm
      obtain ⟨base,lo,hi⟩ := Finset.mem_filter.mp hm
      obtain ⟨member,_,zero,one⟩ := compression m base
      apply List.mem_toFinset.mpr
      apply List.mem_filter.mpr
      refine ⟨member,?_⟩
      simp only [v,zero,one]
      change (val C (List.ofFn (row m false)) (9+j) && !val C (List.ofFn (row m true)) (9+j)) = true
      rw [lo,hi]
      rfl
    · intro m hm l hl eq
      have mm := (compression m (Finset.mem_filter.mp hm).1).2.1
      have ll := (compression l (Finset.mem_filter.mp hl).1).2.1
      change m/2 = l/2 at eq
      exact mm.symm.trans ((congrArg (fun z : Nat => 2*z) eq).trans ll)
  exact three.trans (inject.trans (List.toFinset_card_le good))

end Petersen3831.Packed

#print axioms Petersen3831.Packed.normalization
