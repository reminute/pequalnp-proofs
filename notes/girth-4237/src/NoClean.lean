import Anchor

namespace GirthAnchor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_1490

attribute [local instance] gateOpDecEq

theorem block_get (n k r : Nat) (gs : List Gate) (good : r<gs.length) :
    (blocks n k gs)[2*r]? = some (buffer n gs[r]) ∧
    (blocks n k gs)[2*r+1]? = some (mainGate n (k+r) gs[r]) := by
  induction gs generalizing k r with
  | nil => simp at good
  | cons g gs ih =>
    cases r with
    | zero => simp [blocks]
    | succ r =>
      have prev := ih (k+1) r (by simpa using good)
      simpa only [blocks,Nat.mul_succ,List.getElem?_cons_succ,List.getElem_cons_succ,
        Nat.add_assoc,Nat.add_comm 1] using prev

theorem gate_pair (n : Nat) (C : Circuit) (r : Nat) (hr : r<C.gates.length) :
    gateAt (anchored n C) (2*r+1) = buffer n C.gates[r] ∧
    gateAt (anchored n C) (2*r+2) = mainGate n r C.gates[r] := by
  obtain ⟨a,b⟩ := block_get n 0 r C.gates hr
  simp only [Nat.zero_add] at b
  simp only [gateAt,anchored,List.getD_eq_getElem?_getD,List.getElem?_cons_succ,a,b,Option.getD_some,and_self]

theorem anchor_gate (n : Nat) (C : Circuit) : gateAt (anchored n C) 0 = anchor := rfl

theorem anchor_true (n : Nat) (C : Circuit) (x : Fin n → Bool) :
    gateVal n (anchored n C) 0 x = true := by
  apply (show val (anchored n C) (List.ofFn x) (n+0)=true from ?_)
  rw [val_gate List.length_ofFn (show 0 < (anchored n C).gates.length by simp [anchored]),anchor_gate]
  rfl

theorem buffer_cone (n : Nat) (C : Circuit) (r : Nat) (hr : r<C.gates.length) :
    InCone n (anchored n C) 0 (2*r+1) := by
  apply (inCone_iff ..).mpr
  refine ⟨by simp [anchored]; omega,0,by omega,?_,Or.inl rfl⟩
  rw [(gate_pair n C r hr).1]
  simp [buffer]

theorem later_and_cone {n : Nat} {C : Circuit} {j : Nat} (hj : j<(anchored n C).gates.length)
    (pos : 0<j) (op : (gateAt (anchored n C) j).op=GateOp.and) : InCone n (anchored n C) 0 j := by
  let r := (j-1)/2
  have total : (anchored n C).gates.length = 2*C.gates.length+1 := by simp [anchored]
  have hr : r<C.gates.length := by dsimp [r]; omega
  have cases : j=2*r+1 ∨ j=2*r+2 := by dsimp [r]; omega
  rcases cases with eq | eq
  · exact eq ▸ buffer_cone n C r hr
  · rw [eq] at op ⊢
    have main := (gate_pair n C r hr).2
    rw [main] at op
    change C.gates[r].op=GateOp.and at op
    apply (inCone_iff ..).mpr
    refine ⟨by omega,2*r+1,by omega,?_,Or.inr (buffer_cone n C r hr)⟩
    rw [main]
    simp [mainGate,op,Nat.add_assoc]

theorem owner_eq_zero {n : Nat} {C : Circuit} {j : Nat} {u v : Fin n}
    (own : Owns n (anchored n C) j u v) : j=0 := by
  by_contra neq
  have before := later_and_cone own.1 (by omega) own.2.1
  have off := own.2.2.2 0 (by omega) before rfl
  rw [anchor_true] at off
  contradiction

theorem no_clean {n : Nat} (G : SimpleGraph (Fin n)) {C : Circuit} {j : Nat} {u v : Fin n}
    (own : Owns n (anchored n C) j u v) :
    ¬ ∀ p q : Fin n, gateVal n (anchored n C) j (pairInput p q)=true → G.Adj p q := by
  intro clean
  rw [owner_eq_zero own] at clean
  exact G.irrefl (clean u u (anchor_true n C _))

end GirthAnchor
