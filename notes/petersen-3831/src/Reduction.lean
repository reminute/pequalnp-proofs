import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3831_825
(normalize : let v := fun (C : Circuit) (w m : Nat) =>
  (C.wires (List.ofFn fun i : Fin 9 => m.testBit i.val)).getD w false
let ok := fun (C : Circuit) => ∀ m : Fin 512,
  v C C.output (m.val ^^^ 1) = ([3,6,12,24,17,33,66,132,264,160,320,288] : List Nat).any (fun e => e &&& m.val == e)
let S := (List.range 256).filter (fun m => (([366204442379749154, 1099511628578, 1794, 770] : List Nat).getD (m / 64) 0).testBit (m % 64))
let expensive := fun (C : Circuit) (k : Nat) => ∃ j < C.gates.length, k < j ∧
  (gateAt C j).op = GateOp.not ∧ 3 ≤ (S.filter (fun m =>
    v C (9+j) (2*m) && !v C (9+j) (2*m+1))).length
∀ (C : Circuit) (k a : Nat), FanInTwo C → C.size ≤ 14 → (C.gates.filter (fun g => g.inputs.contains 0)).length = 1 →
  k < C.gates.length → 0 < a → a < 9+k →
  ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) →
  (gateAt C k).inputs = [0,a] → ok C → 9 ≤ a ∧ expensive C k)
(remaining : let v := fun (C : Circuit) (w m : Nat) =>
  (C.wires (List.ofFn fun i : Fin 9 => m.testBit i.val)).getD w false
let ok := fun (C : Circuit) => ∀ m : Fin 512,
  v C C.output (m.val ^^^ 1) = ([3,6,12,24,17,33,66,132,264,160,320,288] : List Nat).any (fun e => e &&& m.val == e)
let S := (List.range 256).filter (fun m => (([366204442379749154, 1099511628578, 1794, 770] : List Nat).getD (m / 64) 0).testBit (m % 64))
let expensive := fun (C : Circuit) (k : Nat) => ∃ j < C.gates.length, k < j ∧
  (gateAt C j).op = GateOp.not ∧ 3 ≤ (S.filter (fun m =>
    v C (9+j) (2*m) && !v C (9+j) (2*m+1))).length
∀ (C : Circuit) (k a : Nat), FanInTwo C → C.size ≤ 14 → (C.gates.filter (fun g => g.inputs.contains 0)).length = 1 →
  k < C.gates.length → 0 < a → a < 9+k →
  ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) →
  (gateAt C k).inputs = [0,a] → 9 ≤ a → expensive C k → ¬ ok C) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.inputs.contains (0 : ℕ)) x1.gates).length = (1 : ℕ) → x2 < x1.gates.length → (0 : ℕ) < x3 → x3 < (9 : ℕ) + x2 → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.or → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).inputs = [(0 : ℕ), x3] → ∃ (x12 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x13 : Fin (9 : ℕ)) => if x13 = (0 : Fin (9 : ℕ)) then !x12 (0 : Fin (9 : ℕ)) else x12 x13) ≠ (x12 (0 : Fin (9 : ℕ)) && x12 (1 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (3 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (4 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)) && x12 (0 : Fin (9 : ℕ)) || x12 (0 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (6 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (5 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (6 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (8 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ))) := by
  intro C k a fan size once valid positive earlier op inputs
  by_contra! correct
  have table : ∀ m : Fin 512,
      ((List.ofFn (fun i : Fin 9 => (m.val ^^^ 1).testBit i.val))) =
        List.ofFn (fun i : Fin 9 => if i=0 then !m.val.testBit 0 else m.val.testBit i.val) ∧
      (let x := fun i : Fin 9 => m.val.testBit i.val
       (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5)) =
        ([3,6,12,24,17,33,66,132,264,160,320,288] : List Nat).any (fun e => e &&& m.val == e) := by decide +kernel
  have yes (m : Fin 512) :
      (C.wires (List.ofFn fun i : Fin 9 => (m.val ^^^ 1).testBit i.val)).getD C.output false =
        ([3,6,12,24,17,33,66,132,264,160,320,288] : List Nat).any (fun e => e &&& m.val == e) := by
    rw [(table m).1]
    exact (correct (fun i => m.val.testBit i.val)).trans (table m).2
  obtain ⟨internal,inversions⟩ := normalize C k a fan size once valid positive earlier op inputs yes
  exact remaining C k a fan size once valid positive earlier op inputs internal inversions yes
