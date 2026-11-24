import OwnershipBase

namespace GirthAnchor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_1490

attribute [local instance] gateOpDecEq

def wire (n w : Nat) := if w<n then w else n+2*(w-n)+2

def anchor : Gate := ⟨.and,[]⟩

def buffer (n : Nat) (g : Gate) : Gate := ⟨.and,n::(g.inputs.take 1).map (wire n)⟩

def mainGate (n k : Nat) (g : Gate) : Gate :=
  ⟨g.op, if g.op=.and then (n+2*k+1)::g.inputs.tail.map (wire n) else g.inputs.map (wire n)⟩

def blocks (n : Nat) (k : Nat) : List Gate → List Gate
  | [] => []
  | g::gs => buffer n g :: mainGate n k g :: blocks n (k+1) gs

def anchored (n : Nat) (C : Circuit) : Circuit := ⟨anchor::blocks n 0 C.gates,wire n C.output⟩

@[simp] theorem blocks_len (n k : Nat) (gs : List Gate) : (blocks n k gs).length=2*gs.length := by
  induction gs generalizing k with
  | nil => rfl
  | cons g gs ih => simp [blocks,ih,Nat.mul_succ]

theorem exact_size (n : Nat) (C : Circuit) : (anchored n C).size=2*C.size+1 := by
  simp [Circuit.size,anchored]

theorem mono (n : Nat) {C : Circuit} (mc : Monotone2 C) : Monotone2 (anchored n C) := by
  have all (k : Nat) (gs : List Gate)
      (h : ∀g∈gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2) :
      ∀g∈blocks n k gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2 := by
    induction gs generalizing k with
    | nil => simp [blocks]
    | cons g gs ih =>
      have monoG := h g List.mem_cons_self
      intro a mem
      rcases List.mem_cons.mp mem with rfl | mem
      · simp [buffer]
      rcases List.mem_cons.mp mem with rfl | mem
      · refine ⟨monoG.1,?_⟩
        by_cases prod : g.op=.and
        · simp [mainGate,prod,List.length_tail]
          omega
        · simpa [mainGate,prod] using monoG.2
      · exact ih (k+1) (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) a mem
  intro g hg
  rcases List.mem_cons.mp hg with rfl | mem
  · simp [anchor]
  · exact all 0 _ mc _ mem

theorem unchanged_append (A : List Bool) (b : Bool) (i : Nat) (diff : i≠A.length) :
    (A++[b]).getD i false=A.getD i false := by
  by_cases earlier : i<A.length
  · simp [List.getD_eq_getElem?_getD,List.getElem?_append_left earlier]
  · rw [getD_ge _ _ (by simp; omega),getD_ge _ _ (by omega)]

theorem after_append (A : List Bool) (b : Bool) : (A++[b]).getD A.length false=b := by
  simp [List.getD_eq_getElem?_getD]

theorem wire_old (n k : Nat) : wire n (n+k)=n+2*k+2 := by simp [wire]

theorem wire_ne_buffer (n k w : Nat) : wire n w≠n+2*k+1 := by unfold wire; split <;> omega

theorem wire_ne_main (n k w : Nat) (diff : w≠n+k) : wire n w≠n+2*k+2 := by
  unfold wire
  split <;> omega

structure Correspond (n k : Nat) (A B : List Bool) : Prop where
  before : A.length=n+k
  afterPad : B.length=n+2*k+1
  truth : B.getD n false=true
  read : ∀ w, B.getD (wire n w) false=A.getD w false

theorem step {n k : Nat} {A B : List Bool} (r : Correspond n k A B) (g : Gate) :
    Correspond n (k+1) (stepWire A g) (stepWire (stepWire B (buffer n g)) (mainGate n k g)) := by
  let f (w : Nat) := A.getD w false
  let b := ((g.inputs.take 1).map f).all id
  let out := g.op.eval (g.inputs.map f)
  have mapped (L : List Nat) :
      (L.map (wire n)).map (fun w => B.getD w false) = L.map f := by
    simp only [List.map_map,Function.comp_def,r.read,f]
  have first : stepWire B (buffer n g) = B++[b] := by
    change B++[B.getD n false && (((g.inputs.take 1).map (wire n)).map (fun w => B.getD w false)).all id] = _
    rw [r.truth,mapped,Bool.true_and]
  have saved (w : Nat) : (B++[b]).getD (wire n w) false = f w := by
    rw [unchanged_append, r.read]
    exact r.afterPad ▸ wire_ne_buffer n k w
  have current : (B++[b]).getD (n+2*k+1) false=b := by rw [← r.afterPad,after_append]
  have mapped' (L : List Nat) :
      (L.map (wire n)).map (fun w => (B++[b]).getD w false) = L.map f := by
    simp only [List.map_map,Function.comp_def,saved]
  have second : stepWire (B++[b]) (mainGate n k g) = (B++[b])++[out] := by
    unfold stepWire
    congr 2
    by_cases prod : g.op=.and
    · simp only [mainGate,prod,ite_true,List.map_cons,current,mapped',out,GateOp.eval,List.all_cons,id_eq]
      cases ins : g.inputs <;> simp [b,ins]
    · simp only [mainGate,prod,ite_false,out,mapped']
  rw [first,second]
  change Correspond n (k+1) (A++[out]) ((B++[b])++[out])
  constructor
  · simp [r.before,Nat.add_assoc]
  · simp [r.afterPad]; omega
  · rw [unchanged_append _ _ _ (by simp [r.afterPad]; omega), unchanged_append _ _ _ (by rw [r.afterPad]; omega),r.truth]
  · intro w
    by_cases eq : w=n+k
    · subst w
      rw [wire_old]
      have size : (B++[b]).length=n+2*k+2 := by simp [r.afterPad]
      rw [← size,after_append,← r.before,after_append]
    · rw [unchanged_append _ _ _ (by have h:=wire_ne_main n k w eq; simp [r.afterPad]; omega),saved,
        unchanged_append _ _ _ (by rw [r.before]; exact eq)]

theorem fold_blocks (n k : Nat) (gs : List Gate) (A B : List Bool) (h : Correspond n k A B) :
    Correspond n (k+gs.length) (gs.foldl stepWire A) ((blocks n k gs).foldl stepWire B) := by
  induction gs generalizing k A B with
  | nil => simpa [blocks] using h
  | cons g gs ih =>
    simpa only [blocks,List.foldl_cons,List.length_cons,Nat.add_assoc,Nat.add_comm 1] using
      ih (k+1) _ _ (step h g)

theorem same_eval (n : Nat) (C : Circuit) (x : Fin n → Bool) :
    (anchored n C).eval (List.ofFn x)=C.eval (List.ofFn x) := by
  let A := List.ofFn x
  have len : A.length=n := List.length_ofFn
  have init : Correspond n 0 A (A++[true]) := by
    refine ⟨by simpa using len,by simp [len],len ▸ after_append A true,?_⟩
    intro w
    by_cases base : w<n
    · rw [wire,if_pos base,unchanged_append _ _ _ (by omega)]
    · rw [getD_ge _ _ (by unfold wire; rw [if_neg base]; simp [len]; omega),getD_ge _ _ (by omega)]
  exact (fold_blocks n 0 C.gates A (A++[true]) init).read C.output

end GirthAnchor
