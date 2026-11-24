import DegreePartner
import WeightedPin

namespace Edge606.MinimalPartner

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Cubic1971.StarReader Cubic1971.PartnerCertificate
open PEqualNP.Outside.L_meta_1708_aux

-- The wire-renumbering invariant and its two proofs are from the L-meta-1971
-- companion, Cubic1971.NormalForm. Here the resulting circuit preserves
-- Monotone2, and the earlier wire may itself be an internal gate output.
def redirect (a v i : Nat) := if i=a then v else if a < i then i-1 else i
def relabel (a v : Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map (redirect a v)⟩
def aligned (a v : Nat) (u w : List Bool) : Prop :=
  a≤w.length ∧ u.length=w.length+1 ∧ ∀i,u.getD i false=w.getD (redirect a v i) false

theorem after_copy (w : List Bool) (v : Nat) (z : Bool) (eq : z=w.getD v false) :
    aligned w.length v (w++[z]) w := by
  refine ⟨le_rfl,by simp,fun i => ?_⟩
  rcases lt_trichotomy i w.length with lo | rfl | hi
  · simpa [redirect,lo.ne,not_lt.mpr lo.le] using List.getD_append w [z] false i lo
  · simpa [redirect,List.getD_append_right] using eq
  · have outside : (w++[z]).length ≤ i := by simp; omega
    have outside' : w.length ≤ i-1 := by omega
    simp only [redirect,ite_eq_right hi.ne',ite_eq_left hi,List.getD_eq_getElem?_getD,
      List.getElem?_eq_none outside,List.getElem?_eq_none outside']

theorem carry_copy {a v : Nat} (earlier : v<a) (gs : List Gate) {u w : List Bool}
    (match' : aligned a v u w) : aligned a v (run gs u) (run (gs.map (relabel a v)) w) := by
  induction gs generalizing u w with
  | nil => exact match'
  | cons g gs ih =>
    obtain ⟨ready,len,equal⟩ := match'
    have val : gateValue g u=gateValue (relabel a v g) w := by
      unfold gateValue
      apply congrArg g.op.eval
      simp only [relabel,List.map_map]
      exact List.map_congr_left (fun i _ => equal i)
    apply ih
    refine ⟨by simp; omega,by simp [len],fun i => ?_⟩
    by_cases ok : i<u.length
    · have valid : redirect a v i<w.length := by unfold redirect; split_ifs <;> omega
      simpa only [List.getD_append _ _ _ _ ok,List.getD_append _ _ _ _ valid] using equal i
    · have hi : a < i := by omega
      have shift : redirect a v i=i-1 := by simp [redirect,hi.ne',hi]
      rw [shift,List.getD_append_right u _ _ i (by omega),List.getD_append_right w _ _ (i-1) (by omega),val]
      exact congrArg (fun j => [gateValue (relabel a v g) w].getD j false) (by omega)

/-- A gate that copies any earlier physical wire on every input can be removed. -/
theorem bypass_copy {n : Nat} (C : Circuit) (mono : Monotone2 C)
    (pre post : List Gate) (r : Gate) (i : Nat) (layout : C.gates = pre ++ r :: post)
    (earlier : i < n + pre.length)
    (copyOn : ∀ x : Fin n → Bool, gateValue r (run pre (List.ofFn x)) =
      (run pre (List.ofFn x)).getD i false) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 = C.size ∧ circuitFun n D = circuitFun n C := by
  let a := n + pre.length
  let D : Circuit := ⟨pre ++ post.map (relabel a i), redirect a i C.output⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · intro g mem
    change g ∈ pre ++ post.map (relabel a i) at mem
    rcases List.mem_append.mp mem with old | new
    · exact mono _ (layout ▸ List.mem_append_left _ old)
    · obtain ⟨h, hm, rfl⟩ := List.mem_map.mp new
      simpa [relabel] using mono h (layout ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hm))
  · simp [D,Circuit.size,layout]; omega
  · funext x
    let w := run pre (List.ofFn x)
    have count : w.length = a := by
      change (wiresFrom pre (List.ofFn x)).length = n + pre.length
      simp [length_wiresFrom]
    have matched := after_copy w i (gateValue r w) (copyOn x)
    rw [count] at matched
    have done' := (carry_copy earlier post matched).2.2 C.output
    change (run (pre ++ post.map (relabel a i)) (List.ofFn x)).getD _ false =
      (run C.gates (List.ofFn x)).getD C.output false
    rw [layout]
    simpa only [D,w,run,List.foldl_append,List.foldl_cons] using done'.symm

theorem not_copy {n : Nat} (C : Circuit) (minimal : IsMinimalMonoCircuit n C)
    (pre post : List Gate) (r : Gate) (i : Nat) (layout : C.gates = pre ++ r :: post)
    (earlier : i < n + pre.length) :
    ¬ ∀ x : Fin n → Bool, gateValue r (run pre (List.ofFn x)) =
      (run pre (List.ofFn x)).getD i false := by
  intro copies
  obtain ⟨D,mono,size,eq⟩ := bypass_copy C minimal.1 pre post r i layout earlier copies
  have := minimal.2 D mono eq
  omega

/-- A single earlier wire cannot be the only operand, even listed twice. -/
theorem no_single_operand {n : Nat} (C : Circuit) (minimal : IsMinimalMonoCircuit n C)
    (pre post : List Gate) (r : Gate) (i : Nat) (layout : C.gates = pre ++ r :: post)
    (earlier : i < n + pre.length) : ¬ (r.inputs = [i] ∨ r.inputs = [i,i]) := by
  intro shape
  apply not_copy C minimal pre post r i layout earlier
  intro x
  have mem : r ∈ C.gates := layout ▸ List.mem_append_right _ List.mem_cons_self
  have ops : r.op = .and ∨ r.op = .or := (minimal.1 r mem).1
  rcases shape with arg | arg <;> rcases ops with op | op
  all_goals
    simp only [gateValue,op,arg,List.map_cons,List.map_nil]
    cases (run pre (List.ofFn x)).getD i false <;> rfl

/-- A binary AND with a raw input has a partner that rejects the empty
    assignment in every least-size monotone circuit. -/
theorem and_empty {n : Nat} (C : Circuit) (minimal : IsMinimalMonoCircuit n C)
    (pre post : List Gate) (r : Gate) (k : Nat) (v : Fin n)
    (layout : C.gates = pre ++ r :: post) (op : r.op = .and)
    (args : r.inputs = [v.val,k] ∨ r.inputs = [k,v.val]) :
    physical pre k (∅ : Finset (Fin n)) = false := by
  cases base : physical pre k (∅ : Finset (Fin n)) with
  | false => rfl
  | true =>
    exfalso
    apply not_copy C minimal pre post r v.val layout (by have := v.isLt; omega)
    intro x
    let S := Finset.univ.filter fun i : Fin n => x i = true
    have represent : bits S = x := by
      funext i
      simp [bits,S]
    have pos (g : Gate) (hg : g ∈ pre) : g.op = .and ∨ g.op = .or :=
      (minimal.1 g (layout ▸ List.mem_append_left _ hg)).1
    have active := DegreePartner.physical_mono pre k pos (Finset.empty_subset S) base
    change (run pre (List.ofFn (bits S))).getD k false = true at active
    rw [represent] at active
    rcases args with order | order <;>
      simp only [gateValue,op,order,List.map_cons,List.map_nil,GateOp.eval,List.all_cons,
        List.all_nil,id_eq,active,Bool.and_true,Bool.true_and]

end Edge606.MinimalPartner
