import RawPartners
import CleanSignal
import MinimalPartner

namespace Edge606.ReaderShape

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Cubic1971.StarReader Cubic1971.PartnerCertificate
open GraphDensity (edgeFunction)

private theorem proper {L : List Nat} {i : Nat} (read : i ∈ L) (two : L.length ≤ 2)
    (copies : ¬(L = [i] ∨ L = [i,i])) :
    ∃ w, w ≠ i ∧ (L = [i,w] ∨ L = [w,i]) := by
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
  · simp at read
  · have same : i = a := by simpa using read
    exact (copies (Or.inl (by rw [same]))).elim
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at read
    rcases read with rfl | rfl
    · exact ⟨b,fun eq => copies (Or.inr (by rw [eq])),Or.inl rfl⟩
    · exact ⟨a,fun eq => copies (Or.inr (by rw [eq])),Or.inr rfl⟩
  · simp at two

private theorem sole {n : Nat} {C : Circuit} {v : Fin n} {pre post : List Gate} {r : Gate}
    (layout : C.gates = pre ++ r :: post) (read : v.val ∈ r.inputs)
    (cap : WeightedPin.readers C v ≤ 1) : ∀ g ∈ pre ++ post, ¬effective v.val g := by
  let p (g : Gate) := decide (v.val ∈ g.inputs)
  have yes : p r = true := decide_eq_true read
  rw [WeightedPin.readers_eq_length] at cap
  change (C.gates.filter p).length ≤ 1 at cap
  rw [layout,List.filter_append,List.filter_cons_of_pos yes] at cap
  simp only [List.length_append,List.length_cons] at cap
  have left : pre.filter p = [] := List.length_eq_zero_iff.mp (by omega)
  have right : post.filter p = [] := List.length_eq_zero_iff.mp (by omega)
  intro g hg he
  have present : v.val ∈ g.inputs := List.mem_of_mem_take he
  have value : p g = true := decide_eq_true present
  rcases List.mem_append.mp hg with h | h
  · exact List.not_mem_nil (left ▸ List.mem_filter.mpr ⟨h,value⟩)
  · exact List.not_mem_nil (right ▸ List.mem_filter.mpr ⟨h,value⟩)

/-- In the remaining minimum circuits, low-degree active vertices have a unique
    proper reader. If it comes early, it is an OR with a partner already below
    the graph function on every assignment. -/
theorem locate {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (girth : GirthEdgeNegatives.GirthFive G) (C : Circuit) (minimum : IsMinimalMonoCircuit n C)
    (computes : circuitFun n C = edgeFunction G) (k : Nat) (hk : 0 < k)
    (sparse : ReaderCore.sparseReads k G C) (v : Fin n)
    (active : 0 < G.degree v) (low : G.degree v ≤ 2*k) :
    ∃ (pre post : List Gate) (r : Gate) (w : Nat), C.gates = pre ++ r :: post ∧
      (∀ g ∈ pre ++ post, ¬effective v.val g) ∧ n ≤ w ∧ w < n + pre.length ∧
      (r.inputs = [v.val,w] ∨ r.inputs = [w,v.val]) ∧
      (G.degree v ≤ pre.length + 1 ∨ (r.op = .or ∧ ∀ x : Fin n → Bool,
        circuitFun n (⟨pre,w⟩ : Circuit) x = true → edgeFunction G x = true)) := by
  obtain ⟨j,read⟩ := PEqualNP.Outside.L_meta_1708_aux.reads_vertex G v active C computes
  let r := C.gates.get j
  have member : r ∈ C.gates := List.get_mem _ _
  obtain ⟨pre,post,layout⟩ := List.mem_iff_append.mp member
  have cap : WeightedPin.readers C v ≤ 1 := by
    by_contra! many
    have bad := sparse v active
    have larger := Nat.mul_le_mul_left k (show 2 ≤ WeightedPin.readers C v by omega)
    omega
  have unique := sole layout read cap
  have earlier : v.val < n + pre.length := by omega
  have ⟨op,len⟩ := minimum.1 r member
  obtain ⟨w,other,args⟩ := proper read len (MinimalPartner.no_single_operand C minimum pre post r v.val layout earlier)
  change r.inputs = [v.val,w] ∨ r.inputs = [w,v.val] at args
  have index := RawPartners.internal_index girth C minimum.1 computes v k hk sparse active low j w other args
  have out := TwinReads.output_ne computes v
  change r.op = GateOp.and ∨ r.op = GateOp.or at op
  have valid : w < n + pre.length := by
    by_contra! invalid
    have off (x : Fin n → Bool) : (run pre (List.ofFn x)).getD w false = false := by
      apply List.getD_eq_default
      change (PEqualNP.Outside.L_meta_1708_aux.wiresFrom pre (List.ofFn x)).length ≤ w
      simpa [PEqualNP.Outside.L_meta_1708_aux.length_wiresFrom] using invalid
    rcases op with andGate | orGate
    · obtain ⟨u,adj⟩ := (G.degree_pos_iff_mem_support v).mp active
      have yes := DegreePartner.and_neighbors G v C pre post r w layout minimum.1 unique args other
        out computes andGate u adj
      change (run pre (List.ofFn (bits {u}))).getD w false = true at yes
      rw [off] at yes
      contradiction
    · obtain ⟨D,dm,size,same⟩ := MinimalPartner.bypass_copy C minimum.1 pre post r v.val layout earlier (by
        intro x
        unfold gateValue
        rcases args with h | h <;> rw [h,orGate] <;>
          simp only [GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,
            off x,Bool.or_false,Bool.false_or])
      have smallest := minimum.2 D dm same
      omega
  refine ⟨pre,post,r,w,layout,unique,index,valid,args,?_⟩
  rcases op with andGate | orGate
  · have off := MinimalPartner.and_empty C minimum pre post r w v layout andGate args
    exact Or.inl (DegreePartner.and_essential G v C pre post r w layout minimum.1 unique args other out
      computes andGate off).2
  · rcases CleanSignal.or_global G v C pre post r w layout minimum.1 unique args other out
      computes orGate girth with late | clean
    · exact Or.inl late
    · exact Or.inr ⟨orGate,clean⟩

end Edge606.ReaderShape

#print axioms Edge606.ReaderShape.locate
