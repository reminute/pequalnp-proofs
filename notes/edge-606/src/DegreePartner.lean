import Sensitivity
import Support

namespace Edge606.DegreePartner

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Cubic1971.StarReader Cubic1971.PartnerCertificate

-- The ordered-wire induction is from the L-meta-1971 SuffixBarrier proof.
private def Ordered (w z : List Bool) : Prop :=
  w.length = z.length ∧ ∀ i, w.getD i false = true → z.getD i false = true

private theorem extend {w z : List Bool} (h : Ordered w z) {x y : Bool}
    (xy : x = true → y = true) : Ordered (w ++ [x]) (z ++ [y]) := by
  refine ⟨by simp [h.1],fun i => ?_⟩
  by_cases earlier : i < w.length
  · rw [List.getD_append _ _ _ _ earlier,List.getD_append _ _ _ _ (h.1 ▸ earlier)]
    exact h.2 i
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by rw [←h.1]; omega),h.1]
    cases i-z.length with
    | zero => exact xy
    | succ j => simp [List.getD_eq_getElem?_getD]

private theorem run_order (gs : List Gate)
    (pos : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) {w z : List Bool}
    (h : Ordered w z) : Ordered (run gs w) (run gs z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    apply ih (fun d mem => pos d (List.mem_cons_of_mem _ mem))
    apply extend h
    rcases pos g (by simp) with op | op
    · simp [gateValue,op,GateOp.eval]
      exact fun all i mem => h.2 i (all i mem)
    · simp [gateValue,op,GateOp.eval]
      exact fun i mem on => ⟨i,mem,h.2 i on⟩

variable {n : Nat}

theorem physical_mono (pre : List Gate) (k : Nat)
    (pos : ∀ g ∈ pre, g.op = .and ∨ g.op = .or)
    {S T : Finset (Fin n)} (sub : S ⊆ T) :
    physical pre k S = true → physical pre k T = true := by
  apply (run_order pre pos ?_).2 k
  refine ⟨by simp,fun i => ?_⟩
  by_cases hi : i < n
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left hi,
      Option.getD_some,bits,decide_eq_true_eq]
    exact fun h => sub h
  · simp [List.getD_eq_getElem?_getD,hi]

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n)
variable (C : Circuit) (pre post : List Gate) (r : Gate) (k : Nat)
variable (layout : C.gates = pre ++ r :: post) (mono : Monotone2 C)
variable (sole : ∀ g ∈ pre ++ post, ¬effective v.val g)
variable (args : r.inputs = [v.val,k] ∨ r.inputs = [k,v.val])
variable (other : k ≠ v.val) (output : C.output ≠ v.val)
variable (computes : circuitFun n C = GraphDensity.edgeFunction G)

include layout mono in
private theorem prefixMono :
    Monotone2 (⟨pre,k⟩ : Circuit) := by
  intro g mem
  exact mono g (layout ▸ List.mem_append_left _ mem)

include layout mono sole args other output computes

private theorem enabled (pass : Bool) (op : r.op = if pass then .and else .or)
    (S : Finset (Fin n)) (s : sensitive G ∅ v S) : physical pre k S = pass := by
  apply circuit_enabled C pre post r k pass layout (GirthFiveCore.mono_fan mono) sole op args other output _ (by simp) S s
  rw [computes]
  funext x
  apply Bool.eq_iff_iff.mpr
  simp [GraphDensity.edgeFunction,NestedCover.graphFun]

/-- If a sole OR's partner fires on an independent set avoiding v, the set
    contains at least deg(v) active coordinates. -/
theorem or_width (op : r.op = .or) (girth : GirthEdgeNegatives.GirthFive G)
    (S : Finset (Fin n)) (away : v ∉ S) (ind : free G S) (fires : physical pre k S = true) :
    G.degree v ≤ S.card := by
  by_contra! short
  obtain ⟨T,sub,_,sensitiveT⟩ := Sensitivity.complete_input (v:=v) girth S ∅ away
    (by simp) ind (by simpa using short)
  have pfx := prefixMono C pre post r k layout mono
  have on := physical_mono pre k (fun g hg => (pfx g hg).1) sub fires
  have off := enabled G v C pre post r k layout mono sole args other output computes false op T sensitiveT
  exact Bool.noConfusion (off.symm.trans on)

theorem and_neighbors (op : r.op = .and) :
    ∀ w, G.Adj v w → physical pre k {w} = true := by
  intro w vw
  apply enabled G v C pre post r k layout mono sole args other output computes true op
  exact ⟨by simpa using vw.ne,by simp [clean],by simp [free],w,by simp,vw⟩

/-- Every neighbor is witnessed essential by flipping it on in the empty
    input. This bounds the actual number of gates before the sole AND. -/
theorem and_essential (op : r.op = .and) (base : physical pre k (∅ : Finset (Fin n)) = false) :
    G.neighborFinset v ⊆ Support.essentialInputs (circuitFun n (⟨pre,k⟩ : Circuit)) ∧
    G.degree v ≤ pre.length + 1 := by
  classical
  have sub : G.neighborFinset v ⊆ Support.essentialInputs (circuitFun n (⟨pre,k⟩ : Circuit)) := by
    intro w hw
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,bits ∅,?_⟩
    have upd : Function.update (bits (∅ : Finset (Fin n))) w (!(bits ∅ w)) = bits {w} := by
      funext i
      by_cases h : i=w <;> simp [bits,h,Function.update_of_ne]
    rw [upd]
    change physical pre k {w} ≠ physical pre k (∅ : Finset (Fin n))
    rw [base,and_neighbors G v C pre post r k layout mono sole args other output computes op w
      ((G.mem_neighborFinset v w).mp hw)]
    decide
  refine ⟨sub,?_⟩
  rw [← G.card_neighborFinset_eq_degree]
  exact (Finset.card_le_card sub).trans (Support.monotone_bound _ (prefixMono C pre post r k layout mono))

/-- A smallest accepted subset of an independent row witnesses at least deg(v)
    essential inputs of the partner. Erasing any one of those inputs rejects. -/
theorem or_minimal_witness (op : r.op = .or) (girth : GirthEdgeNegatives.GirthFive G)
    (S : Finset (Fin n)) (away : v ∉ S) (ind : free G S) (fires : physical pre k S = true) :
    ∃ T ⊆ S, physical pre k T = true ∧ G.degree v ≤ T.card ∧
      T ⊆ Support.essentialInputs (circuitFun n (⟨pre,k⟩ : Circuit)) := by
  classical
  let candidate (m : Nat) := ∃ T : Finset (Fin n), T ⊆ S ∧ physical pre k T = true ∧ T.card = m
  have ex : ∃ m, candidate m := ⟨S.card,S,Finset.Subset.rfl,fires,rfl⟩
  obtain ⟨T,sub,on,smallest⟩ := Nat.find_spec ex
  have size := or_width G v C pre post r k layout mono sole args other output computes op girth T
    (fun h => away (sub h)) (fun u hu w hw => ind u (sub hu) w (sub hw)) on
  refine ⟨T,sub,on,size,?_⟩
  intro w hw
  have off : physical pre k (T.erase w) ≠ true := by
    intro high
    apply Nat.find_min ex (smallest ▸ Finset.card_erase_lt_of_mem hw)
    exact ⟨T.erase w,(Finset.erase_subset _ _).trans sub,high,rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,bits (T.erase w),?_⟩
  have upd : Function.update (bits (T.erase w)) w (!(bits (T.erase w) w)) = bits T := by
    funext i
    by_cases h : i=w <;> simp [bits,h,hw,Function.update_of_ne]
  rw [upd]
  change physical pre k T ≠ physical pre k (T.erase w)
  exact fun eq => off (eq.symm.trans on)

omit layout mono sole args other output computes in
theorem no_independent_iff :
    (¬ ∃ S : Finset (Fin n), v ∉ S ∧ free G S ∧ physical pre k S = true) ↔
      (∀ x : Fin n → Bool, x v = false → circuitFun n (⟨pre,k⟩ : Circuit) x = true →
        GraphDensity.edgeFunction G x = true) := by
  classical
  constructor
  · intro absent x center fires
    let S := Finset.univ.filter (fun i => x i = true)
    have same : bits S = x := by funext i; cases h : x i <;> simp [bits,S,h]
    have on : physical pre k S = true := by
      change circuitFun n (⟨pre,k⟩ : Circuit) (bits S) = true
      rwa [same]
    by_contra none
    apply absent
    refine ⟨S,by simp [S,center],?_,on⟩
    intro u hu w hw edge
    exact none (decide_eq_true ⟨u,w,edge,(Finset.mem_filter.mp hu).2,(Finset.mem_filter.mp hw).2⟩)
  · rintro safe ⟨S,away,ind,on⟩
    have hit := safe (bits S) (by simp [bits,away]) on
    simp only [GraphDensity.edgeFunction,bits,decide_eq_true_eq] at hit
    obtain ⟨u,w,edge,hu,hw⟩ := hit
    exact ind u hu w hw edge

/-- In any correct monotone circuit, either the sole OR's partner needs a prefix
    with at least deg(v)-1 gates, or every input accepted by that partner with
    the center off already contains an edge. No circuit minimality is needed. -/
theorem or_dichotomy (op : r.op = .or) (girth : GirthEdgeNegatives.GirthFive G) :
    G.degree v ≤ pre.length + 1 ∨
      (∀ x : Fin n → Bool, x v = false → circuitFun n (⟨pre,k⟩ : Circuit) x = true →
        GraphDensity.edgeFunction G x = true) := by
  classical
  by_cases witness : ∃ S : Finset (Fin n), v ∉ S ∧ free G S ∧ physical pre k S = true
  · obtain ⟨S,away,ind,on⟩ := witness
    obtain ⟨T,_,_,size,sub⟩ := or_minimal_witness G v C pre post r k layout mono sole
      args other output computes op girth S away ind on
    exact Or.inl (size.trans ((Finset.card_le_card sub).trans
      (Support.monotone_bound _ (prefixMono C pre post r k layout mono))))
  · exact Or.inr ((no_independent_iff G v pre k).mp witness)

end Edge606.DegreePartner

#print axioms Edge606.DegreePartner.physical_mono
#print axioms Edge606.DegreePartner.or_width
#print axioms Edge606.DegreePartner.and_neighbors
#print axioms Edge606.DegreePartner.and_essential
#print axioms Edge606.DegreePartner.or_minimal_witness
#print axioms Edge606.DegreePartner.no_independent_iff
#print axioms Edge606.DegreePartner.or_dichotomy
