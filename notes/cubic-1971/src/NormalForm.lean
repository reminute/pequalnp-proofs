import PartnerCertificate
import GraphStar

namespace Cubic1971.NormalForm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open StarReader NeighborCube PartnerCertificate

private theorem run_len (gs : List Gate) (x : List Bool) : (run gs x).length=x.length+gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (x++[gateValue g x])).length=_
    rw [ih]; simp; omega

private theorem keeps (gs : List Gate) (x : List Bool) {i : Nat} (hi : i<x.length) :
    (run gs x).getD i false=x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (x++[gateValue g x])).getD i false=_
    rw [ih _ (by simp; omega),List.getD_append _ _ _ _ hi]

private theorem raw {n} (gs : List Gate) (x : Fin n → Bool) (v : Fin n) :
    (run gs (List.ofFn x)).getD v.val false=x v := by
  rw [keeps _ _ (by simp)]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left v.isLt,Option.getD_some]

private def redirect (a v i : Nat) := if i=a then v else if a < i then i-1 else i
private def relabel (a v : Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map (redirect a v)⟩
private def aligned (a v : Nat) (u w : List Bool) : Prop :=
  a≤w.length ∧ u.length=w.length+1 ∧ ∀i,u.getD i false=w.getD (redirect a v i) false

private theorem after_copy (w : List Bool) (v : Nat) (z : Bool) (eq : z=w.getD v false) :
    aligned w.length v (w++[z]) w := by
  refine ⟨le_rfl,by simp,fun i => ?_⟩
  rcases lt_trichotomy i w.length with lo | rfl | hi
  · simpa [redirect,lo.ne,not_lt.mpr lo.le] using List.getD_append w [z] false i lo
  · simpa [redirect,List.getD_append_right] using eq
  · have outside : (w++[z]).length ≤ i := by simp; omega
    have outside' : w.length ≤ i-1 := by omega
    simp only [redirect,ite_eq_right hi.ne',ite_eq_left hi,List.getD_eq_getElem?_getD,
      List.getElem?_eq_none outside,List.getElem?_eq_none outside']

private theorem carry_copy {a v : Nat} (earlier : v<a) (gs : List Gate) {u w : List Bool}
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

/-- Delete one gate that copies an earlier raw input for all input rows, preserving
    the default value of forward and invalid wire reads in both halves. -/
theorem not_copy {n : Nat} {C : Circuit} {f : (Fin n → Bool) → Bool}
    (legal : FanInTwo C) (correct : circuitFun n C=f)
    (least : ∀ s, HasCircuitSize n f s → C.size ≤ s)
    {pre post : List Gate} {r : Gate} (layout : C.gates=pre++r::post) (v : Fin n)
    (copyOn : ∀ x : Fin n → Bool, gateValue r (run pre (List.ofFn x))=(run pre (List.ofFn x)).getD v.val false) :
    False := by
  let a := n+pre.length
  let D : Circuit := ⟨pre++post.map (relabel a v.val),redirect a v.val C.output⟩
  have fan : FanInTwo D := by
    intro g mem
    rcases List.mem_append.mp mem with old | new
    · exact legal _ (layout ▸ List.mem_append_left _ old)
    · obtain ⟨h,hm,rfl⟩ := List.mem_map.mp new
      simpa [relabel] using legal h (layout ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hm))
  have same (x : Fin n → Bool) : circuitFun n D x=circuitFun n C x := by
    let w := run pre (List.ofFn x)
    have count : w.length=a := by simp [w,a,run_len]
    have matched := after_copy w v.val (gateValue r w) (copyOn x)
    rw [count] at matched
    have done' := (carry_copy (show v.val<a by dsimp [a]; omega) post matched).2.2 C.output
    change (run (pre++post.map (relabel a v.val)) (List.ofFn x)).getD _ false=
      (run C.gates (List.ofFn x)).getD C.output false
    rw [layout]
    simpa only [D,w,run,List.foldl_append,List.foldl_cons] using done'.symm
  have upper := least D.size ⟨D,fan,le_rfl,fun x => (same x).trans (congrFun correct x)⟩
  simp [D,Circuit.size,layout] at upper

private theorem shapes {n : Nat} (v : Fin n) (r : Gate) (len : r.inputs.length≤2)
    (read : effective v.val r) :
    r.inputs=[v.val] ∨ r.inputs=[v.val,v.val] ∨
      ∃ k, k≠v.val ∧ (r.inputs=[v.val,k] ∨ r.inputs=[k,v.val]) := by
  have member : v.val∈r.inputs := List.mem_of_mem_take read
  cases h : r.inputs with
  | nil => simp [h] at member
  | cons a rest =>
    cases rest with
    | nil => exact Or.inl (by simpa [h,eq_comm] using member)
    | cons b tail =>
      have tail' : tail=[] := by simp [h] at len; simpa using len
      subst tail
      simp only [h,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with eq | eq
      · subst a
        by_cases same : b=v.val
        · exact Or.inr (Or.inl (by rw [same]))
        · exact Or.inr (Or.inr ⟨b,same,Or.inl rfl⟩)
      · subst b
        by_cases same : a=v.val
        · exact Or.inr (Or.inl (by rw [same]))
        · exact Or.inr (Or.inr ⟨a,same,Or.inr rfl⟩)

variable {n : Nat}

def readerCases (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (v : Fin n)
    (leaf : Fin 3 → Fin n) (pre : List Gate) (r : Gate) : Prop :=
  (r.op=.not ∧ r.inputs.head?=some v.val ∧
    ∀ x : Fin n → Bool, gateValue r (run pre (List.ofFn x))= !(x v)) ∨
  ∃ (isAnd : Bool) (k : Nat), k≠v.val ∧ k<n+pre.length ∧
    r.op=(if isAnd then .and else .or) ∧ (r.inputs=[v.val,k] ∨ r.inputs=[k,v.val]) ∧
    ((∀s, partner v leaf pre k s=isAnd) ∨
      ∀s, partner v leaf pre k s=if isAnd then anyNeighbor s else !(anyNeighbor s)) ∧
    (∀ P Z : Finset (Fin n), v∉P → Disjoint P Z → clean A P → free G P →
      (∀ S, v∉S → P⊆S → Disjoint S Z → physical pre k S≠isAnd) →
      (∀ w, G.Adj v w → w∈Z ∨ ∃u∈P, G.Adj w u) ∧ 3≤(P∪Z).card)

theorem least_reader_form (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool)
    (C : Circuit) (degree : ∀u∉A,(G.neighborSet u).ncard=3)
    (cycles : ∀a (p : G.Walk a a), p.IsCycle → 7≤p.length)
    (ordinary : ∀ u w, G.Adj u w → u∉A)
    (spec : ∀ x, f x=true ↔ (∃u∈A,x u=true) ∨ ∃u w,G.Adj u w ∧ x u=true ∧ x w=true)
    (legal : FanInTwo C) (correct : circuitFun n C=f)
    (least : ∀s,HasCircuitSize n f s → C.size ≤ s)
    (rare : ∃v∉A, (C.gates.filter (readBit v.val)).length≤1) :
    ∃ v∉A, ∃ leaf : Fin 3 → Fin n, Function.Injective leaf ∧ (∀u, G.Adj v u ↔ ∃i,leaf i=u) ∧
      ∃ pre r post, C.gates=pre++r::post ∧ effective v.val r ∧
      (∀g∈pre++post,¬effective v.val g) ∧ C.output≠v.val ∧ readerCases G A v leaf pre r := by
  classical
  obtain ⟨v,vm,cap⟩ := rare
  have card : Fintype.card (G.neighborSet v) = 3 := by
    simpa only [←Nat.card_coe_set_eq,Nat.card_eq_fintype_card] using degree v vm
  let equiv := Fintype.equivFinOfCardEq card
  let leaf (i : Fin 3) := (equiv.symm i).val
  have adj (i : Fin 3) : G.Adj v (leaf i) := (equiv.symm i).property
  have girth : GirthEdgeNegatives.GirthFive G := fun a p h => le_trans (by decide) (cycles a p h)
  have star (s : Bits) (x : Bool) : C.eval (List.ofFn (starInput v leaf s x))=(x && anyNeighbor s) :=
    (congrFun correct _).trans (GraphStar.evaluates_reader G A f spec ordinary v leaf adj
      (fun i j h => GirthEdgeNegatives.no_triangle girth (adj i) h (adj j).symm) s x)
  obtain ⟨pre,r,post,layout,read,sole⟩ := split_reader C v leaf legal cap star
  have output := output_ne_of_star C v leaf star
  refine ⟨v,vm,leaf,fun _ _ eq => equiv.symm.injective (Subtype.ext eq),?_,pre,r,post,layout,read,sole,output,?_⟩
  · intro u
    constructor
    · intro h
      exact ⟨equiv ⟨u,h⟩,congrArg Subtype.val (equiv.symm_apply_apply _)⟩
    · rintro ⟨i,rfl⟩; exact adj i
  have allowed := legal r (layout ▸ List.mem_append_right _ List.mem_cons_self)
  have target : f=graphFun G A := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [spec,graphFun,Bool.or_eq_true,decide_eq_true_eq]
  by_cases neg : r.op=.not
  · left
    cases ins : r.inputs with
    | nil => simp [effective,neg,ins,GateOp.eval] at read
    | cons a tail =>
      have eq : v.val=a := by simpa [effective,neg,ins,GateOp.eval] using read
      refine ⟨neg,by simp [eq],fun x => ?_⟩
      simp [gateValue,neg,ins,GateOp.eval,← eq]
      exact raw pre x v
  · right
    have ao : r.op=.and ∨ r.op=.or := by
      rcases allowed.1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (neg h).elim
    obtain unary | twice | ⟨k,other,ins⟩ := shapes v r allowed.2 read
    · apply False.elim (not_copy legal correct least layout v ?_)
      intro x
      rcases ao with h | h <;> simp [gateValue,h,unary,GateOp.eval]
    · apply False.elim (not_copy legal correct least layout v ?_)
      intro x
      rcases ao with h | h <;> simp [gateValue,h,twice,GateOp.eval]
    let isAnd := decide (r.op=.and)
    have gate : r.op=if isAnd then .and else .or := by rcases ao with h | h <;> simp [isAnd,h]
    have actual := circuit_enabled C pre post r k isAnd layout legal sole gate ins other output
      (correct.trans target) vm
    have valid : k<n+pre.length := by
      by_contra! invalid
      have missing (x : Fin n → Bool) : (run pre (List.ofFn x)).getD k false=false := by
        have far : (run pre (List.ofFn x)).length ≤ k := by simpa [run_len] using invalid
        simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none far]
      cases b : isAnd with
      | true =>
        have vw := adj 0
        have active : sensitive G A v {leaf 0} := by
          refine ⟨by simpa using vw.ne,?_,?_,leaf 0,by simp,vw⟩
          · intro u h; obtain rfl := Finset.mem_singleton.mp h; exact ordinary _ _ vw.symm
          · intro u hu t ht
            obtain rfl := Finset.mem_singleton.mp hu
            obtain rfl := Finset.mem_singleton.mp ht
            exact G.irrefl
        have on := actual _ active
        unfold physical at on
        rw [missing,b] at on
        contradiction
      | false =>
        apply not_copy legal correct least layout v
        intro x
        have op : r.op=.or := by simpa [b] using gate
        rcases ins with h | h <;> simp only [gateValue,op,h,List.map_cons,List.map_nil,GateOp.eval] <;> rw [missing] <;> simp
    refine ⟨isAnd,k,other,valid,gate,ins,classified_reader C v leaf pre post r k isAnd layout legal sole
      gate ins other output star,?_⟩
    intro P Z without disjoint good independent cert
    exact circuit_certificate C pre post r k isAnd layout legal sole gate ins other output
      (correct.trans target) vm (fun h => ordinary _ _ h) girth (degree v vm) without disjoint good independent cert

end Cubic1971.NormalForm

#print axioms Cubic1971.NormalForm.not_copy
#print axioms Cubic1971.NormalForm.least_reader_form
