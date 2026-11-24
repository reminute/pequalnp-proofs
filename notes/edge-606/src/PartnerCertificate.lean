import EdgeNegatives
import StarReader

namespace Cubic1971.PartnerCertificate

open SimpleGraph PEqualNP.MetaComplexity.NestedCover

variable {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
variable {A P Z S : Finset (Fin n)} {v : Fin n}

def bits (S : Finset (Fin n)) (u : Fin n) : Bool := decide (u∈S)
def clean (A S : Finset (Fin n)) := ∀ u ∈ S, u ∉ A
def free (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :=
  ∀ u ∈ S, ∀ w ∈ S, ¬G.Adj u w

def sensitive (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (v : Fin n) (S : Finset (Fin n)) : Prop :=
  v∉S ∧ clean A S ∧ free G S ∧ ∃ w∈S, G.Adj v w

theorem graph_on (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A S : Finset (Fin n)) :
    graphFun G A (bits S) = true ↔ (∃ a∈A, a∈S) ∨ ∃ i j, G.Adj i j ∧ i∈S ∧ j∈S := by
  simp [graphFun,bits]

theorem toggle (hv : v∉A) (away : v∉S) :
    sensitive G A v S ↔ graphFun G A (bits S)=false ∧ graphFun G A (bits (insert v S))=true := by
  constructor
  · rintro ⟨_,good,ind,w,mem,adj⟩
    constructor
    · cases h : graphFun G A (bits S) with
      | false => rfl
      | true =>
        rcases (graph_on G A S).mp h with ⟨a,ma,ms⟩ | ⟨i,j,ij,mi,mj⟩
        · exact (good a ms ma).elim
        · exact (ind i mi j mj ij).elim
    · exact (graph_on G A _).mpr (Or.inr ⟨v,w,adj,Finset.mem_insert_self _ _,Finset.mem_insert_of_mem mem⟩)
  · rintro ⟨off,on⟩
    have absent : ¬ ((∃ a∈A, a∈S) ∨ ∃ i j, G.Adj i j ∧ i∈S ∧ j∈S) := by
      intro yes
      exact Bool.noConfusion (off.symm.trans ((graph_on G A S).mpr yes))
    refine ⟨away,fun u us ua => absent (Or.inl ⟨u,ua,us⟩),
      fun u us w ws adj => absent (Or.inr ⟨u,w,adj,us,ws⟩),?_⟩
    rcases (graph_on G A _).mp on with ⟨a,ma,ms⟩ | ⟨i,j,adj,mi,mj⟩
    · rcases Finset.mem_insert.mp ms with rfl | old
      · exact (hv ma).elim
      · exact (absent (Or.inl ⟨a,ma,old⟩)).elim
    · rcases Finset.mem_insert.mp mi with rfl | hi
      · rcases Finset.mem_insert.mp mj with rfl | hj
        · exact (G.loopless.irrefl _ adj).elim
        · exact ⟨j,hj,adj⟩
      · rcases Finset.mem_insert.mp mj with rfl | hj
        · exact ⟨i,hi,adj.symm⟩
        · exact (absent (Or.inr ⟨i,j,adj,hi,hj⟩)).elim

omit [DecidableRel G.Adj] in
/-- A partial assignment fixing P high and Z low extends to a sensitive row
    exactly if one neighbor can be adjoined without violating the fixed literals. -/
theorem completion_iff (away : v∉P) (apart : Disjoint P Z)
    (ordinary : ∀ {u w}, G.Adj u w → u∉A) (marked : clean A P) (ind : free G P) :
    (∃ S, P⊆S ∧ Disjoint S Z ∧ sensitive G A v S) ↔
    ∃ w, G.Adj v w ∧ w∉Z ∧ ∀ u∈P, ¬G.Adj w u := by
  constructor
  · rintro ⟨S,sub,no,_,_,ok,w,ws,adj⟩
    exact ⟨w,adj,fun wz => Finset.disjoint_left.mp no ws wz,fun u up => ok w ws u (sub up)⟩
  · rintro ⟨w,adj,wz,extend⟩
    refine ⟨insert w P,Finset.subset_insert _ _,Finset.disjoint_left.mpr ?_,?_,?_,?_,w,by simp,adj⟩
    · intro i mem zi
      rcases Finset.mem_insert.mp mem with rfl | hi
      · exact wz zi
      · exact Finset.disjoint_left.mp apart hi zi
    · simp [adj.ne,away]
    · intro i mem
      rcases Finset.mem_insert.mp mem with rfl | u
      · exact ordinary adj.symm
      · exact marked i u
    · intro i hi j hj
      rcases Finset.mem_insert.mp hi with rfl | ia <;> rcases Finset.mem_insert.mp hj with rfl | ja
      · exact G.irrefl
      · exact extend j ja
      · exact fun ij => extend i ia ij.symm
      · exact ind i ia j ja

omit [DecidableRel G.Adj] in
/-- If the partner is enabled on all sensitive inputs, every certificate forcing
    its blocking value must block every neighbor by one of two signed conditions. -/
theorem blockers (partner : Finset (Fin n) → Bool) (pass : Bool)
    (enabled : ∀ S, sensitive G A v S → partner S=pass)
    (away : v∉P) (apart : Disjoint P Z) (ordinary : ∀ {u w}, G.Adj u w → u∉A)
    (marked : clean A P) (ind : free G P)
    (cert : ∀ S, v∉S → P⊆S → Disjoint S Z → partner S≠pass) :
    ∀ w, G.Adj v w → w∈Z ∨ ∃ u∈P, G.Adj w u := by
  intro w vw
  by_contra! denied
  obtain ⟨S,hi,lo,s⟩ := (completion_iff away apart ordinary marked ind).mpr ⟨w,vw,denied.1,denied.2⟩
  exact cert S s.1 hi lo (enabled S s)

private def branch (G : SimpleGraph (Fin n)) (v w t : Fin n) :=
  t=w ∨ (t≠v ∧ G.Adj w t)

omit [DecidableRel G.Adj] in
private theorem branch_unique (girth : GirthEdgeNegatives.GirthFive G) {a b t : Fin n}
    (va : G.Adj v a) (vb : G.Adj v b) (ha : branch G v a t) (hb : branch G v b t) : a=b := by
  by_contra diff
  rcases ha with rfl | ⟨other,at'⟩ <;> rcases hb with eq | ⟨_,bt'⟩
  · exact diff eq
  · exact GirthEdgeNegatives.no_triangle girth vb bt' va.symm
  · subst t
    exact GirthEdgeNegatives.no_triangle girth va at' vb.symm
  · exact GirthEdgeNegatives.no_square girth va at' bt'.symm vb.symm other.symm diff

/-- The three signed blocks use three distinct raw variables. Girth five is
    already sufficient for this part of the girth-seven problem. -/
theorem three_literals (girth : GirthEdgeNegatives.GirthFive G) (degree : (G.neighborSet v).ncard=3)
    (away : v∉P) (block : ∀ w, G.Adj v w → w∈Z ∨ ∃ u∈P, G.Adj w u) : 3≤(P∪Z).card := by
  classical
  have pick (w : G.neighborSet v) : ∃ u : ↑(P∪Z), branch G v w.val u.val := by
    rcases block w.val w.property with h | ⟨u,up,adj⟩
    · exact ⟨⟨w.val,Finset.mem_union_right _ h⟩,Or.inl rfl⟩
    · exact ⟨⟨u,Finset.mem_union_left _ up⟩,Or.inr ⟨fun eq => away (eq ▸ up),adj⟩⟩
  choose f hf using pick
  have inj : Function.Injective f := by
    intro i j eq
    apply Subtype.ext
    exact branch_unique girth i.property j.property (hf i) (eq ▸ hf j)
  have bound := Fintype.card_le_of_injective f inj
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at degree
  simpa only [degree,Fintype.card_coe] using bound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def physical (pre : List Gate) (k : Nat) (S : Finset (Fin n)) : Bool :=
  (StarReader.run pre (List.ofFn (bits S))).getD k false

/-- The enabling value applies to the physical prefix wire on every independent,
    unmarked set that meets the center's neighborhood. -/
theorem circuit_enabled (C : Circuit) (pre post : List Gate) (r : Gate) (k : Nat) (isAnd : Bool)
    (layout : C.gates = pre ++ r :: post) (legal : FanInTwo C)
    (sole : ∀ g ∈ pre ++ post, ¬StarReader.effective v.val g)
    (readerOp : r.op=if isAnd then .and else .or)
    (inputs : r.inputs=[v.val,k] ∨ r.inputs=[k,v.val]) (other : k≠v.val) (output : C.output≠v.val)
    (correct : circuitFun n C=graphFun G A) (ordinary : v∉A)
    (S : Finset (Fin n)) (hs : sensitive G A v S) : physical pre k S=isAnd := by
  have off : Function.update (bits S) v false=bits S := by
    funext u
    by_cases h : u=v <;> simp [h,Function.update_of_ne,bits,hs.1]
  have on : Function.update (bits S) v true=bits (insert v S) := by
    funext u
    by_cases h : u=v <;> simp [h,Function.update_of_ne,bits]
  have ⟨lo,hi⟩ := (toggle ordinary hs.1).mp hs
  have changeVal : C.eval (List.ofFn (Function.update (bits S) v false)) ≠
      C.eval (List.ofFn (Function.update (bits S) v true)) := by
    change circuitFun n C _ ≠ circuitFun n C _
    rw [off,on,correct,lo,hi]
    decide
  have fact := StarReader.gatedPartner C v pre post r k isAnd layout legal sole readerOp inputs
    other output (bits S) changeVal
  rw [off] at fact
  exact fact

/-- A certificate of the wrong physical partner value on an independent
    mark-free positive part has to mention at least three distinct coordinates. -/
theorem circuit_certificate (C : Circuit) (pre post : List Gate) (r : Gate) (k : Nat) (isAnd : Bool)
    (layout : C.gates = pre ++ r :: post) (legal : FanInTwo C)
    (sole : ∀ g ∈ pre ++ post, ¬StarReader.effective v.val g)
    (readerOp : r.op=if isAnd then .and else .or)
    (inputs : r.inputs=[v.val,k] ∨ r.inputs=[k,v.val]) (other : k≠v.val) (output : C.output≠v.val)
    (correct : circuitFun n C=graphFun G A) (unmarked : v∉A)
    (ordinary : ∀ {u w}, G.Adj u w → u∉A)
    (girth : GirthEdgeNegatives.GirthFive G) (degree : (G.neighborSet v).ncard=3)
    (away : v∉P) (apart : Disjoint P Z) (good : clean A P) (ind : free G P)
    (cert : ∀ S, v∉S → P⊆S → Disjoint S Z → physical pre k S≠isAnd) :
    (∀ w, G.Adj v w → w∈Z ∨ ∃ u∈P, G.Adj w u) ∧ 3 ≤ (P∪Z).card := by
  have on := circuit_enabled C pre post r k isAnd layout legal sole readerOp inputs other output correct unmarked
  have block := blockers _ isAnd on away apart ordinary good ind cert
  exact ⟨block,three_literals girth degree away block⟩

/-- The same conclusion applies when a support bound is semantic. In particular,
    with at most two observed coordinates the partner is enabled on *every*
    unmarked independent row, even if it has no active neighbor of v. -/
theorem supported_pair (partner : Finset (Fin n) → Bool) (pass : Bool)
    (enabled : ∀ S, sensitive G A v S → partner S=pass)
    (ordinary : ∀ {u w}, G.Adj u w → u∉A)
    (girth : GirthEdgeNegatives.GirthFive G) (degree : (G.neighborSet v).ncard=3)
    (K : Finset (Fin n)) (small : K.card≤2)
    (supportOn : ∀ S T : Finset (Fin n), v∉S → v∉T →
      (∀ x∈K, x∈S ↔ x∈T) → partner S=partner T)
    (S : Finset (Fin n)) (away : v∉S) (good : clean A S) (ind : free G S) : partner S=pass := by
  by_contra wrong
  let P := K∩S
  let Z := K\S
  have subP : P⊆S := Finset.inter_subset_right
  have apart : Disjoint P Z := Finset.disjoint_left.mpr fun _ hp hz => (Finset.mem_sdiff.mp hz).2 (subP hp)
  have certificate (T : Finset (Fin n)) (vT : v∉T) (subT : P⊆T) (sep : Disjoint T Z) :
      partner T≠pass := by
    rw [← supportOn S T away vT (fun x xK => ?_)]
    · exact wrong
    · constructor
      · exact fun xS => subT (Finset.mem_inter.mpr ⟨xK,xS⟩)
      · intro xT
        by_contra miss
        exact Finset.disjoint_left.mp sep xT (Finset.mem_sdiff.mpr ⟨xK,miss⟩)
  have obstruction := blockers partner pass enabled (fun p => away (subP p)) apart ordinary
    (fun u h => good u (subP h)) (fun u h w j => ind u (subP h) w (subP j)) certificate
  have count := three_literals girth degree (fun p => away (subP p)) obstruction
  have le : P∪Z⊆K := Finset.union_subset Finset.inter_subset_left Finset.sdiff_subset
  have upper := Finset.card_le_card le
  omega

def children (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v w : Fin n) : Finset (Fin n) :=
  (G.neighborFinset w).erase v

/-- A positive obstruction must select a child of each neighbor. A signed one
    may instead fix that neighbor to false. The choices are indexed by the three
    neighbors, without imposing an arbitrary order on them. -/
theorem choice_counts (degree : ∀u∉A, (G.neighborSet u).ncard=3) (ordinary : ∀ {u w}, G.Adj u w → u∉A)
    (unmarked : v∉A) :
    Fintype.card (∀ w : G.neighborSet v, ↥(children G v w.val)) = 8 ∧
    Fintype.card (∀ w : G.neighborSet v, ↥(insert w.val (children G v w.val))) = 27 := by
  have countV : Fintype.card (G.neighborSet v)=3 := by
    simpa only [← Nat.card_coe_set_eq,Nat.card_eq_fintype_card] using degree v unmarked
  have kids (w : G.neighborSet v) : (children G v w.val).card=2 := by
    have adj : G.Adj v w.val := w.property
    have mem := (G.mem_neighborFinset w.val v).mpr adj.symm
    have full : (G.neighborFinset w.val).card=3 := by
      rw [← Set.ncard_coe_finset,SimpleGraph.coe_neighborFinset]
      exact degree w.val (ordinary adj.symm)
    rw [children,Finset.card_erase_of_mem mem,full]
  have choices (w : G.neighborSet v) : (insert w.val (children G v w.val)).card=3 := by
    have fresh : w.val ∉ children G v w.val := by simp [children]
    rw [Finset.card_insert_of_notMem fresh,kids]
  constructor <;> rw [Fintype.card_pi] <;>
    simp only [Fintype.card_coe,kids,choices,Finset.prod_const,Finset.card_univ,countV] <;> decide

/-- The endpoint sets of different choices of children are different. Thus the
    count of eight does not double-count a single three-vertex obstruction. -/
theorem transversal_injective (girth : GirthEdgeNegatives.GirthFive G) :
    Function.Injective (fun f : (∀ w : G.neighborSet v, ↥(children G v w.val)) =>
      Finset.univ.image (fun w => (f w).val)) := by
  intro f g eq
  dsimp only at eq
  funext w
  apply Subtype.ext
  have h : (f w).val ∈ Finset.univ.image (fun k => (g k).val) := by
    rw [← eq]
    exact Finset.mem_image.mpr ⟨w,Finset.mem_univ _,rfl⟩
  obtain ⟨k,_,same⟩ := Finset.mem_image.mp h
  have child (d : G.neighborSet v) (a : ↥(children G v d.val)) : branch G v d.val a.val := by
    obtain ⟨ne,mem⟩ := Finset.mem_erase.mp a.property
    exact Or.inr ⟨ne,(G.mem_neighborFinset _ _).mp mem⟩
  have wk : w=k := Subtype.ext (branch_unique girth w.property k.property (child w (f w)) (same ▸ child k (g k)))
  subst k
  exact same.symm

/-- For a clean independent conjunction, the list of positive obstructions is
    complete: one must take one second neighbor in each of the three branches. -/
theorem positive_obstructions (away : v∉P) (ordinary : ∀ {u w}, G.Adj u w → u∉A)
    (good : clean A P) (ind : free G P) :
    (∀ S, P⊆S → ¬ sensitive G A v S) ↔
    ∃ f : (∀ w : G.neighborSet v, ↥(children G v w.val)), ∀ w, (f w).val ∈ P := by
  constructor
  · intro no
    have chooseChild (w : G.neighborSet v) : ∃ u : ↥(children G v w.val), u.val∈P := by
      by_contra! miss
      have available : ∀ u∈P, ¬G.Adj w.val u := by
        intro u up adj
        exact miss ⟨u,Finset.mem_erase.mpr ⟨fun eq => away (eq ▸ up),(G.mem_neighborFinset _ _).mpr adj⟩⟩ up
      obtain ⟨S,sub,_,s⟩ := (completion_iff (Z:=∅) away (by simp) ordinary good ind).mpr
        ⟨w.val,w.property,by simp,available⟩
      exact no S sub s
    choose f hf using chooseChild
    exact ⟨f,hf⟩
  · rintro ⟨f,hf⟩ S sub ⟨_,_,indS,w,ws,vw⟩
    let w' : G.neighborSet v := ⟨w,vw⟩
    have adj := (G.mem_neighborFinset w _).mp (Finset.mem_erase.mp (f w').property).2
    exact indS w ws _ (sub (hf w')) adj

/-- The representatives themselves are independent full inputs, since an edge
    joining chosen children in different branches would create a pentagon. -/
theorem child_sets_free (girth : ∀ a (p : G.Walk a a), p.IsCycle → 7≤p.length)
    (f : ∀ w : G.neighborSet v, ↥(children G v w.val)) :
    free G (Finset.univ.image fun w => (f w).val) := by
  intro a ma b mb edge
  obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp ma
  obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp mb
  have ne : w≠u := by intro same; subst u; exact G.irrefl edge
  have wu : w.val ≠ u.val := fun eq => ne (Subtype.ext eq)
  have vw : G.Adj v w.val := w.property
  have vu : G.Adj v u.val := u.property
  obtain ⟨wv,rawW⟩ := Finset.mem_erase.mp (f w).property
  obtain ⟨uv,rawU⟩ := Finset.mem_erase.mp (f u).property
  have ww := (G.mem_neighborFinset _ _).mp rawW
  have uu := (G.mem_neighborFinset _ _).mp rawU
  have girth5 : GirthEdgeNegatives.GirthFive G := fun a p c => le_trans (by decide) (girth a p c)
  have cross1 : w.val ≠ (f u).val := by
    intro eq
    exact GirthEdgeNegatives.no_triangle girth5 vu (eq ▸ uu) vw.symm
  have cross2 : u.val ≠ (f w).val := by
    intro eq
    exact GirthEdgeNegatives.no_triangle girth5 vw (eq ▸ ww) vu.symm
  let path : G.Walk v v := .cons vw (.cons ww (.cons edge (.cons uu.symm (.cons vu.symm .nil))))
  have cycle : path.IsCycle := by
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    simp [path,Walk.isPath_def,vw.ne.symm,vu.ne.symm,ww.ne,uu.ne.symm,
      edge.ne,wu,wv,uv,cross1,cross2.symm]
  have short := girth v path cycle
  simp [path] at short

/-- A monotone OR partner can be true on a mark-free independent set only if
    all three branches are represented at distance two. An AND partner must pass
    every assignment containing at least one neighbor. -/
theorem monotone_extremes (partner : Finset (Fin n) → Bool) (pass : Bool)
    (mon : ∀ T U : Finset (Fin n), v∉T → v∉U → T⊆U → partner T=true → partner U=true)
    (enabled : ∀ S, sensitive G A v S → partner S=pass)
    (ordinary : ∀ {u w}, G.Adj u w → u∉A) (S : Finset (Fin n)) (away : v∉S) :
    (pass=false → clean A S → free G S → partner S=true →
      ∃ f : (∀ w : G.neighborSet v, ↥(children G v w.val)), ∀ w, (f w).val∈S) ∧
    (pass=true → (∃ w∈S, G.Adj v w) → partner S=true) := by
  constructor
  · rintro rfl good ind on
    apply (positive_obstructions away ordinary good ind).mp
    intro T sub hs
    exact Bool.noConfusion ((enabled _ hs).symm.trans (mon S T away hs.1 sub on))
  · rintro rfl ⟨w,ws,vw⟩
    apply mon {w} S (by simpa using vw.ne) away (Finset.singleton_subset_iff.mpr ws)
    apply enabled
    refine ⟨by simpa using vw.ne,?_,?_,w,by simp,vw⟩
    · intro u h; obtain rfl := Finset.mem_singleton.mp h
      exact ordinary vw.symm
    · intro u hu t ht
      obtain rfl := Finset.mem_singleton.mp hu
      obtain rfl := Finset.mem_singleton.mp ht
      exact G.irrefl

end Cubic1971.PartnerCertificate

#print axioms Cubic1971.PartnerCertificate.completion_iff
#print axioms Cubic1971.PartnerCertificate.blockers
#print axioms Cubic1971.PartnerCertificate.three_literals
#print axioms Cubic1971.PartnerCertificate.circuit_certificate
#print axioms Cubic1971.PartnerCertificate.supported_pair
#print axioms Cubic1971.PartnerCertificate.choice_counts
#print axioms Cubic1971.PartnerCertificate.transversal_injective
#print axioms Cubic1971.PartnerCertificate.positive_obstructions
#print axioms Cubic1971.PartnerCertificate.child_sets_free
#print axioms Cubic1971.PartnerCertificate.monotone_extremes
