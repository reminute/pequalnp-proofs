import ConeBase

namespace G11Structure

open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1490

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem cone_lt {a b : ℕ} (ha : InCone n C a b) : a < b := by
  induction b using Nat.strong_induction_on with
  | ind b ih =>
    obtain ⟨_,k,hk,_,eq | sub⟩ := (inCone_iff n C a b).mp ha
    · omega
    · exact (ih k hk sub).trans hk

theorem side_operand {c : ℕ} (ao : IsAO2 n C) (hc : c < C.gates.length) (b : Fin 2) :
    opnd C c b ∈ (gateAt C c).inputs ∧ opnd C c b < n+c := by
  obtain ⟨a,d,eq⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hc))
  have member : opnd C c b ∈ (gateAt C c).inputs := by
    fin_cases b <;> simp [opnd,eq]
  exact ⟨member,ao.2.1 c hc _ member⟩

theorem and_sides {c : ℕ} (ao : IsAO2 n C) (hc : c < C.gates.length)
    (op : (gateAt C c).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C c x = true ↔ ∀ b : Fin 2, wireVal n C (opnd C c b) x = true := by
  have ev := val_and (C:=C) (n:=n) (x:=List.ofFn x) List.length_ofFn hc op
  obtain ⟨a,d,eq⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hc))
  have e₀ : opnd C c 0 = a := by simp [opnd,eq]
  have e₁ : opnd C c 1 = d := by simp [opnd,eq]
  constructor
  · intro ok b
    exact (ev.mp ok _ (side_operand ao hc b).1).2
  · intro ok
    apply ev.mpr
    intro w hw
    have less := ao.2.1 c hc w hw
    simp [eq] at hw
    rcases hw with rfl | rfl
    · exact ⟨less,e₀ ▸ ok 0⟩
    · exact ⟨less,e₁ ▸ ok 1⟩

theorem and_ancestor_junk (tf : TopForm G C) {c g : ℕ}
    (hc : c < C.gates.length) (cop : (gateAt C c).op = GateOp.and)
    (hg : g < C.gates.length) (gop : (gateAt C g).op = GateOp.and)
    (anc : InCone n C g c) : g ∈ junk G C := by
  have notBelow : ¬ BelowF G C g := fun below => tf g hg c hc gop below cop anc
  change ¬ ∀ x : Fin n → Bool, gateVal n C g x = true → graphFun G ∅ x = true at notBelow
  push Not at notBelow
  obtain ⟨x,hit,miss⟩ := notBelow
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg,gop,hg,x,hit,by simpa using miss⟩

def lit (S : Finset (Fin n)) (x : Fin n → Bool) : Prop := ∃ v ∈ S, x v = true

theorem operand_iff (ao : IsAO2 n C) (tf : TopForm G C) {a : ℕ}
    (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and) (b : Fin 2) (x : Fin n → Bool) :
    wireVal n C (opnd C a b) x = true ↔ lit (side C a b) x ∨
      ∃ j ∈ junk G C, OrReaches n C (opnd C a b) j ∧ gateVal n C j x = true := by
  constructor
  · intro hw
    obtain ⟨w,path,hit,hw | ⟨g,hg,rfl,notOr⟩⟩ :=
      or_trace (C:=C) (n:=n) (x:=List.ofFn x) List.length_ofFn (opnd C a b) hw
    · let v : Fin n := ⟨w,hw⟩
      exact Or.inl ⟨v,reach_mem_orIn v path,(val_ofFn C x v).symm.trans hit⟩
    · have gop := (ao.1 _ (gateAt_mem hg)).resolve_right notOr
      obtain ⟨mem,earlier⟩ := side_operand ao ha b
      have dirty := and_ancestor_junk tf ha hop hg gop (operand_cone ha mem earlier path)
      exact Or.inr ⟨g,dirty,reach_orReaches path g rfl hg,hit⟩
  · rintro (⟨v,mem,hit⟩ | ⟨j,_,path,hit⟩)
    · exact reach_var_val x _ v (mem_orIn_reach v mem) hit
    · exact orStep_up (n:=n) List.length_ofFn (orReaches_reach j _ path).1 hit

theorem primitive_junk (ao : IsAO2 n C) (tf : TopForm G C) {j k : ℕ}
    (hset : junk G C = {j,k}) (hkj : ¬ InCone n C k j) (x : Fin n → Bool) :
    gateVal n C j x = true ↔ ∀ b : Fin 2, lit (side C j b) x := by
  have member : j ∈ junk G C := hset ▸ Finset.mem_insert_self _ _
  obtain ⟨bound,op,_⟩ := Finset.mem_filter.mp member
  have hj := Finset.mem_range.mp bound
  rw [and_sides ao hj op x]
  constructor
  · intro ok b
    rcases (operand_iff ao tf hj op b x).mp (ok b) with litSide | ⟨a,ha,reach,_⟩
    · exact litSide
    · have anc := operand_cone hj (side_operand ao hj b).1 (side_operand ao hj b).2 (orReaches_reach a _ reach).1
      rw [hset] at ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · have := cone_lt anc
        omega
      · exact (hkj anc).elim
  · exact fun litAll b => (operand_iff ao tf hj op b x).mpr (Or.inl (litAll b))

theorem no_dirty_both_sides (ao : IsAO2 n C) {t j : ℕ}
    (ht : t ∈ tops G C) (hj : j ∈ junk G C) :
    ¬ (OrReaches n C (opnd C t 0) j ∧ OrReaches n C (opnd C t 1) j) := by
  classical
  rintro ⟨h₀,h₁⟩
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at ht
  obtain ⟨bt,opt,below⟩ := ht
  obtain ⟨_,_,_,x,on,off⟩ := Finset.mem_filter.mp hj
  have hit : gateVal n C t x = true := by
    apply (and_sides ao bt opt x).mpr
    intro b
    have both : OrReaches n C (opnd C t b) j := by fin_cases b <;> assumption
    exact orStep_up (n:=n) List.length_ofFn (orReaches_reach j _ both).1 on
  exact Bool.noConfusion (off.symm.trans (below x hit))

theorem cone_trans {a b c : ℕ} (ab : InCone n C a b) (bc : InCone n C b c) :
    InCone n C a c := by
  induction c using Nat.strong_induction_on with
  | ind c ih =>
    obtain ⟨hc,k,hk,mem,sub⟩ := (inCone_iff n C b c).mp bc
    apply (inCone_iff n C a c).mpr
    refine ⟨hc,k,hk,mem,Or.inr ?_⟩
    rcases sub with rfl | prev
    · exact ab
    · exact ih k hk prev

theorem or_path_to_gate {a k : ℕ} (anc : InCone n C a k)
    (clean : ∀ m, (m = k ∨ InCone n C m k) → InCone n C a m → (gateAt C m).op = GateOp.or) :
    Relation.ReflTransGen (OrStep n C) (n+k) (n+a) := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    obtain ⟨hk,m,lt,mem,sub⟩ := (inCone_iff n C a k).mp anc
    have down : OrStep n C (n+k) (n+m) := ⟨k,hk,rfl,clean k (Or.inl rfl) anc,mem,by omega⟩
    rcases sub with rfl | am
    · exact .single down
    · apply Relation.ReflTransGen.head down
      apply ih m lt am
      intro u position au
      have mk := (inCone_iff n C m k).mpr ⟨hk,m,lt,mem,Or.inl rfl⟩
      rcases position with rfl | um
      · exact clean _ (Or.inr mk) au
      · exact clean u (Or.inr (cone_trans um mk)) au

theorem reaches_one_side (ao : IsAO2 n C) (tf : TopForm G C) {j k t : ℕ}
    (marked : junk G C = {j,k}) (incomp : ¬ InCone n C j k) (ht : t ∈ tops G C)
    (jt : InCone n C j t) : ∃ b : Fin 2, OrReaches n C (opnd C t b) j := by
  classical
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at ht
  obtain ⟨ht,op,_⟩ := ht
  obtain ⟨_,m,mt,reader,sub⟩ := (inCone_iff n C j t).mp jt
  have mt' := (inCone_iff n C m t).mpr ⟨ht,m,mt,reader,Or.inl rfl⟩
  have path : Relation.ReflTransGen (OrStep n C) (n+m) (n+j) := by
    rcases sub with rfl | jm
    · exact .refl
    · apply or_path_to_gate jm
      intro u pos ju
      have ut : InCone n C u t := pos.elim (fun eq => eq.symm ▸ mt') (fun um => cone_trans um mt')
      have hu := (cone_lt ut).trans ht
      rcases ao.1 _ (gateAt_mem hu) with prod | plus
      · have mem := and_ancestor_junk tf ht op hu prod ut
        rw [marked] at mem
        simp only [Finset.mem_insert, Finset.mem_singleton] at mem
        rcases mem with rfl | rfl
        · have := cone_lt ju
          omega
        · exact (incomp ju).elim
      · exact plus
  obtain ⟨a,b,ins⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem ht))
  have cases : n+m = a ∨ n+m = b := by simpa [ins] using reader
  have hj := (cone_lt jt).trans ht
  have reached := reach_orReaches path j rfl hj
  rcases cases with rfl | rfl
  · exact ⟨0,by simpa [opnd,ins] using reached⟩
  · exact ⟨1,by simpa [opnd,ins] using reached⟩

theorem opposite_cleans_product (ao : IsAO2 n C) {t j k : ℕ} (ht : t ∈ tops G C)
    (jLeft : OrReaches n C (opnd C t 0) j)
    (kRight : OrReaches n C (opnd C t 1) k) (x : Fin n → Bool)
    (onJ : gateVal n C j x = true) (onK : gateVal n C k x = true) :
    graphFun G ∅ x = true := by
  classical
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at ht
  obtain ⟨bound,op,below⟩ := ht
  apply below x
  apply (and_sides ao bound op x).mpr
  intro b
  fin_cases b
  · exact orStep_up (n:=n) List.length_ofFn (orReaches_reach j _ jLeft).1 onJ
  · exact orStep_up (n:=n) List.length_ofFn (orReaches_reach k _ kRight).1 onK

theorem same_side_vertex (ao : IsAO2 n C) {t j : ℕ} (ht : t ∈ tops G C)
    (b : Fin 2) (reach : OrReaches n C (opnd C t b) j) (w : Fin n)
    (raw : w ∈ side C t (1-b)) : w ∈ wmax G C j := by
  classical
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at ht
  obtain ⟨bound,op,below⟩ := ht
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro x hit litW
  apply below x
  apply (and_sides ao bound op x).mpr
  intro d
  by_cases same : d = b
  · subst d
    exact orStep_up (n:=n) List.length_ofFn (orReaches_reach j _ reach).1 hit
  · have other : d = 1-b := by fin_cases d <;> fin_cases b <;> first | exact (same rfl).elim | decide
    rw [other]
    exact reach_var_val x _ w (mem_orIn_reach w raw) litW

def fourClauses (n : ℕ) (C : Circuit) (j k : ℕ) (i : Fin 4) : Finset (Fin n) :=
  Fin.addCases (motive := fun _ : Fin (2+2) => Finset (Fin n))
    (side (n:=n) C j) (side (n:=n) C k) i

theorem four_semantics (ao : IsAO2 n C) (tf : TopForm G C) {j k : ℕ}
    (marked : junk G C = {j,k}) (jk : ¬ InCone n C j k) (kj : ¬ InCone n C k j) (x : Fin n → Bool) :
    (∀ i : Fin 4, lit (fourClauses n C j k i) x) ↔ gateVal n C j x = true ∧ gateVal n C k x = true := by
  have swap : junk G C = {k,j} := marked.trans (Finset.pair_comm _ _)
  have lcase (b : Fin 2) : fourClauses n C j k (Fin.castAdd 2 b) = side C j b := Fin.addCases_left _
  have rcase (b : Fin 2) : fourClauses n C j k (Fin.natAdd 2 b) = side C k b := Fin.addCases_right _
  rw [primitive_junk ao tf marked kj x,primitive_junk ao tf swap jk x]
  constructor
  · intro all
    exact ⟨fun b => by simpa only [lcase] using all (Fin.castAdd 2 b),
      fun b => by simpa only [rcase] using all (Fin.natAdd 2 b)⟩
  · rintro ⟨left,right⟩ i
    exact Fin.addCases (motive := fun z : Fin (2+2) => lit (fourClauses n C j k z) x)
      (fun b => by simpa only [lcase] using left b) (fun b => by simpa only [rcase] using right b) i

theorem merge_dichotomy (ao : IsAO2 n C) (tf : TopForm G C) {j k t : ℕ}
    (marked : junk G C = {j,k}) (jk : ¬ InCone n C j k) (kj : ¬ InCone n C k j)
    (top : t ∈ tops G C) (jt : InCone n C j t) (kt : InCone n C k t) :
    (∃ b : Fin 2, OrReaches n C (opnd C t b) j ∧ OrReaches n C (opnd C t b) k ∧
      side C t (1-b) ⊆ wmax G C j ∩ wmax G C k) ∨
    (∀ x : Fin n → Bool, (∀ i : Fin 4, lit (fourClauses n C j k i) x) → graphFun G ∅ x = true) := by
  obtain ⟨b,hb⟩ := reaches_one_side ao tf marked jk top jt
  obtain ⟨d,hd⟩ := reaches_one_side ao tf (marked.trans (Finset.pair_comm _ _)) kj top kt
  by_cases same : b = d
  · subst d
    refine Or.inl ⟨b,hb,hd,?_⟩
    intro v hv
    exact Finset.mem_inter.mpr ⟨same_side_vertex ao top b hb v hv, same_side_vertex ao top b hd v hv⟩
  · right
    intro x all
    obtain ⟨hitJ,hitK⟩ := (four_semantics ao tf marked jk kj x).mp all
    fin_cases b <;> fin_cases d
    · exact (same rfl).elim
    · exact opposite_cleans_product ao top hb hd x hitJ hitK
    · exact opposite_cleans_product ao top hd hb x hitK hitJ
    · exact (same rfl).elim

end G11Structure

namespace G11Structure

open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1490

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem in_operand_pos (ao : IsAO2 n C) {t u : ℕ} (bound : t < C.gates.length)
    (mem : u ∈ (gateAt C t).inputs) : ∃ b : Fin 2, opnd C t b = u := by
  obtain ⟨a,d,eq⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem bound))
  have split : u = a ∨ u = d := by simpa [eq] using mem
  rcases split with rfl | rfl
  · exact ⟨0,by simp [opnd,eq]⟩
  · exact ⟨1,by simp [opnd,eq]⟩

theorem raw_empty_at_and {g : ℕ} (op : (gateAt C g).op = GateOp.and) :
    orIn n C (n+g) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  rcases (mem_orIn_reach v hv).cases_head with eq | ⟨_,⟨i,_,ei,hi,_,_⟩,_⟩
  · have := v.isLt
    omega
  · have same : i = g := by omega
    subst i
    rw [op] at hi
    contradiction

theorem raw_empty_from_inputs {g : ℕ}
    (empty : ∀ u ∈ (gateAt C g).inputs, orIn n C u = ∅) : orIn n C (n+g) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  rcases (mem_orIn_reach v hv).cases_head with eq | ⟨u,⟨i,_,ei,_,mem,_⟩,path⟩
  · have := v.isLt
    omega
  · have same : i = g := by omega
    subst i
    have seen := reach_mem_orIn v path
    rw [empty u mem] at seen
    exact Finset.notMem_empty _ seen

theorem two_raw_empty {a b g : ℕ} (ao : IsAO2 n C) (hg : g < C.gates.length)
    (diff : a ≠ b) (ha : a ∈ (gateAt C g).inputs) (hb : b ∈ (gateAt C g).inputs)
    (ea : orIn n C a = ∅) (eb : orIn n C b = ∅) : orIn n C (n+g) = ∅ := by
  apply raw_empty_from_inputs
  obtain ⟨u,v,ins⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hg))
  intro w hw
  simp [ins] at ha hb hw
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hw with rfl | rfl <;> first
    | assumption
    | exact (diff rfl).elim

theorem witness_rare_reader (ao : IsAO2 n C) {w j : ℕ} (raw : (orIn n C w).Nonempty)
    (blocked : orIn n C (n+j) = ∅) (bad : ∃ x, gateVal n C j x = true ∧ graphFun G ∅ x = false)
    (path : Relation.ReflTransGen (OrStep n C) w (n+j)) :
    ∃ h, j < h ∧ h ∈ orN G C \ lam G C ∧ n+j ∈ (gateAt C h).inputs ∧
      Relation.ReflTransGen (OrStep n C) w (n+h) ∧
      ∃ x, gateVal n C h x = true ∧ graphFun G ∅ x = false := by
  classical
  rcases path.cases_tail with eq | ⟨u,prev,⟨h,bound,hu,op,mem,earlier⟩⟩
  · exact (raw.ne_empty (eq ▸ blocked)).elim
  · subst u
    obtain ⟨x,hit,miss⟩ := bad
    have on : gateVal n C h x = true := (val_or List.length_ofFn bound op).mpr ⟨n+j,mem,earlier,hit⟩
    have outside : ¬ BelowF G C h := fun clean => Bool.noConfusion (miss.symm.trans (clean x on))
    have inN : h ∈ orN G C := by
      simp only [orN,gatesWhere,Finset.mem_filter,Finset.mem_range]
      exact ⟨bound,op,outside⟩
    have apart : h ∉ lam G C := by
      intro inLam
      obtain ⟨_,nonemptyZero,nonemptyOne,_⟩ := Finset.mem_filter.mp inLam
      obtain ⟨b,eb⟩ := in_operand_pos ao bound mem
      have no : ¬ (orIn n C (opnd C h b)).Nonempty := fun z => z.ne_empty (eb.symm ▸ blocked)
      fin_cases b
      · exact no nonemptyZero
      · exact no nonemptyOne
    exact ⟨h,by omega,Finset.mem_sdiff.mpr ⟨inN,apart⟩,mem,prev,x,on,miss⟩

theorem two_rare_of_common_top (ao : IsAO2 n C) (tf : TopForm G C) {j k t : ℕ}
    (diff : j ≠ k) (marked : junk G C = {j,k}) (jk : ¬ InCone n C j k) (kj : ¬ InCone n C k j)
    (top : t ∈ tops G C) (jt : InCone n C j t) (kt : InCone n C k t)
    (centered : t ∉ centreless G C) : 2 ≤ (orN G C \ lam G C).card := by
  classical
  have nonempty (b : Fin 2) : (orIn n C (opnd C t b)).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro none
    apply centered
    apply Finset.mem_filter.mpr
    refine ⟨top,?_⟩
    fin_cases b
    · exact Or.inl none
    · exact Or.inr none
  obtain ⟨b,left⟩ := reaches_one_side ao tf marked jk top jt
  obtain ⟨d,right⟩ := reaches_one_side ao tf (marked.trans (Finset.pair_comm _ _)) kj top kt
  have jMem : j ∈ junk G C := by simp [marked]
  have kMem : k ∈ junk G C := by simp [marked]
  obtain ⟨_,opJ,_,badJ⟩ := Finset.mem_filter.mp jMem
  obtain ⟨_,opK,_,badK⟩ := Finset.mem_filter.mp kMem
  have jEmpty := raw_empty_at_and (n:=n) opJ
  have kEmpty := raw_empty_at_and (n:=n) opK
  obtain ⟨i,_,hi,readsJ,reachI,badI⟩ := witness_rare_reader ao (nonempty b) jEmpty badJ (orReaches_reach j _ left).1
  obtain ⟨i',_,hi',readsK,_,_⟩ := witness_rare_reader ao (nonempty d) kEmpty badK (orReaches_reach k _ right).1
  apply Finset.one_lt_card_iff.mpr
  by_cases eq : i = i'
  · subst i'
    have inN := (Finset.mem_sdiff.mp hi).1
    simp only [orN,gatesWhere,Finset.mem_filter,Finset.mem_range] at inN
    have bound : i < C.gates.length := inN.1
    have eI := two_raw_empty ao bound (show n+j ≠ n+k by omega) readsJ readsK jEmpty kEmpty
    obtain ⟨h,lt,good,_,_,_⟩ := witness_rare_reader ao (nonempty b) eI badI reachI
    exact ⟨i,h,hi,good,lt.ne⟩
  · exact ⟨i,i',hi,hi',eq⟩

end G11Structure
