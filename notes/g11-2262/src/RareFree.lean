import Structure

namespace G11Structure

open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1490

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem rare_free_direct (ao : IsAO2 n C) (rare : orN G C \ lam G C = ∅)
    {w j : ℕ} (hj : j ∈ junk G C) (reach : OrReaches n C w j) : w = n+j := by
  classical
  obtain ⟨_,opJ,_,x,hit,miss⟩ := Finset.mem_filter.mp hj
  rcases (orReaches_reach j _ reach).1.cases_tail with same | ⟨u,_,⟨h,hb,hu,op,mem,earlier⟩⟩
  · exact same.symm
  · have on : gateVal n C h x = true := (val_or List.length_ofFn hb op).mpr ⟨n+j,mem,earlier,hit⟩
    have outside : ¬ BelowF G C h := fun below => Bool.noConfusion (miss.symm.trans (below x on))
    have isN : h ∈ orN G C := by
      simp only [orN,gatesWhere,Finset.mem_filter,Finset.mem_range]
      exact ⟨hb,op,outside⟩
    have notLam : h ∉ lam G C := by
      intro inside
      obtain ⟨_,h₀,h₁,_⟩ := Finset.mem_filter.mp inside
      obtain ⟨b,eq⟩ := in_operand_pos ao hb mem
      have empty : orIn n C (opnd C h b) = ∅ := by rw [eq,raw_empty_at_and opJ]
      fin_cases b
      · exact h₀.ne_empty empty
      · exact h₁.ne_empty empty
    exact (Finset.notMem_empty h (rare ▸ Finset.mem_sdiff.mpr ⟨isN,notLam⟩)).elim

theorem rare_free_centreless (ao : IsAO2 n C) (rare : orN G C \ lam G C = ∅)
    {t j : ℕ} (top : t ∈ tops G C) (hj : j ∈ junk G C)
    (b : Fin 2) (reach : OrReaches n C (opnd C t b) j) : t ∈ centreless G C := by
  classical
  have eq := rare_free_direct ao rare hj reach
  have empty : side (n:=n) C t b = ∅ := by
    unfold side
    rw [eq]
    exact raw_empty_at_and (Finset.mem_filter.mp hj).2.1
  apply Finset.mem_filter.mpr
  refine ⟨top,?_⟩
  fin_cases b
  · exact Or.inl empty
  · exact Or.inr empty

theorem rare_free_joint {j k t : ℕ} (ao : IsAO2 n C) (tf : TopForm G C)
    (marked : junk G C = {j,k}) (jk : ¬ InCone n C j k) (kj : ¬ InCone n C k j)
    (top : t ∈ tops G C) (jt : InCone n C j t) (kt : InCone n C k t)
    (rare : orN G C \ lam G C = ∅) (few : (centreless G C).card ≤ 1)
    (source : ∀ u v : Fin n, s(u,v) ∈ Ustar G C → ∃ z ∈ tops G C, ∃ b : Fin 2, ∃ i : ℕ,
      (i = j ∨ i = k) ∧ gateVal n C z (pairInput u v) = true ∧
      OrReaches n C (opnd C z b) i ∧ gateVal n C i (pairInput u v) = true) :
    ∀ u v : Fin n, s(u,v) ∈ Ustar G C →
      gateVal n C j (pairInput u v) = true ∧ gateVal n C k (pairInput u v) = true := by
  classical
  obtain ⟨b,hb⟩ := reaches_one_side ao tf marked jk top jt
  obtain ⟨d,hd⟩ := reaches_one_side ao tf (marked.trans (Finset.pair_comm _ _)) kj top kt
  have jMem : j ∈ junk G C := by simp [marked]
  have kMem : k ∈ junk G C := by simp [marked]
  have jWire := rare_free_direct ao rare jMem hb
  have kWire := rare_free_direct ao rare kMem hd
  have tCent := rare_free_centreless ao rare top jMem b hb
  intro u v edge
  obtain ⟨z,zTop,b',i,which,hit,reached,_⟩ := source u v edge
  have iMem : i ∈ junk G C := which.elim (fun eq => eq.symm ▸ jMem) (fun eq => eq.symm ▸ kMem)
  have zCent := rare_free_centreless ao rare zTop iMem b' reached
  have eqzt := Finset.card_le_one_iff.mp few zCent tCent
  subst z
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at top
  have both := (and_sides ao top.1 top.2.1 (pairInput u v)).mp hit
  exact ⟨by simpa only [jWire,wireVal,gateVal] using both b,
    by simpa only [kWire,wireVal,gateVal] using both d⟩

theorem cross_residual {a : ℕ} (atop : a ∈ tops G C)
    (sides : ∀ a ∈ tops G C, ∀ u ∈ side C a 0, ∀ v ∈ side C a 1, G.Adj u v)
    {u v : Fin n} (hu : u ∈ side C a 0) (hv : v ∈ side C a 1) :
    (G.deleteEdges (Ustar G C : Set _)).Adj u v := by
  apply SimpleGraph.deleteEdges_adj.mpr
  refine ⟨sides a atop u hu v hv,?_⟩
  intro missing
  have present : s(u,v) ∈ starEdges G C := Finset.mem_biUnion.mpr
    ⟨a,atop,Finset.mem_image.mpr ⟨(u,v),Finset.mem_product.mpr ⟨hu,hv⟩,rfl⟩⟩
  exact (Finset.mem_sdiff.mp missing).2 present

theorem rare_free_raw_clause (ao : IsAO2 n C) (rare : orN G C \ lam G C = ∅)
    (sides : ∀ a ∈ tops G C, ∀ u ∈ side C a 0, ∀ v ∈ side C a 1, G.Adj u v) (w : ℕ) :
    (orIn n C w).card ≤ 1 ∨ ∃ c : Fin n, ∀ v ∈ orIn n C w,
      (G.deleteEdges (Ustar G C : Set _)).Adj c v := by
  classical
  by_cases few : (orIn n C w).card ≤ 1
  · exact Or.inl few
  right
  obtain ⟨u,v,hu,hv,diff⟩ := Finset.one_lt_card_iff.mp (Nat.lt_of_not_ge few)
  have wire : ∃ k, k < C.gates.length ∧ w = n+k := by
    by_contra none
    have mustEq (z : Fin n) (hz : z ∈ orIn n C w) : w = z.val := by
      rcases (mem_orIn_reach z hz).cases_head with eq | ⟨_,⟨k,hk,eq,_,_,_⟩,_⟩
      · exact eq
      · exact (none ⟨k,hk,eq⟩).elim
    exact diff (Fin.ext ((mustEq u hu).symm.trans (mustEq v hv)))
  obtain ⟨k,hk,rfl⟩ := wire
  have op : (gateAt C k).op = GateOp.or := by
    rcases ao.1 _ (gateAt_mem hk) with prod | plus
    · have empty := raw_empty_at_and (n:=n) prod
      rw [empty] at hu
      exact (Finset.notMem_empty _ hu).elim
    · exact plus
  have outside : ¬ BelowF G C k := by
    intro below
    have on : gateVal n C k (pairInput u u) = true :=
      reach_var_val (pairInput u u) _ u (mem_orIn_reach u hu) (pairInput_left u u)
    exact G.irrefl ((graphFun_pair G u u).mp (below _ on))
  have inN : k ∈ orN G C := by
    simp only [orN,gatesWhere,Finset.mem_filter,Finset.mem_range]
    exact ⟨hk,op,outside⟩
  have inL : k ∈ lam G C := by
    by_contra outL
    have mem := Finset.mem_sdiff.mpr ⟨inN,outL⟩
    rw [rare] at mem
    exact Finset.notMem_empty _ mem
  obtain ⟨_,_,_,a,atop,b,one,path⟩ := Finset.mem_filter.mp inL
  obtain ⟨c,sideC⟩ := Finset.card_eq_one.mp one
  refine ⟨c,?_⟩
  intro z hz
  have inLeaves : z ∈ side C a b := reach_mem_orIn z
    ((orReaches_reach k _ path).1.trans (mem_orIn_reach z hz))
  have own : c ∈ side C a (1-b) := sideC.symm ▸ Finset.mem_singleton_self c
  fin_cases b
  · exact (cross_residual atop sides inLeaves own).symm
  · exact cross_residual atop sides own inLeaves

end G11Structure
