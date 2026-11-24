import NoRareBound

namespace G11Residual

open G11Certificate G11FourClauses G11Structure
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

abbrev Guard := Bool × Finset (Fin 11)

def chosen (j k : ℕ) (b : Bool) : ℕ := if b then k else j

def safe (C : Circuit) (j k : ℕ) (g : Guard) : Prop :=
  ∀ x : Fin 11 → Bool, gateVal 11 C (chosen j k g.1) x = true →
    lit g.2 x → graphFun graph ∅ x = true

def acceptsGuard (C : Circuit) (j k : ℕ) (g : Guard) (x : Fin 11 → Bool) : Prop :=
  gateVal 11 C (chosen j k g.1) x = true ∧ lit g.2 x

def seen (C : Circuit) (z : ℕ) : Prop :=
  ∃ b : Fin 2, ∃ i ∈ junk graph C, OrReaches 11 C (opnd C z b) i

theorem position_pair (b d : Fin 2) : d=b ∨ d=1-b := by
  fin_cases b <;> fin_cases d <;> decide

theorem allowed_wire (C : Circuit) (ao : IsAO2 11 C) (rare : orN graph C \ lam graph C = ∅)
    (sides : ∀ a ∈ tops graph C, ∀ u ∈ side C a 0, ∀ v ∈ side C a 1, graph.Adj u v)
    (w : ℕ) : G11Protected.allowed (residualIndices C) (orIn 11 C w) := by
  rcases rare_free_raw_clause ao rare sides w with small | ⟨c,adj⟩
  · exact Or.inl (Finset.card_le_one_iff_subset_singleton.mp small)
  · exact Or.inr ⟨c,fun v hv => neighbors_index C c v (adj _ hv)⟩

theorem guard_for_top {C : Circuit} {j k z : ℕ} (ao : IsAO2 11 C) (tf : TopForm graph C)
    (rare : orN graph C \ lam graph C = ∅) (marked : junk graph C = {j,k})
    (sides : ∀ a ∈ tops graph C, ∀ u ∈ side C a 0, ∀ v ∈ side C a 1, graph.Adj u v)
    (zt : z ∈ tops graph C) :
    ∃ g : Guard, G11Protected.allowed (residualIndices C) g.2 ∧ safe C j k g ∧
      ∀ x, seen C z → gateVal 11 C z x = true →
        (gateVal 11 C j x = true ∧ gateVal 11 C k x = true) ∨ acceptsGuard C j k g x := by
  classical
  have emptyAllowed : G11Protected.allowed (residualIndices C) ∅ := Or.inl ⟨0,Finset.empty_subset _⟩
  have emptySafe : safe C j k (false,∅) := by
    rintro x _ ⟨v,h,_⟩
    exact (Finset.notMem_empty v h).elim
  by_cases anySeen : seen C z
  · obtain ⟨b,i,hI,more⟩ := anySeen
    have direct := rare_free_direct ao rare hI more
    have facts := zt
    simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at facts
    obtain ⟨bound,op,below⟩ := facts
    have markedI : i = j ∨ i = k := by simpa [marked] using hI
    obtain ⟨flag,choice⟩ : ∃ flag : Bool, chosen j k flag = i := by
      rcases markedI with rfl | rfl
      · exact ⟨false,rfl⟩
      · exact ⟨true,rfl⟩
    by_cases mixed : ∃ a ∈ junk graph C, OrReaches 11 C (opnd C z (1-b)) a
    · obtain ⟨a,hA,reachA⟩ := mixed
      have aWire := rare_free_direct ao rare hA reachA
      have diff : i ≠ a := by
        rintro rfl
        apply no_dirty_both_sides ao zt hI
        fin_cases b
        · exact ⟨more,reachA⟩
        · exact ⟨reachA,more⟩
      have markedA : a = j ∨ a = k := by simpa [marked] using hA
      refine ⟨(false,∅),emptyAllowed,emptySafe,?_⟩
      intro x _ onZ
      have on := (and_sides ao bound op x).mp onZ
      have hi : gateVal 11 C i x = true := by simpa only [direct,gateVal,wireVal] using on b
      have ha : gateVal 11 C a x = true := by simpa only [aWire,gateVal,wireVal] using on (1-b)
      left
      rcases markedI with rfl | rfl <;> rcases markedA with rfl | rfl <;> first
        | exact (diff rfl).elim
        | exact ⟨hi,ha⟩
        | exact ⟨ha,hi⟩
    · let Q := side (n:=11) C z (1-b)
      refine ⟨(flag,Q),allowed_wire C ao rare sides (opnd C z (1-b)),?_,?_⟩
      · intro x hi raw
        change gateVal 11 C (chosen j k flag) x = true at hi
        rw [choice] at hi
        apply below x
        apply (and_sides ao bound op x).mpr
        intro d
        rcases position_pair b d with rfl | rfl
        · simpa only [direct,gateVal,wireVal] using hi
        · exact (operand_iff ao tf bound op _ x).mpr (Or.inl raw)
      · intro x _ onZ
        have on := (and_sides ao bound op x).mp onZ
        right
        refine ⟨?_,?_⟩
        · change gateVal 11 C (chosen j k flag) x = true
          rw [choice]
          simpa only [direct,gateVal,wireVal] using on b
        · exact ((operand_iff ao tf bound op _ x).mp (on (1-b))).resolve_right
            (fun ⟨a,ha,reached,_⟩ => mixed ⟨a,ha,reached⟩)
  · exact ⟨(false,∅),emptyAllowed,emptySafe,fun _ h _ => (anySeen h).elim⟩

theorem residual_guards {C : Circuit} {j k t : ℕ} (ao : IsAO2 11 C) (tf : TopForm graph C)
    (rare : orN graph C \ lam graph C = ∅) (distinct : j ≠ k)
    (marked : junk graph C = {j,k}) (jk : ¬ InCone 11 C j k) (kj : ¬ InCone 11 C k j)
    (sides : ∀ a ∈ tops graph C, ∀ u ∈ side C a 0, ∀ v ∈ side C a 1, graph.Adj u v)
    (zt : t ∈ tops graph C) (jt : InCone 11 C j t) (kt : InCone 11 C k t)
    (source : ∀ u v : Fin 11, s(u,v) ∈ Ustar graph C → ∃ z ∈ tops graph C, ∃ b : Fin 2, ∃ i : ℕ,
      (i = j ∨ i = k) ∧ gateVal 11 C z (pairInput u v) = true ∧
      OrReaches 11 C (opnd C z b) i ∧ gateVal 11 C i (pairInput u v) = true) :
    (∀ x : Fin 11 → Bool, gateVal 11 C j x = true → gateVal 11 C k x = true → graphFun graph ∅ x = true) ∧
    ∃ guards : Finset Guard, guards.card ≤ (centreless graph C).card-1 ∧
      (∀ g ∈ guards, G11Protected.allowed (residualIndices C) g.2 ∧ safe C j k g) ∧
      ∀ e ∈ residualIndices C, e ∈ jointEdges C j k ∨
        ∃ g ∈ guards, acceptsGuard C j k g (pairInput (edgeAt e).1 (edgeAt e).2) := by
  classical
  obtain ⟨jMem,kMem⟩ : j ∈ junk graph C ∧ k ∈ junk graph C := by simp [marked]
  obtain ⟨b,hb⟩ := reaches_one_side ao tf marked jk zt jt
  obtain ⟨d,hd⟩ := reaches_one_side ao tf (marked.trans (Finset.pair_comm _ _)) kj zt kt
  have bj := rare_free_direct ao rare jMem hb
  have dk := rare_free_direct ao rare kMem hd
  have tCent := rare_free_centreless ao rare zt jMem b hb
  have clean := (merge_dichotomy ao tf marked jk kj zt jt kt).resolve_left (by
    rintro ⟨p,pj,pk,_⟩
    have e₁ := rare_free_direct ao rare jMem pj
    have e₂ := rare_free_direct ao rare kMem pk
    omega)
  refine ⟨fun x hi hk => clean x ((four_semantics ao tf marked jk kj x).mpr ⟨hi,hk⟩),?_⟩
  let S := (centreless graph C).erase t
  have spec (z : ℕ) (hz : z ∈ S) := guard_for_top ao tf rare marked sides
    (Finset.mem_filter.mp (Finset.mem_erase.mp hz).2).1
  let f (z : ℕ) : Guard := if hz : z ∈ S then (spec z hz).choose else (false,∅)
  have good (z : ℕ) (hz : z ∈ S) : f z = (spec z hz).choose := by simp [f,hz]
  refine ⟨S.image f,Finset.card_image_le.trans_eq (Finset.card_erase_of_mem tCent),?_,?_⟩
  · intro g hg
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hg
    rw [good z hz]
    exact ⟨(spec z hz).choose_spec.1,(spec z hz).choose_spec.2.1⟩
  · intro e he
    let x := pairInput (edgeAt e).1 (edgeAt e).2
    obtain ⟨z,top,p,i,which,hit,reach,_⟩ := source (edgeAt e).1 (edgeAt e).2 (Finset.mem_filter.mp he).2
    have iMem : i ∈ junk graph C := by simpa only [marked,Finset.mem_insert,Finset.mem_singleton] using which
    by_cases same : z=t
    · subst z
      have ht := top
      simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at ht
      have on := (and_sides ao ht.1 ht.2.1 x).mp hit
      exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [bj,wireVal,gateVal] using on b,
        by simpa only [dk,wireVal,gateVal] using on d⟩)
    · have hz : z ∈ S := Finset.mem_erase.mpr ⟨same,rare_free_centreless ao rare top iMem p reach⟩
      rcases (spec z hz).choose_spec.2.2 x ⟨p,i,iMem,reach⟩ hit with joint | guardHit
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,joint⟩)
      · exact Or.inr ⟨f z,Finset.mem_image_of_mem f hz,good z hz ▸ guardHit⟩

end G11Residual
