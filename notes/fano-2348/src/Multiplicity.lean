import NativeNormal

namespace FanoDeskNormal

open SignatureNormal

/-- Given at most one occurrence in the initial wires, the second occurrence
    is the output of a gate whose prefix already contains the signature. -/
private theorem second_output (w : List Sig) (gs : List (Gate Sig)) (x : Sig)
    (start : w.count x ≤ 1) (twice : 1 < (w++gs.map Gate.out).count x) :
    ∃ pre g rest, gs=pre++g::rest ∧ g.out=x ∧ 0<(w++pre.map Gate.out).count x := by
  induction gs generalizing w with
  | nil => simp at twice; omega
  | cons g gs ih =>
    by_cases found : g.out=x ∧ 0<w.count x
    · exact ⟨[],g,gs,rfl,found.1,by simpa using found.2⟩
    have next : (w++[g.out]).count x ≤ 1 := by
      by_cases same : g.out=x
      · have none : w.count x=0 := by by_contra! h; exact found ⟨same,by omega⟩
        simp [same,none]
      · simpa [same] using start
    have twice' : 1 < ((w++[g.out])++gs.map Gate.out).count x := by
      simpa only [List.append_assoc,List.singleton_append,List.map_cons] using twice
    obtain ⟨pre,h,rest,rfl,eq,old⟩ := ih _ next twice'
    exact ⟨g::pre,h,rest,rfl,eq,by simpa only [List.append_assoc,List.singleton_append,List.map_cons] using old⟩

theorem normalize_multiplicity (first : Sig) (s : List Sig) (yes : posted (first::s)) :
    ∃ t : List Sig, t.length ≤ s.length ∧ posted (first::t) ∧
      ∀ x : Sig, (seed++first::t).count x ≤ 2 ∧
        (1 < (seed++first::t).count x → ∃ y ∈ t, y≠x ∧ y=conj x x) := by
  obtain ⟨t,le,ok,cap,gs,rfl,short⟩ := normalize first s yes
  refine ⟨_,le,ok,fun x => ⟨cap x,?_⟩⟩
  intro twice
  obtain ⟨a,b,ab,eq⟩ := ((posted_cons _ _).mp ok).1
  have fresh : first ∉ seed := eq ▸ first_disjunction_fresh a b ab
  have initial : (seed++[first]).count x ≤ 1 := by
    by_cases same : first=x
    · subst x
      simp [List.count_eq_zero.mpr fresh]
    · simpa [same] using List.nodup_iff_count_le_one.mp seed_nodup x
  obtain ⟨pre,g,rest,rfl,out,old⟩ := second_output (seed++[first]) gs x initial
    (by simpa [List.append_assoc] using twice)
  subst x
  obtain ⟨⟨use,member,_,_,computes,different⟩,_⟩ := necessary_AND pre g rest short old
  exact ⟨use.out,List.mem_map.mpr ⟨use,List.mem_append_right _ (List.mem_cons_of_mem _ member),rfl⟩,
    different,computes⟩

end FanoDeskNormal

#print axioms FanoDeskNormal.normalize_multiplicity
