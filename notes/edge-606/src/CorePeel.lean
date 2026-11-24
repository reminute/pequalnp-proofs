import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

namespace GirthFiveCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def ends (S : Finset (Sym2 V)) : Finset V := univ.filter fun v => ∃ e ∈ S, v ∈ e
def atVertex (S : Finset (Sym2 V)) (v : V) : Finset (Sym2 V) := S.filter fun e => v ∈ e

/-- Peeling low-degree vertices charges every removed edge to one removed
    vertex. The bound also retains the number of vertices of the final core. -/
theorem peel (D : ℕ) (S : Finset (Sym2 V)) :
    ∃ T ⊆ S, (∀ v, (atVertex T v).card = 0 ∨ D < (atVertex T v).card) ∧
      S.card + D*(ends T).card ≤ T.card + D*(ends S).card := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases all : ∀ v, (atVertex S v).card = 0 ∨ D < (atVertex S v).card
    · exact ⟨S,Subset.rfl,all,le_rfl⟩
    push Not at all
    obtain ⟨v,on,low⟩ := all
    let rest := S \ atVertex S v
    have inc : atVertex S v ⊆ S := filter_subset _ _
    have d : 0 < (atVertex S v).card := Nat.pos_of_ne_zero on
    have nrest : rest.card + (atVertex S v).card = S.card := card_sdiff_add_card_eq_card inc
    have sub : rest ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset,fun same => by
      have := congrArg Finset.card same
      omega⟩
    obtain ⟨T,tRest,core,cost⟩ := ih rest sub
    have incl : ends rest ⊆ ends S := by
      intro w hw
      obtain ⟨e,he,x⟩ := (mem_filter.mp hw).2
      exact mem_filter.mpr ⟨mem_univ _,e,(mem_sdiff.mp he).1,x⟩
    have vS : v ∈ ends S := by
      obtain ⟨e,he⟩ := card_pos.mp d
      exact mem_filter.mpr ⟨mem_univ _,e,(mem_filter.mp he).1,(mem_filter.mp he).2⟩
    have vRest : v ∉ ends rest := by
      intro hv
      obtain ⟨e,he,ev⟩ := (mem_filter.mp hv).2
      obtain ⟨inS,left⟩ := mem_sdiff.mp he
      exact left (mem_filter.mpr ⟨inS,ev⟩)
    have strict : (ends rest).card < (ends S).card := card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨incl,fun eq => vRest (eq ▸ vS)⟩)
    have scaled := Nat.mul_le_mul_left D (Nat.succ_le_of_lt strict)
    rw [Nat.mul_succ] at scaled
    exact ⟨T,tRest.trans sub.le,core,by omega⟩

theorem ends_edges (G : SimpleGraph V) [DecidableRel G.Adj] :
    ends G.edgeFinset = G.support.toFinset := by
  ext v
  simp only [ends,mem_filter,mem_univ,true_and,Set.mem_toFinset,SimpleGraph.mem_edgeFinset]
  constructor
  · rintro ⟨e,edge,mem⟩
    induction e using Sym2.inductionOn with
    | _ a b =>
      change G.Adj a b at edge
      rcases Sym2.mem_iff.mp mem with rfl | rfl
      · exact ⟨b,edge⟩
      · exact ⟨a,edge.symm⟩
  · rintro ⟨w,adj⟩
    exact ⟨s(v,w),adj,by simp⟩

end GirthFiveCore
