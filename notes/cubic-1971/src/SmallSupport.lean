import PartnerCertificate

namespace Cubic1971.SmallSupport

open PartnerCertificate

variable {n : Nat} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {v : Fin n}

def Supported (v : Fin n) (K : Finset (Fin n)) (p : Finset (Fin n) → Bool) : Prop :=
  ∀ S T, v ∉ S → v ∉ T → (∀ x ∈ K, x ∈ S ↔ x ∈ T) → p S = p T

/-- Only the intersection with the support can explain a blocking value.
    The rest of the row can contain arbitrary marks or edges. -/
theorem local_enable (p : Finset (Fin n) → Bool) (pass : Bool)
    (enabled : ∀ S, sensitive G A v S → p S = pass)
    (ordinary : ∀ {u w}, G.Adj u w → u ∉ A)
    (girth : GirthEdgeNegatives.GirthFive G) (degree : (G.neighborSet v).ncard = 3)
    (K : Finset (Fin n)) (small : K.card ≤ 2) (support : Supported v K p)
    (S : Finset (Fin n)) (away : v ∉ S) (good : clean A (K ∩ S)) (ind : free G (K ∩ S)) :
    p S = pass := by
  classical
  have away' : v ∉ K ∩ S := fun h => away (Finset.mem_inter.mp h).2
  have eq := support S (K ∩ S) away away' (fun u h => by simp [h])
  exact eq.trans (supported_pair p pass enabled ordinary girth degree K small support _ away' good ind)

/-- A partner depending on two ordinary raw coordinates is either constantly
    enabled or blocks exactly on the positive edge between those coordinates. -/
theorem ordinary_pair (p : Finset (Fin n) → Bool) (pass : Bool)
    (enabled : ∀ S, sensitive G A v S → p S = pass)
    (ordinary : ∀ {u w}, G.Adj u w → u ∉ A)
    (girth : GirthEdgeNegatives.GirthFive G) (degree : (G.neighborSet v).ncard = 3)
    (a b : Fin n) (av : a ≠ v) (bv : b ≠ v) (goodA : a ∉ A) (goodB : b ∉ A)
    (support : Supported v {a, b} p) :
    (∀ S, v ∉ S → p S = pass) ∨
    (G.Adj a b ∧ ∀ S, v ∉ S →
      p S = if a ∈ S ∧ b ∈ S then !pass else pass) := by
  classical
  let K : Finset (Fin n) := {a,b}
  have small : K.card ≤ 2 := Finset.card_le_two
  have cleanK : clean A K := by
    intro u mem
    rcases (show u = a ∨ u = b by simpa [K] using mem) with rfl | rfl
    · exact goodA
    · exact goodB
  have defaultVal (S : Finset (Fin n)) (away : v ∉ S)
      (h : ¬(G.Adj a b ∧ a ∈ S ∧ b ∈ S)) : p S = pass := by
    apply local_enable p pass enabled @ordinary girth degree K small support S away
    · exact fun u mem => cleanK u (Finset.mem_inter.mp mem).1
    · intro u hu w hw adj
      obtain ⟨uk,us⟩ := Finset.mem_inter.mp hu
      obtain ⟨wk,ws⟩ := Finset.mem_inter.mp hw
      simp only [K,Finset.mem_insert,Finset.mem_singleton] at uk wk
      rcases uk with rfl | rfl <;> rcases wk with rfl | rfl
      · exact G.irrefl adj
      · exact h ⟨adj,us,ws⟩
      · exact h ⟨adj.symm,ws,us⟩
      · exact G.irrefl adj
  by_cases edge : G.Adj a b
  · have awayK : v ∉ K := by simp [K,Ne.symm av,Ne.symm bv]
    have full (S : Finset (Fin n)) (away : v ∉ S) (ha : a ∈ S) (hb : b ∈ S) : p S = p K := by
      apply support S K away awayK
      intro u uk
      have hit : u ∈ S := by
        rcases (show u = a ∨ u = b by simpa [K] using uk) with rfl | rfl
        · exact ha
        · exact hb
      simp [uk,hit,K] at *
    by_cases agrees : p K = pass
    · left
      intro S away
      by_cases both : a ∈ S ∧ b ∈ S
      · exact (full S away both.1 both.2).trans agrees
      · exact defaultVal S away (fun yes => both yes.2)
    · right
      refine ⟨edge, fun S away => ?_⟩
      split_ifs with both
      · rw [full S away both.1 both.2]
        cases h : p K <;> cases pass <;> simp_all
      · exact defaultVal S away (fun yes => both yes.2)
  · exact Or.inl (fun S away => defaultVal S away (fun yes => edge yes.1))

end Cubic1971.SmallSupport

#print axioms Cubic1971.SmallSupport.ordinary_pair
