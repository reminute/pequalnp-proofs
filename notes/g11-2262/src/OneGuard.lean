import RareGuards

namespace G11Residual

open G11Certificate G11FourClauses G11Structure
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

abbrev Sample := Fin 11 → Bool
def negInput (z : Fin 24) (v : Fin 11) : Bool := decide (v ∈ negative z)
def edgeInput (e : Fin 16) : Sample := pairInput (edgeAt e).1 (edgeAt e).2

theorem negative_off (z : Fin 24) : graphFun graph ∅ (negInput z) = false := by
  cases on : graphFun graph ∅ (negInput z) with
  | false => rfl
  | true =>
    simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,
      decide_eq_true_eq,negInput] at on
    obtain ⟨u,v,adj,hu,hv⟩ := on
    exact (graph_independent z u v hu hv adj).elim

theorem positive_lit (A : Finset (Fin 11)) (e : Fin 16) :
    lit A (edgeInput e) ↔ ¬Disjoint (edge e) A := by
  constructor
  · rintro ⟨v,hv,on⟩
    exact Finset.not_disjoint_iff.mpr ⟨v,by simpa [edge,edgeInput,pairInput] using on,hv⟩
  · intro h
    obtain ⟨v,on,hv⟩ := Finset.not_disjoint_iff.mp h
    exact ⟨v,hv,by simpa [edge,edgeInput,pairInput] using on⟩

theorem negative_lit (A : Finset (Fin 11)) (z : Fin 24) :
    lit A (negInput z) ↔ ¬Disjoint A (negative z) := by
  simp [lit,negInput, Finset.not_disjoint_iff]

def allHits (U : Finset (Fin 16)) (A : Finset (Fin 11)) : Prop := ∀ e ∈ U, ¬Disjoint (edge e) A

def capture (U : Finset (Fin 16)) (Y : Finset (Fin 24)) : Finset (Fin 16) :=
  U.filter fun e => (∃ z ∈ Y, (edgeAt e).1 ∈ negative z) ∧ (∃ z ∈ Y, (edgeAt e).2 ∈ negative z)

def obstruction (U : Finset (Fin 16)) : Prop := ∃ Y : Finset (Fin 24), ∃ z ∈ Y,
  (∀ y ∈ Y, ∀ A, G11Protected.allowed U A → allHits U A → ¬ Disjoint A (negative y)) ∧
  (∀ B, G11Protected.allowed U B → allHits (capture U Y) B → ¬ Disjoint B (negative z))

theorem forbid_one_guard (U : Finset (Fin 16)) (X K : Sample → Prop)
    (A B : Fin 2 → Finset (Fin 11)) (Q : Finset (Fin 11))
    (allowA : ∀ b, G11Protected.allowed U (A b)) (allowB : ∀ b, G11Protected.allowed U (B b))
    (xForm : ∀ x, X x ↔ ∀ b, lit (A b) x) (kForm : ∀ x, K x ↔ ∀ b, lit (B b) x)
    (clean : ∀ x, X x → K x → graphFun graph ∅ x = true)
    (guardClean : ∀ x, X x → lit Q x → graphFun graph ∅ x = true)
    (pos : ∀ e ∈ U, X (edgeInput e) ∧ (K (edgeInput e) ∨ lit Q (edgeInput e)))
    (blocked : obstruction U) : False := by
  obtain ⟨Y,z,zY,first,second⟩ := blocked
  have xNeg (y : Fin 24) (hy : y ∈ Y) : X (negInput y) := by
    apply (xForm _).mpr
    intro b
    apply (negative_lit _ _).mpr
    apply first y hy _ (allowA b)
    intro e he
    exact (positive_lit _ _).mp ((xForm _).mp (pos e he).1 b)
  have noQ (w : Fin 11) (y : Fin 24) (hy : y ∈ Y) (hw : w ∈ negative y) : w ∉ Q := by
    intro inQ
    have fail := guardClean _ (xNeg y hy) ⟨w,inQ,decide_eq_true hw⟩
    rw [negative_off y] at fail
    contradiction
  have kNeg : K (negInput z) := by
    apply (kForm _).mpr
    intro b
    apply (negative_lit _ _).mpr
    apply second _ (allowB b)
    intro e he
    obtain ⟨inU,⟨y,hy,ey⟩,⟨y',hy',ey'⟩⟩ := Finset.mem_filter.mp he
    have noLit : ¬ lit Q (edgeInput e) := by
      rintro ⟨w,hw,on⟩
      have eq : w=(edgeAt e).1 ∨ w=(edgeAt e).2 := by simpa [edgeInput,pairInput] using on
      rcases eq with rfl | rfl
      · exact noQ _ y hy ey hw
      · exact noQ _ y' hy' ey' hw
    have onK := (pos e inU).2.resolve_right noLit
    exact (positive_lit _ _).mp ((kForm _).mp onK b)
  have impossible := clean _ (xNeg z zY) kNeg
  rw [negative_off z] at impossible
  contradiction

theorem singleton_guard_profile {C : Circuit} {j k : ℕ} (S : Finset Guard) (few : S.card ≤ 1)
    (guardsSafe : ∀ g ∈ S, safe C j k g)
    (coverage : ∀ e ∈ residualIndices C, e ∈ jointEdges C j k ∨
      ∃ g ∈ S, acceptsGuard C j k g (edgeInput e)) :
    ∃ g : Guard, safe C j k g ∧ ∀ e ∈ residualIndices C,
      gateVal 11 C (chosen j k g.1) (edgeInput e) = true ∧
      (gateVal 11 C (chosen j k (!g.1)) (edgeInput e) = true ∨ lit g.2 (edgeInput e)) := by
  classical
  obtain ⟨g,safeG,only⟩ : ∃ g, safe C j k g ∧ ∀ g' ∈ S, g'=g := by
    rcases S.eq_empty_or_nonempty with rfl | ⟨g,hg⟩
    · refine ⟨(false,∅),?_,by simp⟩
      rintro x _ ⟨v,hv,_⟩
      exact (Finset.notMem_empty v hv).elim
    · exact ⟨g,guardsSafe g hg,fun g' hg' => Finset.card_le_one_iff.mp few hg' hg⟩
  refine ⟨g,safeG,?_⟩
  intro e he
  rcases coverage e he with pair | ⟨g',hg',hit⟩
  · have joint := (Finset.mem_filter.mp pair).2
    change gateVal 11 C j (edgeInput e) = true ∧ gateVal 11 C k (edgeInput e) = true at joint
    cases g.1 <;> simp [chosen,joint]
  · rcases only g' hg' with rfl
    exact ⟨hit.1,Or.inr hit.2⟩

theorem forbidden_profile {C : Circuit} {j k : ℕ} (ao : IsAO2 11 C) (tf : TopForm graph C)
    (rare : orN graph C \ lam graph C = ∅) (marked : junk graph C = {j,k})
    (jk : ¬ InCone 11 C j k) (kj : ¬ InCone 11 C k j)
    (sides : ∀ a ∈ tops graph C, ∀ u ∈ side C a 0, ∀ v ∈ side C a 1, graph.Adj u v)
    (clean : ∀ x, gateVal 11 C j x = true → gateVal 11 C k x = true → graphFun graph ∅ x = true)
    (S : Finset Guard) (few : S.card ≤ 1) (guardsSafe : ∀ g ∈ S, safe C j k g)
    (coverage : ∀ e ∈ residualIndices C, e ∈ jointEdges C j k ∨ ∃ g ∈ S, acceptsGuard C j k g (edgeInput e))
    (blocked : obstruction (residualIndices C)) : False := by
  obtain ⟨⟨flag,Q⟩,safeQ,yes⟩ := singleton_guard_profile S few guardsSafe coverage
  let X := chosen j k flag
  let K := chosen j k (!flag)
  have f (g : ℕ) (gw : g = j ∨ g = k) (x : Sample) :
      gateVal 11 C g x = true ↔ ∀ b : Fin 2, lit (side C g b) x := by
    rcases gw with rfl | rfl
    · exact primitive_junk ao tf marked kj x
    · exact primitive_junk ao tf (marked.trans (Finset.pair_comm _ _)) jk x
  have firstEq : X=j ∨ X=k := by cases flag <;> simp [X,chosen]
  have secondEq : K=j ∨ K=k := by cases flag <;> simp [K,chosen]
  apply forbid_one_guard (residualIndices C)
    (fun x => gateVal 11 C X x = true) (fun x => gateVal 11 C K x = true)
    (side C X) (side C K) Q
    (fun b => allowed_wire C ao rare sides (opnd C X b))
    (fun b => allowed_wire C ao rare sides (opnd C K b))
    (f X firstEq) (f K secondEq) _ safeQ yes blocked
  intro x hx hk
  cases flag
  · exact clean x hx hk
  · exact clean x hk hx

end G11Residual
