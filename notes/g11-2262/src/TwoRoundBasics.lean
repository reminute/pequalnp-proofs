import TwoRoundData

namespace G11TwoRounds

open G11Protected G11Certificate

def Hits (V : Finset (Fin 16)) (A : Finset (Fin 11)) : Prop :=
  ∀ e ∈ V, ¬ Disjoint (edge e) A

def captured (U : Finset (Fin 16)) (Y : Finset (Fin 24)) : Finset (Fin 16) :=
  U.filter fun e => edge e ⊆ Y.biUnion negative

theorem captured_mono {U V : Finset (Fin 16)} (sub : U ⊆ V) (Y : Finset (Fin 24)) :
    captured U Y ⊆ captured V Y := fun _ h =>
  Finset.mem_filter.mpr ⟨sub (Finset.mem_filter.mp h).1,(Finset.mem_filter.mp h).2⟩

def blocks (lo need : Finset (Fin 16)) (z : Fin 24) : Prop :=
  (∀ c : Fin 11, obstructs need z {c}) ∧
    ∀ c : Fin 11, obstructs need z (neighbors lo c)

instance (lo need : Finset (Fin 16)) (z : Fin 24) : Decidable (blocks lo need z) := by
  unfold blocks; infer_instance

def validHint (h : Hint) : Prop :=
  h.z ∈ h.rows ∧ (∀ y ∈ h.rows, blocks h.edges h.edges y) ∧
    blocks h.edges (captured h.edges h.rows) h.z

instance (h : Hint) : Decidable (validHint h) := by unfold validHint; infer_instance

theorem forced_hit {lo V U W : Finset (Fin 16)} {z : Fin 24} (inside : lo ⊆ U)
    (need : V ⊆ W) (checked : blocks lo V z) (A : Finset (Fin 11))
    (shape : allowed U A) (hits : Hits W A) : ¬ Disjoint A (negative z) := by
  intro off
  have block (B : Finset (Fin 11)) (bad : obstructs V z B) (ab : A ⊆ B) : False := by
    obtain ⟨e,he,separate⟩ := bad
    apply hits e (need he)
    apply separate.mono_right
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨ab hv, Finset.disjoint_left.mp off hv⟩
  rcases shape with ⟨c,hc⟩ | ⟨c,hc⟩
  · exact block {c} (checked.1 c) hc
  · exact block (neighbors lo c) (checked.2 c) (hc.trans (neighbors_anti inside c))

end G11TwoRounds
