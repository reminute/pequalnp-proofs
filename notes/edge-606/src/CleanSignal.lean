import DegreePartner
import TwinReads

namespace Edge606.CleanSignal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Cubic1971.StarReader

variable {n : Nat}

/-- Any noncenter output of a prefix with no direct read of the center is
    unchanged when just the center input changes. Forward reads default to false. -/
theorem prefix_agrees (pre : List Gate) (k : Nat) (v : Fin n) (other : k ≠ v.val)
    (none : ∀ g ∈ pre, v.val ∉ g.inputs) (x y : Fin n → Bool)
    (agree : ∀ i, i ≠ v → x i = y i) :
    circuitFun n (⟨pre,k⟩ : Circuit) x = circuitFun n ⟨pre,k⟩ y := by
  apply TwinReads.masked_many _ other x y agree
  intro j reads
  exact (none (pre.get j) (List.get_mem _ j) reads).elim

private theorem graph_reset {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (x : Fin n → Bool) (v : Fin n) (on : GraphDensity.edgeFunction G (Function.update x v false) = true) :
    GraphDensity.edgeFunction G x = true := by
  obtain ⟨a,b,edge,ha,hb⟩ := of_decide_eq_true on
  have stays (i : Fin n) (hi : Function.update x v false i = true) : x i = true := by
    by_cases h : i=v <;> simp_all [Function.update_of_ne]
  exact decide_eq_true ⟨a,b,edge,stays a ha,stays b hb⟩

/-- Promote an implication checked only at center=false to the entire cube. -/
theorem global_of_off (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre : List Gate) (k : Nat) (v : Fin n) (other : k ≠ v.val)
    (none : ∀ g ∈ pre, v.val ∉ g.inputs)
    (off : ∀ x : Fin n → Bool, x v = false → circuitFun n (⟨pre,k⟩ : Circuit) x = true →
      GraphDensity.edgeFunction G x = true) :
    ∀ x : Fin n → Bool, circuitFun n (⟨pre,k⟩ : Circuit) x = true →
      GraphDensity.edgeFunction G x = true := by
  intro x high
  let y := Function.update x v false
  have same := prefix_agrees pre k v other none x y (fun i hi => by simp [y,Function.update_of_ne hi])
  exact graph_reset x v (off y (by simp [y]) (same.symm.trans high))

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n)
variable (C : Circuit) (pre post : List Gate) (r : Gate) (k : Nat)
variable (layout : C.gates = pre ++ r :: post) (mono : Monotone2 C)
variable (sole : ∀ g ∈ pre ++ post, ¬effective v.val g)
variable (args : r.inputs = [v.val,k] ∨ r.inputs = [k,v.val])
variable (other : k ≠ v.val) (output : C.output ≠ v.val)
variable (computes : circuitFun n C = GraphDensity.edgeFunction G)
include layout mono sole args other output computes

theorem or_global (op : r.op = .or) (girth : GirthEdgeNegatives.GirthFive G) :
    G.degree v ≤ pre.length + 1 ∨
      ∀ x : Fin n → Bool, circuitFun n (⟨pre,k⟩ : Circuit) x = true → GraphDensity.edgeFunction G x = true := by
  apply (DegreePartner.or_dichotomy G v C pre post r k layout mono sole args other output computes op girth).imp_right
  apply global_of_off G pre k v other
  intro g mem reads
  have inC : g ∈ C.gates := layout ▸ List.mem_append_left _ mem
  obtain ⟨ops,sz⟩ := mono g inC
  apply sole g (List.mem_append_left _ mem)
  change g.op = .and ∨ g.op = .or at ops
  rcases ops with hop | hop <;> simpa [effective,hop,GateOp.eval,List.take_of_length_le sz] using reads

/-- The safety premise for moving the partner to a final OR gate, phrased
    entirely in terms of the original circuit and the prefix circuit. -/
theorem short_safe (op : r.op = .or) (girth : GirthEdgeNegatives.GirthFive G)
    (short : pre.length + 1 < G.degree v) :
    ∀ x : Fin n → Bool, circuitFun n (⟨pre,k⟩ : Circuit) x = true → circuitFun n C x = true := by
  rw [computes]
  exact (or_global G v C pre post r k layout mono sole args other output computes op girth).resolve_left
    (Nat.not_le_of_gt short)

end Edge606.CleanSignal

#print axioms Edge606.CleanSignal.prefix_agrees
#print axioms Edge606.CleanSignal.global_of_off
#print axioms Edge606.CleanSignal.or_global
#print axioms Edge606.CleanSignal.short_safe
