import PEqualNP.Defs

namespace Edge606.Restriction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {n : ℕ}

/-- Keep the inputs indexed by S and pin its complement to false. -/
def mask (S : Finset (Fin n)) (x : Fin n → Bool) (i : Fin n) : Bool :=
  if i ∈ S then x i else false

private def route (S : Finset (Fin n)) (stop j : ℕ) : ℕ :=
  if h : j < n then if (⟨j,h⟩ : Fin n) ∈ S then j else stop else j

private def mappedGate (S : Finset (Fin n)) (stop : ℕ) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (route S stop)⟩

/-- The first index outside the complete wire list is false throughout evaluation.
    Mapping pinned inputs to this index introduces no gates. -/
def restrict (S : Finset (Fin n)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (mappedGate S (n+C.size)),route S (n+C.size) C.output⟩

@[simp] theorem size (S : Finset (Fin n)) (C : Circuit) : (restrict S C).size=C.size := by
  simp [restrict,Circuit.size]

theorem monotone (S : Finset (Fin n)) (C : Circuit) (mono : Monotone2 C) :
    Monotone2 (restrict S C) := by
  intro g hg
  obtain ⟨old,member,rfl⟩ := List.mem_map.mp hg
  simpa only [mappedGate,List.length_map] using mono old member

theorem fanInTwo (S : Finset (Fin n)) (C : Circuit) (fan : FanInTwo C) :
    FanInTwo (restrict S C) := by
  intro g hg
  obtain ⟨old,member,rfl⟩ := List.mem_map.mp hg
  simpa only [mappedGate,List.length_map] using fan old member

private theorem read (S : Finset (Fin n)) (x : Fin n → Bool) (t : List Bool)
    (stop j : ℕ) (bound : n + t.length ≤ stop) :
    (List.ofFn x ++ t).getD (route S stop j) false =
      (List.ofFn (mask S x) ++ t).getD j false := by
  by_cases lo : j < n
  · let i : Fin n := ⟨j,lo⟩
    have raw (y : Fin n → Bool) :
        (List.ofFn y ++ t).getD j false = y i := by
      have valid : j < (List.ofFn y).length := by simpa using lo
      rw [List.getD_append _ _ _ _ valid]
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem valid,i]
    by_cases keep : i ∈ S
    · simp only [route,lo,↓reduceDIte,show (⟨j,lo⟩ : Fin n) = i from rfl,keep,↓reduceIte]
      rw [raw,raw]
      simp [mask,keep]
    · simp only [route,lo,↓reduceDIte,show (⟨j,lo⟩ : Fin n) = i from rfl,keep,↓reduceIte]
      rw [raw,List.getD_eq_default _ _ (by simpa using bound)]
      simp [mask,keep]
  · have past (y : Fin n → Bool) : (List.ofFn y).length ≤ j := by simp; omega
    simp only [route,lo,↓reduceDIte,List.getD_append_right _ _ _ _ (past _),List.length_ofFn]

private def value (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map (w.getD · false))

private def tailRun (raw : List Bool) : List Gate → List Bool → List Bool
  | [], t => t
  | g :: gs, t => tailRun raw gs (t ++ [value g (raw++t)])

private theorem fold_eq (gs : List Gate) (raw t : List Bool) :
    gs.foldl (fun w g => w ++ [value g w]) (raw++t) = raw ++ tailRun raw gs t := by
  induction gs generalizing t with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons,tailRun,List.append_assoc,ih]

private theorem tail_len (gs : List Gate) (raw t : List Bool) :
    (tailRun raw gs t).length = t.length + gs.length := by
  induction gs generalizing t with
  | nil => simp [tailRun]
  | cons g gs ih => simp [tailRun,ih]; omega

private theorem tail_eq (S : Finset (Fin n)) (x : Fin n → Bool) (gs : List Gate)
    (stop : ℕ) (t : List Bool) (bound : n+t.length+gs.length ≤ stop) :
    tailRun (List.ofFn x) (gs.map (mappedGate S stop)) t =
      tailRun (List.ofFn (mask S x)) gs t := by
  induction gs generalizing t with
  | nil => rfl
  | cons g gs ih =>
    have agrees : value (mappedGate S stop g) (List.ofFn x ++ t) =
        value g (List.ofFn (mask S x) ++ t) := by
      simp only [value,mappedGate,List.map_map]
      apply congrArg g.op.eval
      exact List.map_congr_left (fun j _ => read S x t stop j (by omega))
    simp only [List.map_cons,tailRun,agrees]
    apply ih
    simp only [List.length_cons] at bound
    simp
    omega

/-- Restriction preserves evaluation for every circuit, including gates with
    forward references and out-of-range indices. -/
theorem eval (S : Finset (Fin n)) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n (restrict S C) x = circuitFun n C (mask S x) := by
  let gs := C.gates
  let t := tailRun (List.ofFn (mask S x)) gs []
  have eq := tail_eq S x gs (n+C.size) [] (by simp [gs,Circuit.size])
  have left : (restrict S C).wires (List.ofFn x) = List.ofFn x ++ t := by
    change (gs.map _).foldl _ (List.ofFn x) = _
    simpa only [List.append_nil,eq,t,value] using
      fold_eq (gs.map (mappedGate S (n+C.size))) (List.ofFn x) []
  have right : C.wires (List.ofFn (mask S x)) = List.ofFn (mask S x) ++ t := by
    simpa only [List.append_nil,t,value,gs,Circuit.wires] using
      fold_eq gs (List.ofFn (mask S x)) []
  have bound : n+t.length ≤ n+C.size := by simp [t,gs,tail_len,Circuit.size]
  unfold circuitFun Circuit.eval
  rw [left,right]
  exact read S x t (n+C.size) C.output bound

theorem computes_graph (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (S : Finset (Fin n)) (C : Circuit)
    (comp : circuitFun n C =
      fun x => decide (∃ i j, G.Adj i j ∧ x i=true ∧ x j=true))
    (induced : ∀ i j, H.Adj i j ↔ G.Adj i j ∧ i ∈ S ∧ j ∈ S) :
    circuitFun n (restrict S C) =
      fun x => decide (∃ i j, H.Adj i j ∧ x i=true ∧ x j=true) := by
  funext x
  rw [eval,comp]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  have on (i : Fin n) : mask S x i=true ↔ i∈S ∧ x i=true := by
    by_cases hi : i∈S <;> simp [mask,hi]
  constructor
  · rintro ⟨i,j,adj,hi,hj⟩
    obtain ⟨si,xi⟩ := (on i).mp hi
    obtain ⟨sj,xj⟩ := (on j).mp hj
    exact ⟨i,j,(induced i j).mpr ⟨adj,si,sj⟩,xi,xj⟩
  · rintro ⟨i,j,adj,hi,hj⟩
    obtain ⟨uv,si,sj⟩ := (induced i j).mp adj
    exact ⟨i,j,uv,(on i).mpr ⟨si,hi⟩,(on j).mpr ⟨sj,hj⟩⟩

end Edge606.Restriction

#print axioms Edge606.Restriction.eval
#print axioms Edge606.Restriction.monotone
#print axioms Edge606.Restriction.computes_graph
