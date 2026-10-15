import ModalityInference.ComparisonJointEncoding
import ModalityInference.Proofs.ComparisonJointHorn

namespace ModalityInference.ComparisonJointEncoding

open ComparisonPropagation ComparisonJointHorn

def valuation (values : Fin count → Bool) (parameters : Nat → Bool) (v : Nat) : Bool :=
  if h : v < count then values ⟨v, h⟩ else parameters (v - count)

@[simp] theorem valuation_state (values : Fin count → Bool) (parameters : Nat → Bool)
    (i : Fin count) : valuation values parameters i.val = values i := by
  simp [valuation, i.isLt]

@[simp] theorem valuation_guard (values : Fin count → Bool) (parameters : Nat → Bool)
    (i : Nat) : valuation values parameters (count + i) = parameters i := by
  simp [valuation]

theorem prepend_holds (state : Clause) (guards : CNF) (σ : Nat → Bool) :
    CNFHolds σ (prepend state guards) ↔ ClauseHolds σ state ∨ CNFHolds σ guards := by
  simp only [prepend, CNFHolds, List.forall_mem_map, clauseHolds_append]
  simp only [forall_or_left]

theorem encode_correct (obligation : Obligation count) (values : Fin count → Bool)
    (parameters : Nat → Bool) :
    CNFHolds (valuation values parameters) (encode obligation) ↔
      obligation.Holds parameters (fun i => values i = true) := by
  cases obligation <;> simp only [encode, prepend_holds, rename_correct,
    Function.comp_def, valuation_guard, negate_correct, Obligation.Holds]
  all_goals simp only [ClauseHolds, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
  all_goals grind [valuation_state]

theorem encodeAll_correct (obligations : List (Obligation count))
    (values : Fin count → Bool) (parameters : Nat → Bool) :
    CNFHolds (valuation values parameters) (encodeAll obligations) ↔
      ∀ obligation ∈ obligations, obligation.Holds parameters (fun i => values i = true) := by
  simp only [encodeAll, CNFHolds, List.forall_mem_flatMap]
  exact forall_congr' fun obligation => imp_congr_right fun _ =>
    encode_correct obligation values parameters

private theorem shifted_index {count : Nat} {c : Clause} {v : Nat} {b : Bool}
    (h : (v, b) ∈ c.map (fun literal => (count + literal.1, literal.2))) : count ≤ v := by
  obtain ⟨⟨w, p⟩, _, he⟩ := List.mem_map.mp h
  cases he
  exact Nat.le_add_right _ _

theorem prepend_linear {count : Nat} {state : Clause}
    (hs : LinearClause (· < count) state) (guards : CNF) :
    Linear (· < count) (prepend state (rename (count + ·) guards)) := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp hd
  intro v w b hv hw hsv hsw
  exact hs ((List.mem_append.mp hv).resolve_right fun h => (Nat.not_le.mpr hsv) (shifted_index h))
    ((List.mem_append.mp hw).resolve_right fun h => (Nat.not_le.mpr hsw) (shifted_index h)) hsv hsw

theorem encode_linear (obligation : Obligation count) : Linear (· < count) (encode obligation) := by
  cases obligation <;> simp only [encode]
  case lower | edge | upper =>
    apply prepend_linear
    intro v w b hv hw _ _
    grind
  case check condition =>
    simpa [prepend] using prepend_linear (count := count) (state := []) (by simp [LinearClause]) condition

theorem encodeAll_linear (obligations : List (Obligation count)) :
    Linear (· < count) (encodeAll obligations) := by
  intro c hc
  obtain ⟨obligation, _, hc⟩ := List.mem_flatMap.mp hc
  exact encode_linear obligation c hc

/-- The existing modalized-bound compiler gives an exact linear-state query. -/
theorem compileBound_correct (action : ModExpr → Action) (theory : CNF)
    (bound : Bound count) (values : Fin count → Bool) (parameters : Nat → Bool) :
    CNFHolds (valuation values parameters)
        (encodeAll (ComparisonPropagation.compileBound action theory bound)) ↔
      (CNFHolds parameters theory → bound.left.Holds action parameters (fun i => values i = true) →
        bound.right.Holds action parameters (fun i => values i = true)) :=
  (encodeAll_correct _ _ _).trans (ComparisonPropagation.compileBound_correct _ _ _ _ _)

/-- Coordinate projection preserves unary clauses in the remaining state
variables; the guards remain outside the state namespace. -/
theorem project_linear (obligations : List (Obligation count)) (coordinates : List Nat)
    (hcoordinates : ∀ v ∈ coordinates, v < count) :
    Linear (fun v => v < count ∧ v ∉ coordinates)
      (ComparisonPropagation.project coordinates (encodeAll obligations)) := by
  intro c hc
  exact (ComparisonJointHorn.project_linear (encodeAll_linear obligations) hcoordinates c hc).restrict
    (fun _ h => h.1)

end ModalityInference.ComparisonJointEncoding
