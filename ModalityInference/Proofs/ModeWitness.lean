import ModalityInference.Proofs.Projection
import ModalityInference.Proofs.SyntacticEquality
import ModalityInference.Proofs.VariableOccurrences

/-! Reconstructing modality witnesses from Boolean coordinates, independently of solving. -/
namespace ModalityInference

theorem lookup_map_self {α β : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (f : α → β) {v} (hv : v ∈ xs) :
    (xs.map (fun w => (w, f w))).lookup v = some (f v) := by
  induction xs with
  | nil => contradiction
  | cons w xs ih =>
    by_cases h : v = w
    · subst w; simp
    · have he : (v == w) = false := by simpa using h
      simpa only [List.map_cons, List.lookup_cons, he] using
        ih ((List.mem_cons.mp hv).resolve_left h)


theorem ModeSatisfies.congr (c : Constraint) {η θ : ModVar → Mode}
    (h : ∀ v ∈ c.modVars, η v = θ v) : ModeSatisfies η c ↔ ModeSatisfies θ c := by
  cases c <;> simp only [ModeSatisfies, Constraint.modVars, Finset.mem_union,
    or_imp, forall_and] at *
  case mode a b =>
    simp only [ModExpr.Below,
      a.eval_congr (σ := some ∘ η) (τ := some ∘ θ) (fun v hv => congrArg some (h.1 v hv)),
      b.eval_congr (σ := some ∘ η) (τ := some ∘ θ) (fun v hv => congrArg some (h.2 v hv))]
  case defined a =>
    simp only [ModExpr.WellFormed,
      a.eval_congr (σ := some ∘ η) (τ := some ∘ θ) (fun v hv => congrArg some (h v hv))]

theorem ModeModels.congr (cs : Bounds) {η θ : ModVar → Mode}
    (h : ∀ v ∈ cs.modVars, η v = θ v) : ModeModels cs η ↔ ModeModels cs θ := by
  induction cs <;> simp_all [Bounds.modVars_cons, ModeModels, Finset.mem_union, or_imp, forall_and]
  exact fun _ => ModeSatisfies.congr _ h.1

theorem ModeAssignment.ofBooleans_lookup {cs σ v} (hv : v ∈ cs.modVars) :
    (ModeAssignment.ofBooleans cs σ).lookup v = some (projectedModes σ v) := by
  exact lookup_map_self cs.modeVariables _ ((cs.mem_modeVariables v).mpr hv)

theorem ModeAssignment.ofBooleans_models {cs σ}
    (h : (boundsModeFormula cs).eval σ = true) :
    ModeModels cs (ModeAssignment.ofBooleans cs σ).total := by
  apply (ModeModels.congr cs ?_).mpr ((boundsModeFormula_correct cs σ).mp h)
  intro v hv
  simp [ModeAssignment.total, ModeAssignment.ofBooleans_lookup hv]

end ModalityInference
