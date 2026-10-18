import ModalityInference.Proofs.ComparisonObserverModePullback
import ModalityInference.Proofs.ComparisonStructuralAlignment
import ModalityInference.Proofs.SchemeModeWitness

/-! Scalar worlds and guarded action models transport along the same modality
substitution as the observer. Unaffected observations require no scalar model;
active observations use only totality under the original ambient guards. -/
namespace ModalityInference.ComparisonObserverModePullback

open ComparisonAlgebra ComparisonModeRestriction ComparisonControls
  ComparisonStructuralAlignment

def world (ms : ModVar → ModExpr) (η : ModVar → Mode) : ModVar → Mode :=
  projectedModes (SchemeModeSynthesis.strategy ms (encodeModes η))

@[simp] theorem encode_world (ms : ModVar → ModExpr) (η : ModVar → Mode) :
    encodeModes (world ms η) = SchemeModeSynthesis.strategy ms (encodeModes η) :=
  SchemeModeSynthesis.encodeModes_projectedModes _

theorem world_eval {Δ : Bounds} {ms : ModVar → ModExpr} (h : Fixed Δ ms)
    {η : ModVar → Mode} (hη : ModeModels Δ η) (v : ModVar) :
    (ms v).eval (some ∘ η) = some (world ms η v) := by
  simpa only [projectedModes_encodeModes] using
    SchemeModeSynthesis.strategy_eval ms (encodeModes η) v
      (by simpa only [projectedModes_encodeModes] using h.total η hη v)

theorem world_models {Δ : Bounds} {ms : ModVar → ModExpr} (h : Fixed Δ ms)
    {η : ModVar → Mode} (hη : ModeModels Δ η) : ModeModels Δ (world ms η) := by
  apply (ModeModels.congr Δ ?_).mpr hη
  intro v hv
  have he := world_eval h hη v
  rw [h.fixed v hv] at he
  exact (Option.some.inj he).symm

theorem label_value {Δ : Bounds} {ms : ModVar → ModExpr} (h : Fixed Δ ms)
    {η : ModVar → Mode} (hη : ModeModels Δ η) {m n : GuardedMode Δ}
    (he : n.expression = m.expression.subst ms) :
    n.value η = m.value (world ms η) := by
  apply Option.some.inj
  calc
    some (n.value η) = n.expression.eval (some ∘ η) := (n.eval η hη).symm
    _ = m.expression.eval (some ∘ world ms η) := by
      rw [he,ModExpr.eval_subst]
      exact congrArg m.expression.eval (funext (world_eval h hη))
    _ = some (m.value (world ms η)) := m.eval _ (world_models h hη)

private theorem carrier_ext {Δ : Bounds} {shape : ComparisonShape}
    {a b : Carrier Δ shape} (h : a.type = b.type) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- Any supplied family of substituted labels suffices; its proof fields and
values outside the guarded scalar context need not be chosen canonically. -/
theorem model {Δ : Bounds} {ms : ModVar → ModExpr} {shape : ComparisonShape}
    (h : Fixed Δ ms) (f : LatticeHom (Order Δ shape) Bool)
    {raw closed : List (GuardedMode Δ)} {c : Coordinate} {η : ModVar → Mode}
    (labels : ∀m∈raw,∃n∈closed,n.expression = m.expression.subst ms)
    (hf : Model f closed c η) : Model (observer h f) raw c (world ms η) := by
  constructor
  · exact hf.modeModel.elim Or.inl (fun hη => Or.inr (world_models h hη))
  · intro a m hm
    obtain ⟨n,hn,he⟩ := labels m hm
    have ha : carrier h (m.act a) = n.act (carrier h a) := by
      apply carrier_ext
      change CompareTy.modal (a.type.subst CompareTy.var ms) (m.expression.subst ms) =
        CompareTy.modal (a.type.subst CompareTy.var ms) n.expression
      rw [he]
    change f (Order.of (carrier h (m.act a))) =
      coordinateValue c (f (Order.of (carrier h a))) (m.value (world ms η))
    rw [ha]
    have hv := hf.action (carrier h a) n hn
    rcases hf.modeModel with rfl | hη
    · exact hv
    · rw [label_value h hη he] at hv
      exact hv

end ModalityInference.ComparisonObserverModePullback
