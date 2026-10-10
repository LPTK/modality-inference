import ModalityInference.Proofs.Structural
import ModalityInference.Proofs.Evaluation
import ModalityInference.Proofs.Interpretation

namespace ModalityInference.Deferred
/-- DEFERRED. Prerequisites: ground realization commutes with substitution;
induction on subtyping, field-sensitive support and closure interpretation. -/
theorem semantic_subtyping {ρ w Δ a b x y v}
    (hΔ : GroundModels ρ Δ) (h : Subtype Δ a b)
    (ha : a.realize ρ = some x) (hb : b.realize ρ = some y)
    (hv : ValueInterpretation ρ w x Mode.identity v) :
    ValueInterpretation ρ w y Mode.identity v ∧
      ∀ l, Owns ρ v y l → Owns ρ v x l := by sorry

/-- DEFERRED. Prerequisites: structural lemmas, fresh/disjoint allocation splitting,
closed-definition generalization, typed closure captures, region liveness. -/
theorem semantic_soundness {Δ Γ t a ρ w γ ground}
    (ht : Typing Δ Γ t a) (hΔ : GroundModels ρ Δ)
    (hγ : EnvironmentInterpretation ρ w Γ γ) (ha : a.realize ρ = some ground) :
    SemanticEvaluation ρ w Γ γ t ground := by sorry

/-- Proved by induction on the fuelled evaluator. No typing needed. -/
theorem evalFuel_sound {fuel supplies γ t v}
    (h : evalFuel fuel supplies γ t = .success v) : Eval supplies γ t v :=
  ModalityInference.evalFuel_sound h

/-- Proved by induction on `Eval`, with an explicit sufficient fuel bound. -/
theorem evalFuel_complete {supplies γ t v} (h : Eval supplies γ t v) :
    ∃ n, ∀ fuel ≥ n, evalFuel fuel supplies γ t = .success v := h.fuel_complete

/-- DEFERRED. Prerequisites: semantic soundness and both evaluator correspondences.
An arbitrary small fuel budget is explicitly allowed to exhaust. -/
theorem termination_no_stuck {Δ Γ t a ρ w γ ground supplies}
    (ht : Typing Δ Γ t a) (hΔ : GroundModels ρ Δ)
    (hγ : EnvironmentInterpretation ρ w Γ γ) (ha : a.realize ρ = some ground)
    (hs : w.Compatible supplies γ) :
    (∃ v n, ∀ fuel ≥ n, evalFuel fuel supplies γ t = .success v) ∧
      ∀ fuel diagnostic, evalFuel fuel supplies γ t ≠ .rejected diagnostic := by sorry

/-- DEFERRED. Prerequisites: semantic soundness, including *reference* validity,
which cannot be derived from empty ownership of aliased fields. -/
theorem live_result {Δ Γ t a ρ w γ ground supplies v}
    (ht : Typing Δ Γ t a) (hΔ : GroundModels ρ Δ)
    (hγ : EnvironmentInterpretation ρ w Γ γ) (ha : a.realize ρ = some ground)
    (hs : w.Compatible supplies γ) (he : Eval supplies γ t v) :
    w.ValidValue v := by sorry

/-- DEFERRED. Prerequisites: typed support, freshness, context split/lock lemmas. -/
theorem ownership_bound {Δ Γ t a ρ w γ ground supplies v}
    (ht : Typing Δ Γ t a) (hΔ : GroundModels ρ Δ)
    (hγ : EnvironmentInterpretation ρ w Γ γ) (ha : a.realize ρ = some ground)
    (hs : w.Compatible supplies γ) (he : Eval supplies γ t v) :
    ∀ l, Owns ρ v ground l → EnvironmentOwns ρ γ Γ l ∨ supplies.FreshLocation l := by sorry

/-- Proved by structural induction on the concrete interpretation. -/
theorem global_references {ρ w t v}
    (hv : ValueInterpretation ρ w t Mode.identity v) (hg : t.mode.isLocal = false) :
    ∀ l, References v l → HeapLocation l :=
  hv.global_references (by simpa [Mode.compose, Mode.identity] using hg)
/-- Proved by type-indexed support induction, including the many-closure clause. -/
theorem shared_support {ρ w t v}
    (hv : ValueInterpretation ρ w t Mode.identity v)
    (hm : t.mode.once = false) (ha : t.mode.unique = false) :
    ∀ l, ¬ Owns ρ v t l := by
  simpa only [GroundTy.modal_identity] using hv.shared_support
    (by simpa [Mode.compose, Mode.identity] using hm)
    (by simpa [Mode.compose, Mode.identity] using ha)

/-- Proved by structural fuel induction; no typing hypotheses. -/
theorem evalFuel_monotone {n supplies γ t v}
    (h : evalFuel n supplies γ t = .success v) :
    ∀ fuel ≥ n, evalFuel fuel supplies γ t = .success v := ModalityInference.evalFuel_monotone h
end ModalityInference.Deferred
