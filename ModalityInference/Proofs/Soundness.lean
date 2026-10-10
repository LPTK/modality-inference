import ModalityInference.Proofs.Structural

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

/-- DEFERRED. Prerequisites: induction on the fuelled evaluator. No typing needed. -/
theorem evalFuel_sound {fuel supplies γ t v}
    (h : evalFuel fuel supplies γ t = .success v) : Eval supplies γ t v := by sorry

/-- DEFERRED. Prerequisites: induction on `Eval`, monotonicity in fuel. -/
theorem evalFuel_complete {supplies γ t v} (h : Eval supplies γ t v) :
    ∃ n, ∀ fuel ≥ n, evalFuel fuel supplies γ t = .success v := by sorry

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

/-- DEFERRED. Prerequisites: structural ground interpretation induction. -/
theorem global_references {ρ w t v}
    (hv : ValueInterpretation ρ w t Mode.identity v) (hg : t.mode.isLocal = false) :
    ∀ l, References v l → HeapLocation l := by sorry
/-- DEFERRED. Prerequisites: type-indexed support induction and the many-closure clause. -/
theorem shared_support {ρ w t v}
    (hv : ValueInterpretation ρ w t Mode.identity v)
    (hm : t.mode.once = false) (ha : t.mode.unique = false) :
    ∀ l, ¬ Owns ρ v t l := by sorry

/-- DEFERRED. Prerequisites: structural fuel induction; no typing hypotheses. -/
theorem evalFuel_monotone {n supplies γ t v}
    (h : evalFuel n supplies γ t = .success v) :
    ∀ fuel ≥ n, evalFuel fuel supplies γ t = .success v := by sorry
end ModalityInference.Deferred
