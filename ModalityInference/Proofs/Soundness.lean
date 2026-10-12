import ModalityInference.Proofs.Structural
import ModalityInference.Proofs.Evaluation
import ModalityInference.Proofs.Interpretation
import ModalityInference.Proofs.Subtyping
import ModalityInference.Proofs.ResourceSoundness

namespace ModalityInference.Deferred
/-- Proved independently by subtyping induction, preserving field-sensitive
support, symbolic bounds and partial-modality definedness. -/
theorem semantic_subtyping {ρ w Δ a b x y v}
    (hΔ : GroundModels ρ Δ) (h : Subtype Δ a b)
    (ha : a.realize ρ = some x) (hb : b.realize ρ = some y)
    (hv : ValueInterpretation ρ w x Mode.identity v) :
    ValueInterpretation ρ w y Mode.identity v ∧
      ∀ l, Owns ρ v y l → Owns ρ v x l := by
  simpa only [GroundTy.modal_identity] using h.semantic hΔ ha hb hv

/-- REFUTED historical annotation-dependent formulation; see the admission-free
`PolymorphicCapture.no_unrestricted_soundness`. It remains recorded as a proposition.
The corrected `semantic_soundness` below carries ownership evidence for each
ground instance instead of interpreting old capture metadata under a new assignment.
It preserves every core constructor and the original operational semantics. -/
def SemanticSoundness : Prop := ∀ {Δ Γ t a ρ w γ ground},
    Typing Δ Γ t a → GroundModels ρ Δ →
    EnvironmentInterpretation ρ w Γ γ → a.realize ρ = some ground →
    SemanticEvaluation ρ w Γ γ t ground

/-- Corrected fundamental soundness, proved for the entire core by typing induction. -/
theorem semantic_soundness {Δ Γ t a ρ w γ reserved ground}
    (ht : Typing Δ Γ t a) (hΔ : GroundModels ρ Δ)
    (hγ : ResourceEnvironmentInterpretation ρ w Γ γ reserved) (ha : a.realize ρ = some ground) :
    ResourceSemanticEvaluation w γ t ground (ContextResources Γ reserved) :=
  ht.resource_semantic hΔ hγ ha

/-- Proved by induction on the fuelled evaluator. No typing needed. -/
theorem evalFuel_sound {fuel supplies γ t v}
    (h : evalFuel fuel supplies γ t = .success v) : Eval supplies γ t v :=
  ModalityInference.evalFuel_sound h

/-- Proved by induction on `Eval`, with an explicit sufficient fuel bound. -/
theorem evalFuel_complete {supplies γ t v} (h : Eval supplies γ t v) :
    ∃ n, ∀ fuel ≥ n, evalFuel fuel supplies γ t = .success v := h.fuel_complete

/-- Termination and absence of rejection for every typed core term. An arbitrary
small fuel budget may still exhaust. -/
theorem termination_no_stuck {Δ Γ t a ρ w γ reserved ground supplies}
    (ht : Typing Δ Γ t a) (hΔ : GroundModels ρ Δ)
    (hγ : ResourceEnvironmentInterpretation ρ w Γ γ reserved) (ha : a.realize ρ = some ground)
    (hs : w.Compatible supplies γ) :
    (∃ v n, ∀ fuel ≥ n, evalFuel fuel supplies γ t = .success v) ∧
      ∀ fuel diagnostic, evalFuel fuel supplies γ t ≠ .rejected diagnostic := by
  obtain ⟨v, _, he, _, _⟩ := ht.resource_semantic hΔ hγ ha supplies hs
  obtain ⟨n, hn⟩ := he.fuel_complete
  exact ⟨⟨v, n, hn⟩, he.no_rejection⟩

/-- Every result reference remains live, including aliased fields and captures. -/
theorem live_result {Δ Γ t a ρ w γ reserved ground supplies v}
    (ht : Typing Δ Γ t a) (hΔ : GroundModels ρ Δ)
    (hγ : ResourceEnvironmentInterpretation ρ w Γ γ reserved) (ha : a.realize ρ = some ground)
    (hs : w.Compatible supplies γ) (he : Eval supplies γ t v) :
    w.ValidValue v := by
  obtain ⟨v', _, he', hv, _⟩ := ht.resource_semantic hΔ hγ ha supplies hs
  cases he'.deterministic he
  exact hv.valid

/-- Ownership is evidence for the selected ground instance. Every owned result
location comes from a context reserve or this evaluation's fresh supply. -/
theorem ownership_bound {Δ Γ t a ρ w γ reserved ground supplies v}
    (ht : Typing Δ Γ t a) (hΔ : GroundModels ρ Δ)
    (hγ : ResourceEnvironmentInterpretation ρ w Γ γ reserved) (ha : a.realize ρ = some ground)
    (hs : w.Compatible supplies γ) (he : Eval supplies γ t v) :
    ∃ owned, ResourceInterpretation w ground Mode.identity v owned ∧
      ∀ l ∈ owned, l ∈ ContextResources Γ reserved ∨ supplies.FreshLocation l := by
  obtain ⟨v', owned, he', hv, ho⟩ := ht.resource_semantic hΔ hγ ha supplies hs
  cases he'.deterministic he
  exact ⟨owned, hv, fun _ hl => ho hl⟩

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
