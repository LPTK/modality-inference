import ModalityInference.Proofs.SourceTyping
import ModalityInference.RuntimeSemantics
import ModalityInference.Proofs.Runtime
import ModalityInference.Proofs.Soundness

/-! Source typing is sound for direct execution without capture annotations.
The interpretation preserves the same ownership evidence under erasure, so
polymorphic bindings retain their full per-instance semantics.
-/
namespace ModalityInference

/-- The same instance-specific reserve works for every representation of a value. -/
theorem ResourceSchemeInterpretation.erasure {ρ w s v u reserved}
    (hv : ResourceSchemeInterpretation ρ w s v reserved) (he : ValueErasure v u) :
    ResourceSchemeInterpretation ρ w s u reserved :=
  ⟨fun l hl => (he.references l).mp (hv.1 l hl), fun η t hi ht =>
    (hv.2 η t hi ht).elim fun owned ho => ⟨owned, ho.1, ho.2.erasure he⟩⟩

/-- Erasure preserves the reserves of every binding in an open environment. -/
theorem ResourceEnvironmentInterpretation.erasure {ρ w Γ γ δ reserved}
    (hγ : ResourceEnvironmentInterpretation ρ w Γ γ reserved)
    (he : List.Forall₂ ValueErasure γ δ) :
    ResourceEnvironmentInterpretation ρ w Γ δ reserved := by
  refine ⟨?_, hγ.2⟩
  intro i s hi
  obtain ⟨v, hv, hs⟩ := hγ.1 i s hi
  obtain ⟨hiγ, rfl⟩ := List.getElem?_eq_some_iff.mp hv
  exact ⟨δ[i]'(he.length_eq ▸ hiγ),
    List.getElem?_eq_some_iff.mpr ⟨he.length_eq ▸ hiγ, rfl⟩,
    hs.erasure (he.get hiγ (he.length_eq ▸ hiγ))⟩

namespace Runtime

/-- The raw interpretation preserves the exact ownership evidence of any
annotated representation of the same value. -/
theorem resourceInterpretation_erase {w t ambient v owned} :
    ResourceInterpretation w t ambient (eraseValue v) owned ↔
      ModalityInference.ResourceInterpretation w t ambient v owned :=
  ⟨fun h => h.erasure (annotate_erasure v).symm,
    fun h => h.erasure (annotate_erasure v)⟩

/-- Erasure retains every admissible instance and its selected resource subset. -/
theorem resourceSchemeInterpretation_erase {ρ w s v reserved} :
    ResourceSchemeInterpretation ρ w s (eraseValue v) reserved ↔
      ModalityInference.ResourceSchemeInterpretation ρ w s v reserved :=
  ⟨fun h => h.erasure (annotate_erasure v).symm,
    fun h => h.erasure (annotate_erasure v)⟩

private theorem canonical_environment_erasure (γ : ModalityInference.Environment) :
    List.Forall₂ ValueErasure γ ((γ.map eraseValue).map Value.annotate) ∧
      List.Forall₂ ValueErasure ((γ.map eraseValue).map Value.annotate) γ := by
  induction γ with
  | nil => exact ⟨.nil, .nil⟩
  | cons v γ ih =>
    exact ⟨.cons (annotate_erasure v) ih.1, .cons (annotate_erasure v).symm ih.2⟩

/-- Raw environments retain the complete per-instance interpretation and all
separation conditions on the original reserves. -/
theorem resourceEnvironmentInterpretation_erase {ρ w Γ γ reserved} :
    ResourceEnvironmentInterpretation ρ w Γ (γ.map eraseValue) reserved ↔
      ModalityInference.ResourceEnvironmentInterpretation ρ w Γ γ reserved :=
  ⟨fun h => h.erasure (canonical_environment_erasure γ).2,
    fun h => h.erasure (canonical_environment_erasure γ).1⟩

/-- All references of an interpreted raw value remain live. -/
theorem ResourceInterpretation.valid {w t ambient v owned}
    (h : ResourceInterpretation w t ambient v owned) : ValidValue w v := by
  simpa using (validValue_erase w v.annotate).mpr
    (ModalityInference.ResourceInterpretation.valid h)

/-- Owned locations are references of the raw value itself. -/
theorem ResourceInterpretation.references {w t ambient v owned}
    (h : ResourceInterpretation w t ambient v owned) :
    ∀ l ∈ owned, References v l :=
  fun l hl => eraseValue_annotate v ▸ (references_erase v.annotate l).mpr
    (ModalityInference.ResourceInterpretation.references h l hl)

end Runtime

/-- Every well-typed source result has a defined ground interpretation. -/
theorem SourceTyping.realize_defined {Δ Γ t a} (h : SourceTyping Δ Γ t a)
    {ρ} (hΔ : GroundModels ρ Δ) : (a.realize ρ).isSome :=
  h.to_rawTyping.elim fun _ ht => ht.2.realize_defined hΔ

/-- Fundamental soundness of the direct source judgment for raw execution,
including open environments and every admissible polymorphic instance. -/
theorem SourceTyping.resource_semantic {Δ Γ t a} (ht : SourceTyping Δ Γ t a)
    {ρ w γ reserved ground} (hΔ : GroundModels ρ Δ)
    (hγ : Runtime.ResourceEnvironmentInterpretation ρ w Γ γ reserved)
    (ha : a.realize ρ = some ground) :
    Runtime.ResourceSemanticEvaluation w γ t ground (ContextResources Γ reserved) := by
  obtain ⟨t, rfl, hannotated⟩ := ht.to_rawTyping
  intro supplies hs
  have hs' : w.Compatible supplies (γ.map Runtime.Value.annotate) :=
    (Runtime.compatible_erase w supplies _).mp (by simpa [Function.comp_def] using hs)
  obtain ⟨v, owned, he, hv, ho⟩ := hannotated.resource_semantic hΔ hγ ha supplies hs'
  exact ⟨Runtime.eraseValue v, owned,
    by simpa [Function.comp_def] using Runtime.eval_erase he,
    (Runtime.resourceInterpretation_erase).mpr hv, ho⟩

/-- Typed source execution eventually succeeds and never produces a rejection. -/
theorem SourceTyping.termination_no_stuck {Δ Γ t a ρ w γ reserved ground supplies}
    (ht : SourceTyping Δ Γ t a) (hΔ : GroundModels ρ Δ)
    (hγ : Runtime.ResourceEnvironmentInterpretation ρ w Γ γ reserved)
    (ha : a.realize ρ = some ground) (hs : Runtime.Compatible w supplies γ) :
    (∃ v n, ∀ fuel ≥ n, Runtime.evalFuel fuel supplies γ t = .success v) ∧
      ∀ fuel diagnostic, Runtime.evalFuel fuel supplies γ t ≠ .rejected diagnostic := by
  obtain ⟨v, _, he, _, _⟩ := ht.resource_semantic hΔ hγ ha supplies hs
  obtain ⟨n, hn⟩ := he.fuel_complete
  exact ⟨⟨v, n, hn⟩, he.no_rejection⟩

/-- Every reference in a raw result, including aliases and captured values, is live. -/
theorem SourceTyping.live_result {Δ Γ t a ρ w γ reserved ground supplies v}
    (ht : SourceTyping Δ Γ t a) (hΔ : GroundModels ρ Δ)
    (hγ : Runtime.ResourceEnvironmentInterpretation ρ w Γ γ reserved)
    (ha : a.realize ρ = some ground) (hs : Runtime.Compatible w supplies γ)
    (he : Runtime.Eval supplies γ t v) : Runtime.ValidValue w v := by
  obtain ⟨v', _, he', hv, _⟩ := ht.resource_semantic hΔ hγ ha supplies hs
  exact (he'.deterministic he) ▸ hv.valid

/-- Result ownership is drawn from the input reserves or this run's fresh cells. -/
theorem SourceTyping.ownership_bound {Δ Γ t a ρ w γ reserved ground supplies v}
    (ht : SourceTyping Δ Γ t a) (hΔ : GroundModels ρ Δ)
    (hγ : Runtime.ResourceEnvironmentInterpretation ρ w Γ γ reserved)
    (ha : a.realize ρ = some ground) (hs : Runtime.Compatible w supplies γ)
    (he : Runtime.Eval supplies γ t v) :
    ∃ owned, Runtime.ResourceInterpretation w ground Mode.identity v owned ∧
      ∀ l ∈ owned, l ∈ ContextResources Γ reserved ∨ supplies.FreshLocation l := by
  obtain ⟨v', owned, he', hv, ho⟩ := ht.resource_semantic hΔ hγ ha supplies hs
  exact ⟨owned, (he'.deterministic he) ▸ hv, fun _ hl => ho hl⟩

/-- Closed source programs obtain their ground result from typing and own only
fresh locations, with no assumed value interpretation. -/
theorem SourceTyping.resource_closed {Δ t a} (ht : SourceTyping Δ [] t a)
    {ρ w supplies} (hΔ : GroundModels ρ Δ) (hs : Runtime.Compatible w supplies []) :
    ∃ ground v owned, a.realize ρ = some ground ∧ Runtime.Eval supplies [] t v ∧
      Runtime.ResourceInterpretation w ground Mode.identity v owned ∧
      owned ⊆ {l | supplies.FreshLocation l} := by
  obtain ⟨ground, ha⟩ := Option.isSome_iff_exists.mp (ht.realize_defined hΔ)
  obtain ⟨v, owned, he, hv, ho⟩ := ht.resource_semantic hΔ
    (ResourceEnvironmentInterpretation.nil (reserved := fun _ => ∅)) ha supplies hs
  exact ⟨ground, v, owned, ha, he, hv, by simpa using ho⟩

end ModalityInference
