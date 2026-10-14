import ModalityInference.Core.Scoping
import ModalityInference.Inference
import ModalityInference.Generation
import ModalityInference.Semantics
import ModalityInference.Proofs.Erasure
import ModalityInference.Proofs.Substitution
import ModalityInference.Proofs.Scoping
import ModalityInference.Proofs.Generation
import ModalityInference.Proofs.Declarative
import ModalityInference.Proofs.PartialSubstitution
import ModalityInference.Proofs.ResourceContexts

/-! DEFERRED: these statements are a proof worklist, not established results.
Nothing outside `Proofs` imports this module. See README for prerequisites. -/
namespace ModalityInference.Deferred

/-- Proved independently by composition of lookup tables and structural induction. -/
theorem type_substitution_composition (t : Ty) (σ τ : Substitution) :
    τ.ty (σ.ty t) = (τ.compose σ).ty t := Substitution.ty_compose t σ τ

/-- Proved by de Bruijn lifting and induction on every term constructor. -/
theorem term_substitution_scoped (t : RawTerm) (σ : Nat → RawTerm) (n k : Nat)
    (ht : t.Scoped n) (hσ : ∀ i < n, (σ i).Scoped k) : (t.subst σ).Scoped k :=
  t.subst_scoped σ n k ht hσ

/-- Proved under the well-formed-image convention for substitutions. The
unrestricted former statement is refuted in `PartialSubstitution`; ordinary
source images satisfy the condition automatically. -/
theorem subtyping_substitution {Δ : Bounds} {a b : Ty} (σ : Substitution)
    (h : Subtype Δ a b)
    (hσ : σ.WellFormedUnder (σ.bounds Δ)) :
    Subtype (σ.bounds Δ) (σ.ty a) (σ.ty b) :=
  h.substitute σ (fun η hη v => hσ.modes v η hη)

/-- Proved directly from declarative subsumption and type reflexivity. -/
theorem typing_weakening {Δ Γ Γ' t a} (h : RawTyping Δ Γ t a)
    (hc : ContextLe Δ Γ' Γ) : RawTyping Δ Γ' t a := h.weakening hc

/-- Closed replacements avoid duplicating resources from a shared ambient context.
Prerequisites: instantiation/substitution lemmas and the closed-definition lemma. -/
theorem closed_term_substitution {Δ Γ t a} (h : RawTyping Δ Γ t a)
    (σ : Nat → RawTerm)
    (hσ : ∀ (i : Nat) s θ, Γ[i]? = some (some s) → Instantiates s θ →
      EntailsAll Δ (θ.bounds s.bounds) → RawTyping Δ [] (σ i) (θ.ty s.body)) :
    RawTyping Δ [] (t.subst σ) a := by sorry

/-- Proved independently against the relational usage-context specification. -/
theorem split_context_spec (Γ : AlgorithmicContext) (X Y : Finset Nat) :
    UsageSplit Γ (splitContext X Y Γ).1 (splitContext X Y Γ).2 := splitContext_spec Γ X Y

/-- Proved by context induction; the converse is `Lookup.lookupScheme`. -/
theorem symbolic_lock_lookup {Γ i s} (h : lookupScheme Γ i = .success s) :
    Lookup Γ i s := lookupScheme_sound h

/-- Proved for the repaired, instance-indexed ownership interpretation. Each
component has valid bindings, owns only source resources, and is disjoint from
the other component. The shared case uses fresh polymorphic instantiation. -/
theorem context_join_semantics {ρ w Γ Γ₁ Γ₂ γ Δ reserved}
    (hΔ : GroundModels ρ Δ) (h : ContextJoin Δ Γ₁ Γ₂ Γ)
    (hγ : ResourceEnvironmentInterpretation ρ w Γ γ reserved) :
    ∃ left right,
      ResourceEnvironmentInterpretation ρ w Γ₁ γ left ∧
      ResourceEnvironmentInterpretation ρ w Γ₂ γ right ∧
      ContextResources Γ₁ left ⊆ ContextResources Γ reserved ∧
      ContextResources Γ₂ right ⊆ ContextResources Γ reserved ∧
      Disjoint (ContextResources Γ₁ left) (ContextResources Γ₂ right) :=
  h.resource_semantics hΔ hγ

/-- Proved for instance-indexed ownership: each retained binding satisfies its
captured type, and the locked context uses only its original resource reserves. -/
theorem locking_semantics {ρ w Γ Γ' γ Δ m reserved}
    (hΔ : GroundModels ρ Δ) (h : Lock Δ m Γ Γ')
    (hγ : ResourceEnvironmentInterpretation ρ w Γ γ reserved) :
    ResourceEnvironmentInterpretation ρ w Γ' γ reserved ∧
      ContextResources Γ' reserved ⊆ ContextResources Γ reserved :=
  h.resource_semantics hΔ hγ

/-- Proved independently by induction on evaluation; capture selection uses syntax FVs. -/
theorem annotation_erasure {s γ δ t u v}
    (hγ : List.Forall₂ ValueErasure γ δ) (ht : t.erase = u.erase)
    (h : Eval s γ t v) : ∃ w, Eval s δ u w ∧ ValueErasure v w := h.annotation_erasure hγ ht
end ModalityInference.Deferred
