import ModalityInference.Core.Scoping
import ModalityInference.Inference
import ModalityInference.Generation
import ModalityInference.Semantics
import ModalityInference.Proofs.Erasure

/-! DEFERRED: these statements are a proof worklist, not established results.
Nothing outside `Proofs` imports this module. See README for prerequisites. -/
namespace ModalityInference.Deferred

/-- Prerequisites: alpha-renaming of scheme binders, composition of simultaneous substitutions. -/
theorem type_substitution_composition (t : Ty) (σ τ : Substitution) :
    τ.ty (σ.ty t) = (τ.compose σ).ty t := by sorry

/-- Prerequisites: de Bruijn lifting and induction on all term constructors. -/
theorem term_substitution_scoped (t : RawTerm) (σ : Nat → RawTerm) (n k : Nat)
    (ht : t.Scoped n) (hσ : ∀ i < n, (σ i).Scoped k) : (t.subst σ).Scoped k := by sorry

/-- Prerequisites: scheme binder renaming and substitution through declarative bounds. -/
theorem subtyping_substitution {Δ : Bounds} {a b : Ty} (σ : Substitution)
    (h : Subtype Δ a b) : Subtype (σ.bounds Δ) (σ.ty a) (σ.ty b) := by sorry

/-- Prerequisites: reflexivity of scheme subsumption, transitivity of context weakening. -/
theorem typing_weakening {Δ Γ Γ' t a} (h : RawTyping Δ Γ t a)
    (hc : ContextLe Δ Γ' Γ) : RawTyping Δ Γ' t a := by sorry

/-- Closed replacements avoid duplicating resources from a shared ambient context.
Prerequisites: instantiation/substitution lemmas and the closed-definition lemma. -/
theorem closed_term_substitution {Δ Γ t a} (h : RawTyping Δ Γ t a)
    (σ : Nat → RawTerm)
    (hσ : ∀ (i : Nat) s θ, Γ[i]? = some (some s) → Instantiates s θ →
      EntailsAll Δ (θ.bounds s.bounds) → RawTyping Δ [] (σ i) (θ.ty s.body)) :
    RawTyping Δ [] (t.subst σ) a := by sorry

/-- Prerequisites: context routing, polymorphic shared-binding restrictions. -/
theorem split_context_spec (Γ : AlgorithmicContext) (X Y : Finset Nat) :
    UsageSplit Γ (splitContext X Y Γ).1 (splitContext X Y Γ).2 := by sorry

/-- Prerequisites: independent `Lookup` induction, symbolic future/capture equations. -/
theorem symbolic_lock_lookup {Γ i s} (h : lookupScheme Γ i = .success s) :
    Lookup Γ i s := by sorry

/-- Prerequisites: semantic subtyping, support antimonotonicity, scheme unions. -/
theorem context_join_semantics {ρ w Γ Γ₁ Γ₂ γ Δ}
    (hΔ : GroundModels ρ Δ) (h : ContextJoin Δ Γ₁ Γ₂ Γ)
    (hγ : EnvironmentInterpretation ρ w Γ γ) :
    EnvironmentInterpretation ρ w Γ₁ γ ∧ EnvironmentInterpretation ρ w Γ₂ γ ∧
      ∀ l, ¬ (EnvironmentOwns ρ γ Γ₁ l ∧ EnvironmentOwns ρ γ Γ₂ l) := by sorry

/-- Prerequisites: future crossing, closure support interpretation, scheme substitution. -/
theorem locking_semantics {ρ w Γ Γ' γ Δ m}
    (hΔ : GroundModels ρ Δ) (h : Lock Δ m Γ Γ')
    (hγ : EnvironmentInterpretation ρ w Γ γ) :
    EnvironmentInterpretation ρ w Γ' γ ∧
      ∀ l, EnvironmentOwns ρ γ Γ' l → EnvironmentOwns ρ γ Γ l := by sorry

/-- Proved independently by induction on evaluation; capture selection uses syntax FVs. -/
theorem annotation_erasure {s γ δ t u v}
    (hγ : List.Forall₂ ValueErasure γ δ) (ht : t.erase = u.erase)
    (h : Eval s γ t v) : ∃ w, Eval s δ u w ∧ ValueErasure v w := h.annotation_erasure hγ ht
end ModalityInference.Deferred
