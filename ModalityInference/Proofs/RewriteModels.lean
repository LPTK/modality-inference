import ModalityInference.Rewriting
import ModalityInference.Core.Scoping
import ModalityInference.Proofs.ConstraintModels
import ModalityInference.Proofs.GroundEquivalence
import ModalityInference.Proofs.GroundSubstitution
import ModalityInference.Proofs.Reduction

namespace ModalityInference.Deferred

/-- Ground solutions are observed on an explicit original domain, modulo
mutual ground subtyping; fresh auxiliary variables are existentially hidden. -/
def ConfigModels (scope : Scope) (s : RewriteConfig) (ρ : GroundAssignment) : Prop :=
  ∃ η : GroundAssignment, GroundModels η s.constraints ∧
    (∀ v ∈ scope.types, ∃ t, (s.substitution.type v).realize η = some t ∧
      Subtype [] t.reify (ρ.types v).reify ∧ Subtype [] (ρ.types v).reify t.reify) ∧
    (∀ v ∈ scope.modes, (s.substitution.mode v).eval (some ∘ η.modes) = some (ρ.modes v))

theorem ConfigModels.congr {scope s t ρ} (hσ : s.substitution = t.substitution)
    (h : ∀ η, GroundModels η s.constraints ↔ GroundModels η t.constraints) :
    ConfigModels scope s ρ ↔ ConfigModels scope t ρ := by
  simp only [ConfigModels, hσ]
  exact exists_congr fun η => and_congr (h η) Iff.rfl

end ModalityInference.Deferred
