import ModalityInference.Runtime
import ModalityInference.ResourceSemantics

/-! Resource semantics for values without capture annotations. A canonical
internal representation lets the source relation reuse the type-indexed
ownership interpretation. Ownership evidence remains specific to each ground
instance, and never becomes part of the runtime closure.
-/
namespace ModalityInference.Runtime

/-- Ownership of a raw value at a selected ground instance. -/
def ResourceInterpretation (w : World) (t : GroundTy) (ambient : Mode)
    (v : Value) (owned : Resources) : Prop :=
  ModalityInference.ResourceInterpretation w t ambient v.annotate owned

/-- Each admissible instance selects its own ownership from the binding's reserve. -/
def ResourceSchemeInterpretation (ρ : GroundAssignment) (w : World)
    (s : Scheme) (v : Value) (reserved : Resources) : Prop :=
  ModalityInference.ResourceSchemeInterpretation ρ w s v.annotate reserved

/-- Environment evidence reserves disjoint resources for separate bindings,
with instance-specific evidence at every lookup. -/
def ResourceEnvironmentInterpretation (ρ : GroundAssignment) (w : World)
    (Γ : Context) (γ : Environment) (reserved : Nat → Resources) : Prop :=
  ModalityInference.ResourceEnvironmentInterpretation ρ w Γ
    (γ.map Value.annotate) reserved

/-- Evaluation of source syntax with raw environments and raw result values. -/
def ResourceSemanticEvaluation (w : World) (γ : Environment) (t : RawTerm)
    (ground : GroundTy) (available : Resources) : Prop :=
  ∀ supplies, Compatible w supplies γ →
    ∃ v owned, Eval supplies γ t v ∧ ResourceInterpretation w ground Mode.identity v owned ∧
      owned ⊆ available ∪ {l | supplies.FreshLocation l}

end ModalityInference.Runtime
