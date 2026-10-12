import ModalityInference.Semantics

/-! Ownership evidence for polymorphic values is indexed by their ground instance.

The runtime value contains no authoritative ownership annotations. Instead, the
logical relation records a set of owned locations with each instance. Products
and sums propagate the full field types, credits own their cell exactly when
unique, and closures own a subset of their actual captures. Closure application
must account for every owned result location. This permits different instances
of the same erased closure to carry different proof evidence without changing
evaluation, allocation, or the source language.
-/
namespace ModalityInference

abbrev Resources := Set Location

def cellResources (m : Mode) (l : Location) : Resources :=
  if m.unique then {l} else ∅

/-- A ground value together with its erasable ownership evidence. Recursion is
on the ground type; the function clause uses the independent operational semantics. -/
def ResourceInterpretation (w : World) (t : GroundTy) (ambient : Mode)
    (v : Value) (owned : Resources) : Prop :=
  let m := t.mode.compose ambient
  w.ValidValue v ∧ (∀ l ∈ owned, References v l) ∧ match t, v with
  | .unit _, .unit => owned = ∅
  | .credit _, .credit l =>
      (m.isLocal = true ∨ HeapLocation l) ∧ owned = cellResources m l
  | .prod a b _, .pair l x y =>
      (m.isLocal = true ∨ HeapLocation l) ∧
      ∃ first second,
        ResourceInterpretation w a m x first ∧ ResourceInterpretation w b m y second ∧
        Disjoint (cellResources m l) first ∧ Disjoint (cellResources m l) second ∧
        Disjoint first second ∧ owned = cellResources m l ∪ first ∪ second
  | .sum a _ _, .inl x => ResourceInterpretation w a m x owned
  | .sum _ b _, .inr x => ResourceInterpretation w b m x owned
  | .fn a b _, .closure γ _ body =>
      (m.isLocal = false → ∀ l, EnvironmentReferences γ l → HeapLocation l) ∧
      (m.once = false → owned = ∅) ∧
      (∀ (w' : World) x argument,
        (∀ v ∈ γ, w'.ValidValue v) →
        ResourceInterpretation w' a Mode.identity x argument →
        Disjoint owned argument →
        ∀ supplies, w'.Compatible supplies (x :: γ) →
        ∃ result resources, Eval supplies (x :: γ) body result ∧
          ResourceInterpretation w' b Mode.identity result resources ∧
          resources ⊆ owned ∪ argument ∪ {l | supplies.FreshLocation l})
  | _, _ => False

/-- A binding reserves enough ownership for every admissible instance. Each use
selects the resources appropriate to its own ground type. -/
def ResourceSchemeInterpretation (ρ : GroundAssignment) (w : World)
    (s : Scheme) (v : Value) (reserved : Resources) : Prop :=
  (∀ l ∈ reserved, References v l) ∧
  ∀ η t, GroundInstantiates ρ s η → s.body.realize η = some t →
    ∃ owned, owned ⊆ reserved ∧ ResourceInterpretation w t Mode.identity v owned

def ContextResources (Γ : Context) (reserved : Nat → Resources) : Resources :=
  {l | ∃ i s, Γ[i]? = some (some s) ∧ l ∈ reserved i}

def ResourceEnvironmentInterpretation (ρ : GroundAssignment) (w : World)
    (Γ : Context) (γ : Environment) (reserved : Nat → Resources) : Prop :=
  (∀ i s, Γ[i]? = some (some s) →
    ∃ v, γ[i]? = some v ∧ ResourceSchemeInterpretation ρ w s v (reserved i)) ∧
  ∀ i j s t, i ≠ j → Γ[i]? = some (some s) → Γ[j]? = some (some t) →
    Disjoint (reserved i) (reserved j)

def ResourceSemanticEvaluation (w : World) (γ : Environment) (t : AnnotatedTerm)
    (ground : GroundTy) (available : Resources) : Prop :=
  ∀ supplies, w.Compatible supplies γ →
    ∃ v owned, Eval supplies γ t v ∧ ResourceInterpretation w ground Mode.identity v owned ∧
      owned ⊆ available ∪ {l | supplies.FreshLocation l}

end ModalityInference
