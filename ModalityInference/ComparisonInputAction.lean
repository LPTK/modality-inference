import ModalityInference.ComparisonSelectedBases

/-! A prepared action needs type assignments only for its flexible input names
above the fixed namespace. All other type lookups retain their identity. -/
namespace ModalityInference.ComparisonSelectedBases

def inputTypeKeys (p : SchemePreparation.Prepared) : List Nat :=
  (inputNames p).filterMap fun v => match v with
    | .rigid _ => none
    | .flex n => if p.firstType≤n then some n else none

def inputAction (p : SchemePreparation.Prepared) (σ : CompareSubstitution) : CompareSubstitution :=
  { types := (inputTypeKeys p).map fun n => (n,σ.type (.flex n))
    modes := σ.modes }

end ModalityInference.ComparisonSelectedBases
