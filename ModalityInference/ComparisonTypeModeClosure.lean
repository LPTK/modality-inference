import ModalityInference.ComparisonTypes

/-! Apply the shared modality action to every reconstructed type image while
retaining the original substitution domains and modality images. -/
namespace ModalityInference.CompareSubstitution

def closeTypeModes (σ : CompareSubstitution) : CompareSubstitution :=
  { types := σ.types.map fun (n, a) => (n, a.subst CompareTy.var σ.mode)
    modes := σ.modes }

end ModalityInference.CompareSubstitution
