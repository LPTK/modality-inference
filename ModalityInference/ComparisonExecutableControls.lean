import ModalityInference.ComparisonFiniteControlEncoding

/-! Executable control order for the function rule. The top adjustment is
part of the original rule and is distinct from ordinary control order. -/
namespace ModalityInference.ComparisonExecutableControls

open ComparisonFiniteControlEncoding

def future {Δ : Bounds} {names : List ModVar} (m n : Code Δ names) : Bool :=
  order m (n * top Δ names)

end ModalityInference.ComparisonExecutableControls
