import ModalityInference.ComparisonRawContext

/-! Raw context normalization preserves every input name using inert self-facts.
Fresh quantified namespaces are therefore unchanged by deleting redundant edges. -/
namespace ModalityInference.ComparisonAmbientNormalization

def names (Δ : Bounds) : Bounds :=
  Δ.typeVariables.map (fun v => .sub (.var v) (.var v)) ++
    Δ.modeVariables.map (fun v => .mode (.var v) (.var v))

def normalize (Δ : Bounds) : Bounds := ComparisonRawContext.prune Δ ++ names Δ

end ModalityInference.ComparisonAmbientNormalization
