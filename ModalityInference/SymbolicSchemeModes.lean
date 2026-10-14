import ModalityInference.SymbolicModes

/-! Finite assembly of symbolic modality witnesses. Each pair names an original
quantified parameter and the fresh variable whose symbolic image it receives. -/
namespace ModalityInference.SymbolicSchemeModes

def entries {flex} (s : SymbolicModes.Elimination flex) :
    List (Nat × ModVar) → Option (List (Nat × ModExpr))
  | [] => some []
  | (key, v) :: rest => do
    let m ← s.mode v
    let ms ← entries s rest
    return (key, m) :: ms

/-- Failed reification is explicit; no concrete assignment fills a missing image. -/
def assemble {flex} (s : SymbolicModes.Elimination flex)
    (parameters : List (Nat × ModVar)) : Option Substitution := do
  let ms ← entries s parameters
  return {modes := ms}

end ModalityInference.SymbolicSchemeModes
