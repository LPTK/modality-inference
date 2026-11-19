import ModalityInference.ComparisonSuffixSyntax

/-! Executable suffix normalization with completed Boolean totality tests. -/
namespace ModalityInference.ComparisonExecutableSuffix

open ComparisonRawCarrierSuffix

def normalize (total : ModExpr → Bool) (m : ModExpr) : Normalized :=
  if total m then ⟨none,m⟩ else
    match m with
    | .compose l r =>
        match (normalize total r).literal with
        | some p => ⟨some (.compose l p),(normalize total r).control⟩
        | none => ⟨(normalize total l).literal,
            .compose (normalize total l).control (normalize total r).control⟩
    | m => ⟨some m,.epsilon⟩

/-- Only composition children can cause further definedness tests. Residual
labels are tested as complete expressions. -/
def tests : ModExpr → List ModExpr
  | .compose l r => .compose l r :: tests l ++ tests r
  | m => [m]

end ModalityInference.ComparisonExecutableSuffix
