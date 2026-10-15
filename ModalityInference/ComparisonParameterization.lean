import ModalityInference.ComparisonPreparation

/-! A symbolic comparison context becomes a fresh scheme-comparison problem.
Its auxiliary modalities are solved together with every original obligation. -/
namespace ModalityInference.ComparisonParameterization

abbrev Prepared := SchemePreparation.Prepared

def source (p : Prepared) (before : Substitution) (fresh : List Nat)
    (extra : Bounds := []) : Scheme :=
  { typeParams := List.range' p.firstType (p.nextType - p.firstType)
    modParams := List.range' p.firstMode (p.nextMode - p.firstMode) ++ fresh
    bounds := before.bounds p.sourceBounds ++ extra
    body := before.ty p.sourceType }

/-- The target has already been skolemized; its written bounds are expanded
exactly once by the inner comparison. -/
def target (p : Prepared) (original : Scheme) : Scheme :=
  { bounds := p.targetRenaming.bounds original.bounds
    body := p.targetType }

end ModalityInference.ComparisonParameterization
