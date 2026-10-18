import ModalityInference.ComparisonPreparedScalar

/-! Scalar feasibility precedes structural query construction. The preflight
checks only necessary guards and discards its witness; the final comparison
still synthesizes one shared type and modality substitution. -/
namespace ModalityInference.ComparisonPreparedScalarPreflight

def formula (p : SchemePreparation.Prepared) : BoolExpr :=
  .imp (boundsModeFormula p.assumptions)
    (boundsModeFormula (ComparisonPreparedScalar.required p))

def run (fuel : Nat) (p : SchemePreparation.Prepared) : RunResult Unit := do
  let _ ← SchemeModeSynthesis.run fuel (ComparisonPreparedScalar.modeIds p) (formula p)
  return ()

end ModalityInference.ComparisonPreparedScalarPreflight
