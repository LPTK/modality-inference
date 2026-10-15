import ModalityInference.ComparisonExactContext
import ModalityInference.ComparisonReduction
import ModalityInference.ComparisonGuardedTotal

namespace ModalityInference.ComparisonChecker

/-- The deterministic preparations performed between scalar discovery and
structural reduction. -/
structure Setup where
  original : SchemePreparation.Prepared
  before : Substitution
  shapes : ComparisonShapeSolver.Solved
  known : List ModExpr
  shared : Bool

def Setup.input (s : Setup) : SchemePreparation.Prepared :=
  ComparisonExactContext.rewrite s.original s.before

def Setup.total (s : Setup) : ModExpr → Bool := ComparisonBody.isTotal s.known

def Setup.absorption (s : Setup) : ComparisonAbsorption.Result :=
  ComparisonAbsorption.plan s.input s.total

def Setup.absorbed (s : Setup) : SchemePreparation.Prepared :=
  { s.input with sourceType := s.absorption.body }

def Setup.annotations (s : Setup) : ComparisonPartialModes.Result :=
  ComparisonAnnotations.prepare s.absorbed s.total

def Setup.work (s : Setup) : SchemePreparation.Prepared :=
  { s.absorbed with sourceType := s.annotations.substitution.ty s.absorbed.sourceType }

def Setup.bare (s : Setup) : List Nat :=
  (if s.shared then ComparisonBody.eligible s.work s.total else ComparisonPartial.eligible s.work).filter
    (fun n => !(s.before.types.map Prod.fst).contains n)

def Setup.names (s : Setup) : List Nat :=
  (List.range' s.original.firstType (s.original.nextType - s.original.firstType)).filter
    (fun n => !(s.before.types.map Prod.fst).contains n && !s.bare.contains n)

def Setup.templates (s : Setup) : ComparisonSkeleton.Templates :=
  ComparisonSkeleton.allocate s.work s.shapes s.names s.original.nextType s.annotations.nextMode

def Setup.reduced (s : Setup) (result : ComparisonReduction.State) : ComparisonReduction.State :=
  { result with modes :=
    (s.annotations.bounds ++ ComparisonGuardedTotal.scalarBounds s.input.sourceBounds) ++ result.modes }

def Setup.modeIds (s : Setup) : List Nat :=
  (List.range' s.original.firstMode (s.templates.nextMode - s.original.firstMode)).filter
    (fun n => !(s.before.modes.map Prod.fst ++ s.absorption.modes ++
      s.annotations.images.map Prod.fst).contains n)

end ModalityInference.ComparisonChecker
