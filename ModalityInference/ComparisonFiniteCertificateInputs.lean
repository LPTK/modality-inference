import ModalityInference.ComparisonObserverBoundary
import ModalityInference.ComparisonExecutableSuffix
import ModalityInference.ScalarDecision

/-! Deterministic syntax support for the finite comparison construction. -/
namespace ModalityInference.ComparisonFiniteCertificateInputs

abbrev Site := Ty × Option ModExpr

def applyPrefix : Option ModExpr → Ty → Ty
  | none, a => a
  | some p, a => .modal a p

def calls (Δ : Bounds) : Ty → Option ModExpr → List Site
  | a, p => (a,p) :: match a,p with
    | .modal a m, none => calls Δ a (ComparisonExecutableSuffix.normalize (ScalarDecision.defined Δ) m).literal
    | .modal a m, some p => calls Δ a (some (.compose m p))
    | .prod a b, p | .sum a b, p => calls Δ a p ++ calls Δ b p
    | .fn a b, none => calls Δ a none ++ calls Δ b none
    | _, _ => []

def support (queries : List CompareTy) : List Ty := queries.flatMap fun a =>
  (ComparisonObserverBoundary.typeList a).dedup.map (fun v => (show Ty from .var v)) ++
  (ComparisonObserverBoundary.modeList a).dedup.map (fun v => (show Ty from .modal .unit (.var v)))

def boundInputs (Δ : Bounds) : List Ty := Δ.flatMap fun c => match c with
  | .sub a b => [a,b]
  | _ => []

def sites (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) : List Site :=
  (boundInputs Δ ++ (raw ++ support queries)).flatMap fun a => calls Δ a none

def controlNames (Δ : Bounds) : Site → List ModVar
  | (.modal _ m,none) =>
      (ComparisonExecutableSuffix.normalize (ScalarDecision.defined Δ) m).control.freeVariables.dedup
  | _ => []

def names (Δ : Bounds) (sites : List Site) : List ModVar :=
  Δ.modeVariables.dedup ++
    (sites.map fun s => applyPrefix s.2 s.1).flatMap (fun a => a.modeVariables.dedup) ++
    sites.flatMap (controlNames Δ)

def sourceNames (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) : List ModVar :=
  names Δ (sites Δ raw queries)

end ModalityInference.ComparisonFiniteCertificateInputs
