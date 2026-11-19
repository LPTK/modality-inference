import ModalityInference.ComparisonObserverBoundary
import ModalityInference.ComparisonFiniteCertificate

/-! Input data for explicit finite-certificate bounds. These estimates describe
reference certificates, independently of the production witness-search policy. -/
namespace ModalityInference.ComparisonFiniteCertificateBounds

def inputModes (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) : Finset ModVar :=
  Δ.modVars ∪ ComparisonObserverBoundary.allModes (raw.map CompareTy.ofTy ++ queries)

def controlBound (names : Nat) : Nat :=
  2 ^ (2 ^ names + 2 * 2 ^ (2 * names))

def rawSize (a : Ty) : Nat := (ComparisonObserverBoundary.subterms (.ofTy a)).length

def inputNodes (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) : Nat :=
  (ComparisonObserverBoundary.closure
    (ComparisonObserverBoundary.declaredTypes Δ ++ raw.map CompareTy.ofTy)).length +
    (queries.map fun q => (ComparisonObserverBoundary.types q).card +
      2 * (ComparisonObserverBoundary.modes q).card).sum

def nameBound (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) : Nat :=
  (1 + 2 * inputNodes Δ raw queries) * (inputModes Δ raw queries).card

def controlsBound (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) : Nat :=
  controlBound (nameBound Δ raw queries)

def diagramNodes (heads controls queryNodes : Nat) : Nat :=
  let points := heads * controls
  (points * 2) * (points * 2 * 2) +
    (controls * (points * 6) + (heads * (2 * (heads + 2)) + controls * heads ^ 3 * 30)) +
    (points * 2 + queryNodes)

def stateBound (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) : Nat :=
  2 ^ (2 * (8 + 10 * (inputModes Δ raw queries).card) + 2 +
    diagramNodes (inputNodes Δ raw queries) (controlsBound Δ raw queries)
      (ComparisonObserverBoundary.closure queries).length)

def tagsBound (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) : Nat :=
  2 ^ stateBound Δ raw queries + inputNodes Δ raw queries * controlsBound Δ raw queries

def observationsBound (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) : Nat :=
  2 ^ tagsBound Δ raw queries

/-- Input bounds on the carrier dimensions and modality-name list. Literal,
frozen, and machine-name tables have separate finite-support obligations. -/
def WithinDimensions {Δ : Bounds} {names : List ModVar}
    (raw : List Ty) (queries : List CompareTy) (C : ComparisonFiniteCertificate.Candidate Δ names) : Prop :=
  names.length ≤ nameBound Δ raw queries ∧ names.toFinset ⊆ inputModes Δ raw queries ∧
    C.states ≤ stateBound Δ raw queries ∧ C.tags ≤ tagsBound Δ raw queries ∧
    C.observations ≤ observationsBound Δ raw queries

end ModalityInference.ComparisonFiniteCertificateBounds
