import ModalityInference.ComparisonFiniteCertificate
import ModalityInference.ComparisonExecutableSyntaxSupport

/-! Canonical finite lookup fields for a supplied query family. All original
raw subtype bounds are included in the interpreter support. -/
namespace ModalityInference.ComparisonFiniteCertificate

open ComparisonExecutableSyntax

def boundQueries (Δ : Bounds) : List (CompareTy × Option ModExpr) := Δ.flatMap fun c => match c with
  | .sub a b => [(.ofTy a, none), (.ofTy b, none)]
  | _ => []

def queryAccesses (Δ : Bounds) (queries : List (CompareTy × Option ModExpr)) : List Access :=
  accessList (ScalarDecision.defined Δ) (boundQueries Δ ++ queries)

def Candidate.restrictQueries {Δ : Bounds} {names : List ModVar}
    (C : Candidate Δ names) (queries : List (CompareTy × Option ModExpr)) : Candidate Δ names :=
  let keys := queryAccesses Δ queries
  { C with
    prodLiterals := selectRows (literalPrefixes keys) C.prodLiterals
    sumLiterals := selectRows (literalPrefixes keys) C.sumLiterals
    frozen := selectRows (frozenKeys keys) C.frozen }

end ModalityInference.ComparisonFiniteCertificate
