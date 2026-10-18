import ModalityInference.ComparisonSignedQueries

/-! Shared constant selectors are chosen after compiling every nominal relation
and the common scalar query. All finite type images then use that same choice. -/
namespace ModalityInference.ComparisonSignedQuerySolver
open ComparisonPropagation ComparisonSignedSynthesis ComparisonSignedQueries

structure Solution where
  selectors : CNFPropagation.Assignment
  images : List (Nat × CompareTy)

def parameter (v : Nat) : Sum Bool Nat :=
  if v%3=2 then .inr (v/3) else .inl false

def condition (input : Input) (r scalar : CNF) : CNF :=
  ComparisonSignedPolynomials.specialize parameter (input.consistent r) ++ scalar

def run (fuel : Nat) (input : Input) (queries : List Query) (scalar : CNF) : RunResult Solution := do
  let r ← match ComparisonSignedQueries.compile input queries with
    | some r => .success r
    | none => .rejected "nonbinary signed comparison query"
  let selectors ← CNFPropagation.solve fuel (condition input r scalar)
  match input.reconstruct r (CNFPropagation.valuation selectors) with
  | some images => return ⟨selectors,images⟩
  | none => .rejected "signed image reconstruction failed"

end ModalityInference.ComparisonSignedQuerySolver
