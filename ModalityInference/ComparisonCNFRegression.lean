import ModalityInference.ComparisonJointChecker

/-! Executable coverage for canonicalization and selector-guarded comparison. -/
namespace ModalityInference.ComparisonCNFRegression

open ComparisonPropagation

#guard project [0] [[(0, true), (1, true)], [(0, false), (2, true)], [(3, true)]] =
  [[(1, true), (2, true)], [(3, true)]]
#guard project [0] [[(0, true)], [(0, false)]] = [[]]

#guard join [[(0, true)], [(1, true)]] [[(0, true)], [(2, true)]] =
  [[(0, true)], [(1, true), (2, true)]]
#guard join [] [[(0, true)]] = []
#guard join [[]] [[(0, true)]] = [[(0, true)]]
#guard (initial 2 (Vector.replicate 1 [[]]))[0] = seed 2
#guard (initial 2 (Vector.replicate 1 [[(0, true)]]))[0] = [[(0, true)]]

#guard CompactCNF.clean [[(2, true), (1, false), (2, true)],
  [(1, false)], [(0, false), (0, true)]] = [[(1, false)]]
#guard CompactCNF.clean (List.replicate 50000 [(0, true)]) = [[(0, true)]]

-- The selector theory is conjoined once, without expanding its negation.
def manySelectors : Program 0 := { Program.empty 0 with checks := [[(1, true)]] }
#guard (ComparisonSelectorPropagation.query 0 64 manySelectors).length = 129
#guard (ComparisonSelectorPropagation.run 500 0 64 manySelectors).isSuccess

def residual : ModExpr := .leftResidual (.var (.rigid 0)) .bottom
def source : Scheme := ⟨[], [0], [], .modal (.var (.rigid 0)) (.var (.flex 0))⟩
def target : Scheme := ⟨[], [], [.defined residual], .modal (.var (.rigid 0)) residual⟩

#guard (ComparisonJointChecker.run 20000 source target).isSuccess
#guard match ComparisonJointChecker.run 20000 source {target with bounds := []} with
  | .rejected _ => true
  | _ => false

end ModalityInference.ComparisonCNFRegression
