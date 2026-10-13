import ModalityInference.Proofs.SolverEntry
import ModalityInference.Proofs.GroundOrder

/-! Accumulated substitutions must be applied before checking finite type shape. -/
namespace ModalityInference

theorem GroundOrder.nodes_eq {a b} (h : GroundOrder a b) : a.nodes = b.nodes := by
  induction h <;> simp_all [GroundTy.nodes]

namespace ShapeEntry

private def tv (n : Nat) : Ty := .var (.flex n)

def input : SolverState := {
  pending := [.sub (tv 1) (tv 2), .sub (tv 2) (tv 0)]
  substitution := { types := [(0, .prod (tv 1) .unit)] }
  nextType := 3
}

/-- The former entry checked uninstantiated constraints after validating the
accumulated substitution. Its two checks miss cycles crossing that boundary. -/
def formerRunSolver (fuel : Nat) (s : SolverState) : RunResult SolverState := do
  if !s.substitution.checkAcyclic then
    return ← .rejected "initial solver substitution is cyclic, duplicated, or not normalized"
  checkShapes fuel (s.pending ++ s.bounds)
  runWorklist fuel s

theorem acyclic : input.substitution.Acyclic :=
  input.substitution.checkAcyclic_iff.mp rfl

theorem raw_shape_precheck (fuel : Nat) :
    checkShapes (fuel + 3) (input.pending ++ input.bounds) = .success () := rfl

theorem substituted_shape_precheck (fuel : Nat) :
    checkShapes (fuel + 2) (input.substitution.bounds (input.pending ++ input.bounds)) =
      .rejected "occurs check failed through type-bound cycle" := rfl

theorem former_exhausted_twenty : formerRunSolver 20 input = .exhausted := by rfl

theorem corrected_rejects (fuel : Nat) : runSolver (fuel + 2) input =
    .rejected "occurs check failed through type-bound cycle" := rfl

theorem empty_substitution_unchanged {fuel s} (hσ : s.substitution = {}) :
    runSolver fuel s = formerRunSolver fuel s := by
  simp [runSolver, formerRunSolver, hσ]

theorem no_substituted_model :
    ¬ ∃ ρ, GroundModels ρ (input.substitution.bounds (input.pending ++ input.bounds)) := by
  rintro ⟨ρ, hρ⟩
  have hab := hρ (.sub (tv 1) (tv 2)) List.mem_cons_self
  have hba := hρ (.sub (tv 2) (.prod (tv 1) .unit))
    (List.mem_cons_of_mem _ List.mem_cons_self)
  simp [GroundSatisfies, TypeExpr.realize, tv] at hab hba
  have hab' := (GroundOrder.of_subtype hab).nodes_eq
  have hba' := (GroundOrder.of_subtype hba).nodes_eq
  simp only [GroundTy.nodes] at hba'
  omega

end ShapeEntry
end ModalityInference
