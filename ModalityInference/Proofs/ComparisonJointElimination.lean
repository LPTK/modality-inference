import ModalityInference.ComparisonJointElimination
import ModalityInference.Proofs.ComparisonJointBatchReification
import ModalityInference.Proofs.ComparisonReductionClosure

/-! Actual stages of shared elimination and their original scalar obligations. -/
namespace ModalityInference.ComparisonJointElimination

open ComparisonJointBatchReification ComparisonJointAssemblyReification

structure Trace (fuel : Nat) (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (templates : ComparisonSkeleton.Templates)
    (reduced : ComparisonReduction.State) (allowed : List ModVar) (modeIds : List Nat)
    (minimumModes : Nat) (output : Output) where
  groups : List ComparisonGroups.Group
  compiled : List Compiled
  scalar : CNF
  batch : ComparisonJointBatch.Result (entries compiled) (SchemeModeSynthesis.atoms modeIds)
  collection : ComparisonGroups.collect p shapes templates reduced = .success groups
  preparation : prepare fuel p.assumptions reduced.modes groups = .success compiled
  scalar_eq : CompactCNF.toCNF fuel true
    (.imp (boundsModeFormula p.assumptions) (boundsModeFormula reduced.modes)) = .success scalar
  batch_eq : ComparisonJointBatch.run fuel ModalSynthesis.locality (SchemeModeSynthesis.atoms modeIds)
    (entries compiled) minimumModes scalar = .success batch
  assembly : assemble allowed modeIds compiled batch minimumModes = some output

theorem run_trace {fuel p shapes templates reduced allowed modeIds minimumModes output}
    (h : run fuel p shapes templates reduced allowed modeIds minimumModes = .success output) :
    Nonempty (Trace fuel p shapes templates reduced allowed modeIds minimumModes output) := by
  simp only [run, bind, RunResult.bind] at h
  repeat' first | contradiction | cases h | split at h
  rename_i _ groups hc _ compiled hp _ scalar hs _ batch hb _ ha
  exact ⟨⟨groups, compiled, scalar, batch, hc, hp, hs, hb, ha⟩⟩

theorem Trace.scalar_guards {fuel p shapes templates reduced allowed modeIds minimumModes output}
    (t : Trace fuel p shapes templates reduced allowed modeIds minimumModes output)
    (hfixed : ∀ v ∈ p.assumptions.modVars,
      v ∈ allowed ∧ ∀ a < 3, v.atomIndex a ∉ SchemeModeSynthesis.atoms modeIds)
    (hrequired : ∀ v ∈ reduced.modes.modVars, v ∈ allowed ∨ ∃ n ∈ modeIds, v = .flex n) :
    ∀ η, ModeModels p.assumptions η → ModeModels (output.modeAction.bounds reduced.modes) η := by
  apply projected_scalar_guards (assemble_spec t.assembly).1 hfixed hrequired
  intro world
  have h := (CompactCNF.toCNF_correct t.scalar_eq _).mp
    (ComparisonJointBatch.run_scalar t.batch_eq world)
  simpa only [BoolExpr.eval_imp_true] using h

theorem Trace.scalar_entails {fuel p shapes templates reduced allowed modeIds minimumModes output}
    (t : Trace fuel p shapes templates reduced allowed modeIds minimumModes output)
    (hs : ComparisonReduction.ScalarModes reduced)
    (hfixed : ∀ v ∈ p.assumptions.modVars,
      v ∈ allowed ∧ ∀ a < 3, v.atomIndex a ∉ SchemeModeSynthesis.atoms modeIds)
    (hrequired : ∀ v ∈ reduced.modes.modVars, v ∈ allowed ∨ ∃ n ∈ modeIds, v = .flex n) :
    AlgebraEntailsAll p.assumptions (output.substitution.bounds reduced.modes) := by
  apply ComparisonReduction.scalarModes_entails hs
  · intro a b hab
    apply Submode.valid
    intro η hη
    exact t.scalar_guards hfixed hrequired η hη _ (List.mem_map.mpr ⟨.mode a b, hab, rfl⟩)
  · intro m hm η hη
    exact t.scalar_guards hfixed hrequired η hη _ (List.mem_map.mpr ⟨.defined m, hm, rfl⟩)

end ModalityInference.ComparisonJointElimination
