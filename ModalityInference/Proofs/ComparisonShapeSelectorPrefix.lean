import ModalityInference.ComparisonPreparedQueries
import ModalityInference.Proofs.ComparisonSelectedPlan
import ModalityInference.Proofs.ComparisonSignedPreparedEndpoints

/-! Shape selectors occupy the prefix ending at their layout's next index.
Changing later activation choices preserves the actual branch guards and the
complete shared selector formula. Endpoint scope follows from preparation. -/
namespace ModalityInference

namespace ComparisonShapeSelectors

theorem Layout.theory_prefix {layout : Layout} {world other : Nat → Bool}
    (h : ∀n<layout.next, world n=other n) :
    layout.theory.eval world=layout.theory.eval other :=
  SymbolicModes.eval_congr _ (fun n hn => h n (layout.theory_atoms n hn).2)

theorem Layout.branches_guard_prefix {layout : Layout} {shape : ComparisonShape}
    (hs : ∀v∈shape.vars, v∈layout.parameters) {branch : Branch}
    (hb : branch∈layout.branches shape) {world other : Nat → Bool}
    (h : ∀n<layout.next, world n=other n) :
    branch.guard.eval world=branch.guard.eval other :=
  SymbolicModes.eval_congr _ (fun n hn => h n (layout.branches_atoms shape hs branch hb n hn).2)

end ComparisonShapeSelectors

namespace ComparisonSelectedBases

theorem selectorFormula_prefix {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world other : Nat → Bool}
    (h : ∀n<(layout first p solved).next, world n=other n) :
    (selectorFormula first p solved).eval world=(selectorFormula first p solved).eval other :=
  SymbolicModes.eval_congr _ (fun n hn => h n (selectorFormula_atoms first p solved n hn).2)

theorem anchorTheory_prefix {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world other : Nat → Bool}
    (h : ∀n<(layout first p solved).next, world n=other n) :
    (anchorTheory first p solved).eval world=(anchorTheory first p solved).eval other :=
  SymbolicModes.eval_congr _ (fun n hn => h n (anchorTheory_atoms first p solved n hn).2)

theorem prepared_guard_prefix {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {v : TypeVar} (hv : v∈inputNames p)
    {branch : Branch} (hb : branch∈prepared first p solved v) {world other : Nat → Bool}
    (h : ∀n<(layout first p solved).next, world n=other n) :
    branch.guard.eval world=branch.guard.eval other :=
  SymbolicModes.eval_congr _ (fun n hn => h n (prepared_atoms hv hb n hn).2)

end ComparisonSelectedBases

namespace ComparisonPreparedQueries

/-- Every actual endpoint branch uses only the original shared selector prefix.
This is a syntactic support property and requires no successful shape solve. -/
theorem branches_guard_atoms {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {endpoint : Ty × Ty}
    (he : endpoint∈ComparisonSignedObservation.endpoints p)
    {branch : ComparisonSelectedBases.Branch} (hb : branch∈branches first p solved endpoint) :
    ∀n∈branch.guard.atoms, first≤n ∧ n<(ComparisonSelectedBases.layout first p solved).next := by
  have hi : ∀v∈endpoint.1.typeVars, v∈ComparisonSelectedBases.inputNames p :=
    fun v hv => (ComparisonSelectedBases.mem_inputNames p v).mpr
      ((ComparisonSignedObservation.endpoints_input he).1 hv)
  exact ComparisonSelectedBases.bases_atoms
    (fun _ => ComparisonSelectedBases.template_scope hi) hb

theorem branches_guard_prefix {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {endpoint : Ty × Ty}
    (he : endpoint∈ComparisonSignedObservation.endpoints p)
    {branch : ComparisonSelectedBases.Branch} (hb : branch∈branches first p solved endpoint)
    {world other : Nat → Bool}
    (h : ∀n<(ComparisonSelectedBases.layout first p solved).next, world n=other n) :
    branch.guard.eval world=branch.guard.eval other :=
  SymbolicModes.eval_congr _ (fun n hn => h n (branches_guard_atoms he hb n hn).2)

theorem source_branches_guard_prefix {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {endpoint : Ty × Ty}
    (he : endpoint∈ComparisonSignedObservation.sourceEndpoints p)
    {branch : ComparisonSelectedBases.Branch} (hb : branch∈branches first p solved endpoint)
    {world other : Nat → Bool}
    (h : ∀n<(ComparisonSelectedBases.layout first p solved).next, world n=other n) :
    branch.guard.eval world=branch.guard.eval other :=
  branches_guard_prefix (List.mem_append_right _ he) hb h

end ComparisonPreparedQueries

end ModalityInference
