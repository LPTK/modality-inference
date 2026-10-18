import ModalityInference.ComparisonPreparedQueries
import ModalityInference.Proofs.ComparisonCheckerTermination

/-! Structural endpoint preparation reaches a fixed completed result for every
input. Omitting a rejected alternative preserves completed-result stability;
exhausted alternatives remain pending until their construction finishes. -/
namespace ModalityInference

open ComparisonPartialPropagation.Fuel

namespace ComparisonStructuralActions

theorem prepareAction_settles (b : ComparisonControls.Basis) (m : ModExpr) :
    Settles (fun fuel => prepareAction fuel b m) := by
  unfold prepareAction
  apply Settles.bind (ComparisonControls.low_settles _ _)
  intro lower
  apply Settles.bind (ComparisonControls.high_settles _ _)
  intro upper
  exact Settles.pure _

theorem prepare_settles (left right : ComparisonControls.Basis) (m : ModExpr) :
    Settles (fun fuel => prepare fuel left right m) := by
  unfold prepare
  apply Settles.bind (prepareAction_settles _ _)
  intro lower
  apply Settles.bind (prepareAction_settles _ _)
  intro upper
  exact Settles.pure _

end ComparisonStructuralActions

namespace ComparisonStructuralNormalization

theorem constructor_settles (names : List TypeVar) (modes : List ModVar)
    (shapes : TypeVar → ComparisonShape) (s t : ComparisonShape)
    (op : CompareTy → CompareTy → CompareTy) (sign : Bool → Bool) (a b : CompareTy) :
    Settles (fun _ => constructor names modes shapes s t op sign a b) := by
  unfold constructor
  split
  · split
    · exact Settles.pure _
    · exact Settles.rejected _
  · exact Settles.rejected _

theorem modal_settles (names : List TypeVar) (modes : List ModVar)
    (shapes : TypeVar → ComparisonShape) (shape : ComparisonShape)
    (a : CompareTy) (m : ModExpr) :
    Settles (fun fuel => modal fuel names modes shapes shape a m) := by
  unfold modal
  split
  · exact Settles.rejected _
  · split
    · exact Settles.rejected _
    · apply Settles.bind (ComparisonStructuralActions.prepareAction_settles _ _)
      intro action
      split
      · exact Settles.pure _
      · exact Settles.rejected _

theorem run_settles (names : List TypeVar) (modes : List ModVar)
    (shapes : TypeVar → ComparisonShape) (a : CompareTy) :
    Settles (fun fuel => run fuel names modes shapes a) := by
  induction a with
  | var v => exact Settles.pure _
  | unit => exact Settles.pure _
  | credit => exact Settles.pure _
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
      simp only [run]
      apply Settles.bind iha
      intro x
      apply Settles.bind ihb
      intro y
      exact constructor_settles _ _ _ _ _ _ _ _ _
  | join a b iha ihb | meet a b iha ihb =>
      simp only [run]
      apply Settles.bind iha
      intro x
      apply Settles.bind ihb
      intro y
      exact Settles.pure _
  | modal a m ih =>
      simp only [run]
      apply Settles.bind ih
      intro x
      exact modal_settles _ _ _ _ _ _

end ComparisonStructuralNormalization

namespace ComparisonStructuralEndpoints

theorem normalizePair_settles (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (pair : CompareTy × CompareTy) :
    Settles (fun fuel => normalizePair fuel p solved pair) := by
  unfold normalizePair
  apply Settles.bind (ComparisonStructuralNormalization.run_settles _ _ _ _)
  intro left
  apply Settles.bind (ComparisonStructuralNormalization.run_settles _ _ _ _)
  intro right
  exact Settles.pure _

theorem normalizeList_settles (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (pairs : List (CompareTy × CompareTy)) :
    Settles (fun fuel => normalizeList fuel p solved pairs) := by
  induction pairs with
  | nil => exact Settles.pure _
  | cons pair rest ih =>
      unfold normalizeList
      apply Settles.bind (normalizePair_settles _ _ _)
      intro head
      apply Settles.bind ih
      intro tail
      exact Settles.pure _

theorem run_settles (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (action : CompareSubstitution) :
    Settles (fun fuel => run fuel p solved action) := normalizeList_settles _ _ _

end ComparisonStructuralEndpoints

namespace ComparisonStructuralCoherence

theorem run_settles (assumptions : Bounds)
    (endpoints : ComparisonShape → List (CompareTy × CompareTy))
    (layout : ComparisonStructuralLayout.Layout) :
    Settles (fun fuel => run fuel assumptions endpoints layout) := by
  unfold run
  split
  · exact Settles.rejected _
  · exact compact_settles _ _

end ComparisonStructuralCoherence

namespace ComparisonSignedEndpoints

theorem compileGuards_settles (clauses : List Clause) :
    Settles (fun fuel => compileGuards fuel clauses) := by
  induction clauses with
  | nil => exact Settles.pure _
  | cons clause rest ih =>
      unfold compileGuards
      apply Settles.bind (compact_settles _ _)
      intro guards
      apply Settles.bind ih
      intro tail
      exact Settles.pure _

end ComparisonSignedEndpoints

namespace ComparisonPreparedQueries

private theorem optional_settles {α β : Type} {f : Nat → RunResult α}
    {g : Nat → α → RunResult (Option β)} (hf : Settles f)
    (hg : ∀a, Settles (fun fuel => g fuel a)) :
    Settles (fun fuel => match f fuel with
      | .exhausted => .exhausted
      | .rejected _ => .success none
      | .success a => g fuel a) := by
  apply Settles.inspect (g := fun fuel result => match result with
    | .exhausted => .exhausted
    | .rejected _ => .success none
    | .success a => g fuel a) hf (fun _ => rfl)
  intro result hr
  cases result with
  | success a => exact hg a
  | rejected reason => exact Settles.pure _
  | exhausted => exact False.elim (hr rfl)

theorem branch_settles (first activation : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (declared : List ComparisonStructuralEndpoints.Pair)
    (endpoint : Ty × Ty) (b : ComparisonSelectedBases.Branch) :
    Settles (fun fuel => branch fuel first activation p solved declared endpoint b) := by
  unfold branch
  split
  · exact Settles.pure _
  · rename_i layout hlayout
    refine Settles.congr (optional_settles (α := CNF) (β := Alternative)
      (f := fun fuel => ComparisonStructuralCoherence.run fuel p.assumptions
        (ComparisonStructuralEndpoints.atShape declared) layout)
      (g := fun fuel theory => do
      let original ← ComparisonSignedEndpoints.compileGuards fuel
        (ComparisonSignedEndpoints.compile (ComparisonSelectedBases.inputTypeKeys p)
          (ComparisonSignedObservation.context layout ModExpr.var) endpoint.1 endpoint.2)
      match ComparisonSignedBranchCalls.compile
          (ComparisonSignedBranchImages.entries first p solved) layout original with
      | none => return none
      | some clauses => return some ⟨activation,b,endpoint,layout,theory,original,clauses⟩)
      (ComparisonStructuralCoherence.run_settles _ _ _) ?_) ?_
    · intro theory
      apply Settles.bind (ComparisonSignedEndpoints.compileGuards_settles _)
      intro original
      split <;> exact Settles.pure _
    · intro fuel
      dsimp only
      cases ComparisonStructuralCoherence.run fuel p.assumptions
        (ComparisonStructuralEndpoints.atShape declared) layout <;> rfl

theorem alternatives_settles (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (declared : List ComparisonStructuralEndpoints.Pair)
    (endpoint : Ty × Ty) (activation : Nat) (bs : List ComparisonSelectedBases.Branch) :
    Settles (fun fuel => alternatives fuel first p solved declared endpoint activation bs) := by
  induction bs generalizing activation with
  | nil => exact Settles.pure _
  | cons b bs ih =>
      unfold alternatives
      apply Settles.bind (branch_settles _ _ _ _ _ _ _)
      intro head
      apply Settles.bind (ih _)
      intro tail
      exact Settles.pure _

theorem groups_settles (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (declared : List ComparisonStructuralEndpoints.Pair)
    (next : Nat) (endpoints : List (Ty × Ty)) :
    Settles (fun fuel => groups fuel first p solved declared next endpoints) := by
  induction endpoints generalizing next with
  | nil => exact Settles.pure _
  | cons endpoint rest ih =>
      unfold groups
      apply Settles.bind (alternatives_settles _ _ _ _ _ _ _)
      intro choices
      apply Settles.bind (ih _)
      intro tail
      exact Settles.pure _

theorem compile_settles (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) :
    Settles (fun fuel => compile fuel first p solved) := by
  unfold compile
  apply Settles.bind (ComparisonStructuralEndpoints.normalizeList_settles _ _ _)
  intro declared
  apply Settles.bind (groups_settles _ _ _ _ _ _)
  intro groups
  apply Settles.bind (compact_settles _ _)
  intro condition
  exact Settles.pure _

theorem compile_terminates (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) :
    ∃threshold result, result ≠ .exhausted ∧
      ∀fuel ≥ threshold, compile fuel first p solved = result :=
  (compile_settles first p solved).2

theorem compile_stable {small large first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {result : RunResult Program}
    (h : compile small first p solved = result) (hr : result ≠ .exhausted) (hle : small ≤ large) :
    compile large first p solved = result :=
  (compile_settles first p solved).1 hle h hr

end ComparisonPreparedQueries

end ModalityInference
