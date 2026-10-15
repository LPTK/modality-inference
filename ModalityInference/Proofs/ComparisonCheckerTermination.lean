import ModalityInference.Proofs.ComparisonReductionTermination
import ModalityInference.Proofs.ComparisonInstance
import ModalityInference.Proofs.CompactCNF
import ModalityInference.Proofs.SchemeModeSynthesis
import ModalityInference.SchemeSubsumption

/-! Fuel stability and eventual completion of the full scheme checker.
Every executed phase reaches a fixed completed result for arbitrary public
schemes. This operational guarantee is separate from subsumption completeness. -/

namespace ModalityInference
private instance : LawfulMonad RunResult := LawfulMonad.mk'
  (id_map := fun x => by cases x <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x _ _ => by cases x <;> rfl)

namespace ComparisonPartialPropagation.Fuel

def Settles {α : Type} (f : Nat → RunResult α) : Prop := Stable f ∧ Terminates f

theorem Terminates.const {α : Type} (result : RunResult α) (h : result ≠ .exhausted) :
    Terminates (fun _ => result) := ⟨0, result, h, fun _ _ => rfl⟩

theorem Terminates.of_stable {α : Type} {f : Nat → RunResult α} (h : Stable f)
    (hn : ∃ n, f n ≠ .exhausted) : Terminates f := by
  obtain ⟨n, hn⟩ := hn
  exact ⟨n, f n, hn, fun _ hf => h hf rfl hn⟩

theorem Settles.const {α : Type} (result : RunResult α) (h : result ≠ .exhausted) :
    Settles (fun _ => result) := ⟨Stable.const result, Terminates.const result h⟩

theorem Settles.pure {α : Type} (value : α) : Settles (fun _ => .success value) :=
  ⟨Stable.pure value, Terminates.pure value⟩

theorem Settles.rejected {α : Type} (message : String) :
    Settles (fun _ => (RunResult.rejected message : RunResult α)) := Settles.const _ (by simp)

theorem Settles.bind {α β : Type} {f : Nat → RunResult α} {g : Nat → α → RunResult β}
    (hf : Settles f) (hg : ∀ a, Settles (fun fuel => g fuel a)) :
    Settles (fun fuel => (f fuel).bind (g fuel)) :=
  ⟨Stable.bind hf.1 (fun a => (hg a).1), Terminates.bind hf.2 (fun a => (hg a).2)⟩

theorem Settles.forIn {α β : Type} (xs : List α)
    (f : Nat → α → β → RunResult (ForInStep β))
    (hf : ∀ a b, Settles (fun fuel => f fuel a b)) (b : β) :
    Settles (fun fuel => forIn xs b (f fuel)) :=
  ⟨Stable.forIn xs f (fun a b => (hf a b).1) b,
    Terminates.forIn xs f (fun a b => (hf a b).2) b⟩

theorem Settles.mapM {α β : Type} (xs : List α) (f : Nat → α → RunResult β)
    (hf : ∀ a, Settles (fun fuel => f fuel a)) :
    Settles (fun fuel => xs.mapM (f fuel)) := by
  induction xs with
  | nil => exact Settles.pure []
  | cons a xs ih =>
    simp only [List.mapM_cons]
    apply Settles.bind (hf a)
    intro b
    apply Settles.bind ih
    intro bs
    exact Settles.pure _

private theorem compact_not_rejected (fuel : Nat) (positive : Bool) (e : BoolExpr)
    (message : String) : CompactCNF.toCNF fuel positive e ≠ .rejected message := by
  induction fuel generalizing positive e message with
  | zero => simp [CompactCNF.toCNF]
  | succ fuel ih =>
    cases positive <;> cases e
    all_goals simp only [CompactCNF.toCNF, bind, pure, RunResult.bind, CompactCNF.cnfOr]
    all_goals repeat' (split <;> try contradiction)
    all_goals simp_all

theorem compact_settles (positive : Bool) (e : BoolExpr) :
    Settles (fun fuel => CompactCNF.toCNF fuel positive e) := by
  constructor
  · intro small large result hle h hr
    cases result with
    | success result => exact CompactCNF.toCNF_monotone h large hle
    | rejected message => exact False.elim (compact_not_rejected small positive e message h)
    | exhausted => exact False.elim (hr rfl)
  · obtain ⟨n, cs, hn⟩ := CompactCNF.toCNF_complete e positive
    exact ⟨n, .success cs, by simp, hn⟩

theorem backend_settles (e : BoolExpr) :
    Settles (fun fuel => ConcreteBackend.decideFormula fuel e) :=
  ⟨backend_stable e, backend_terminates e⟩

theorem boolean_settles (cs : CNF) : Settles (fun fuel => CNFPropagation.solve fuel cs) := by
  have hs : Stable (fun fuel => CNFPropagation.solve fuel cs) :=
    fun hle h hr => CNFPropagation.solve_stable hr h _ hle
  refine ⟨hs, Terminates.of_stable hs ?_⟩
  obtain ⟨n, hn⟩ := CNFPropagation.solve_terminates cs
  exact ⟨n, hn n le_rfl⟩

theorem synthesizeCNF_settles (flex : List Nat) (cs : CNF) :
    Settles (fun fuel => ModalSynthesis.synthesizeCNF fuel flex cs) := by
  unfold ModalSynthesis.synthesizeCNF
  apply Settles.bind (boolean_settles _)
  intro image
  exact Settles.pure _

theorem synthesize_settles (flex : List Nat) (formula : BoolExpr) :
    Settles (fun fuel => ModalSynthesis.synthesize fuel flex formula) := by
  unfold ModalSynthesis.synthesize
  exact Settles.bind (compact_settles _ _) (fun cs => synthesizeCNF_settles flex cs)

theorem modes_settles (modeIds : List Nat) (formula : BoolExpr) :
    Settles (fun fuel => SchemeModeSynthesis.run fuel modeIds formula) := by
  unfold SchemeModeSynthesis.run
  apply Settles.bind (synthesize_settles _ _)
  intro images
  split
  · exact Settles.rejected _
  · exact Settles.pure _

theorem checkTotal_settles (assumptions : Bounds) (expressions : List ModExpr) :
    Settles (fun fuel => ComparisonBody.checkTotal fuel assumptions expressions) := by
  induction expressions with
  | nil => exact Settles.pure []
  | cons m ms ih =>
    unfold ComparisonBody.checkTotal
    apply Settles.bind (backend_settles _)
    intro report
    apply Settles.bind ih
    intro rest
    exact Settles.pure _

theorem knownTotal_settles (assumptions : Bounds) (expressions : List ModExpr) :
    Settles (fun fuel => ComparisonBody.knownTotal fuel assumptions expressions) :=
  checkTotal_settles _ _

theorem Settles.congr {α : Type} {f g : Nat → RunResult α}
    (hf : Settles f) (h : ∀ fuel, g fuel = f fuel) : Settles g := by
  simpa only [funext h] using hf

theorem Settles.inspect {α β : Type} {f : Nat → RunResult α}
    {g : Nat → RunResult α → RunResult β} (hf : Settles f)
    (he : ∀ fuel, g fuel .exhausted = .exhausted)
    (hg : ∀ result, result ≠ .exhausted → Settles (fun fuel => g fuel result)) :
    Settles (fun fuel => g fuel (f fuel)) := by
  constructor
  · intro small large result hle h hr
    have hfe : f small ≠ .exhausted := by
      intro hfe
      simp only [hfe, he] at h
      exact hr h.symm
    have hs := hf.1 hle rfl hfe
    simpa only [hs] using (hg (f small) hfe).1 hle h hr
  · obtain ⟨n, result, hr, hn⟩ := hf.2
    obtain ⟨m, output, ho, hm⟩ := (hg result hr).2
    exact ⟨max n m, output, ho, fun fuel h => by
      simpa only [hn fuel ((Nat.le_max_left _ _).trans h)] using
        hm fuel ((Nat.le_max_right _ _).trans h)⟩

theorem Settles.recover {α : Type} {f : Nat → RunResult α}
    {g : Nat → String → RunResult α} (hf : Settles f)
    (hg : ∀ reason, Settles (fun fuel => g fuel reason)) :
    Settles (fun fuel => match f fuel with
      | .rejected reason => g fuel reason
      | result => result) := by
  apply Settles.inspect (g := fun fuel result => match result with
    | .rejected reason => g fuel reason
    | result => result) hf (fun _ => rfl)
  intro result hr
  cases result with
  | success value => exact Settles.pure value
  | rejected reason => exact hg reason
  | exhausted => exact False.elim (hr rfl)

end ComparisonPartialPropagation.Fuel
namespace ComparisonControls
open ComparisonPartialPropagation.Fuel

theorem compile_settles (basis : Basis) (channel : Channel) (positive : Bool) (e : BoolExpr) :
    Settles (fun fuel => compile fuel basis channel positive e) := by
  unfold compile
  apply Settles.bind (compact_settles _ _)
  intro clauses
  split
  · exact Settles.pure _
  · exact Settles.rejected _

theorem low_settles (basis : Basis) (m : ModExpr) :
    Settles (fun fuel => low fuel basis m) := compile_settles _ _ _ _

theorem high_settles (basis : Basis) (m : ModExpr) :
    Settles (fun fuel => high fuel basis m) := by
  unfold high
  apply Settles.bind (compile_settles _ _ _ _)
  intro locality
  apply Settles.bind (compile_settles _ _ _ _)
  intro affine
  exact Settles.pure _

end ComparisonControls

namespace ComparisonElimination
open ComparisonPartialPropagation.Fuel

theorem controlsTheory_settles (basis : ComparisonControls.Basis) :
    Settles (fun fuel => controlsTheory fuel basis) := by
  unfold controlsTheory
  apply Settles.bind
  · apply Settles.forIn
    intro coordinate clauses
    apply Settles.bind (compact_settles _ _)
    intro next
    exact Settles.pure _
  · intro clauses
    exact Settles.pure _

theorem leaf_settles (basis : ComparisonControls.Basis) (names : List Nat) (v : TypeVar) :
    Settles (fun _ => leaf basis names v) := by
  cases v <;> simp only [leaf]
  all_goals repeat' first | exact Settles.pure _ | exact Settles.rejected _ | split

theorem endpoint_settles (basis : ComparisonControls.Basis) (names : List Nat)
    (a : ComparisonGroups.Atom) : Settles (fun _ => endpoint basis names a) := by
  unfold endpoint
  apply Settles.bind (leaf_settles _ _ _)
  intro value
  exact Settles.pure _

theorem bound_settles (basis : ComparisonControls.Basis) (names : List Nat)
    (a : ComparisonGroups.Inequality) : Settles (fun _ => bound basis names a) := by
  unfold bound
  apply Settles.bind (endpoint_settles _ _ _)
  intro left
  apply Settles.bind (endpoint_settles _ _ _)
  intro right
  exact Settles.pure _

theorem reduce_settles {count : Nat} (basis : List CompareTy)
    (program : ComparisonPropagation.Program count) :
    Settles (fun _ => ComparisonPropagation.reduce basis program) := by
  simp only [ComparisonPropagation.reduce]
  split
  · exact Settles.rejected _
  · exact Settles.pure _

theorem group_settles (assumptions required : Bounds) (g : ComparisonGroups.Group) :
    Settles (fun fuel => group fuel assumptions required g) := by
  cases he : g.heads with
  | nil => simpa only [group, he] using Settles.rejected "comparison class has no fixed generator"
  | cons first rest =>
    simp only [group, he, bind, pure, RunResult.bind]
    apply Settles.bind
    · apply Settles.forIn
      intro label actions
      apply Settles.bind (ComparisonControls.low_settles _ _)
      intro lower
      apply Settles.bind (ComparisonControls.high_settles _ _)
      intro upper
      exact Settles.pure _
    · intro actions
      apply Settles.bind (controlsTheory_settles _)
      intro initialTheory
      apply Settles.bind (compact_settles _ _)
      intro guards
      apply Settles.bind
      · apply Settles.forIn
        intro pair theory
        apply Settles.bind (endpoint_settles _ _ _)
        intro a
        apply Settles.bind (endpoint_settles _ _ _)
        intro b
        cases ha : a.leaf with
        | flex i => exact Fin.elim0 i
        | fixed x =>
          cases hb : b.leaf with
          | flex i => exact Fin.elim0 i
          | fixed y =>
            exact Settles.pure _
      · intro theory
        apply Settles.bind (Settles.mapM _ _ (fun pair => bound_settles _ _ pair))
        intro bounds
        apply Settles.bind (reduce_settles _ _)
        intro result
        exact Settles.pure _

end ComparisonElimination
namespace ComparisonGroups
open ComparisonPartialPropagation.Fuel

theorem collect_settles (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (templates : ComparisonSkeleton.Templates)
    (reduced : ComparisonReduction.State) :
    Settles (fun _ => collect p shapes templates reduced) := by
  simp only [collect, bind, pure, RunResult.bind]
  apply Settles.bind
  · apply Settles.mapM
    intro pair
    split
    · exact Settles.rejected _
    · exact Settles.pure _
  · intro goals
    apply Settles.bind
    · apply Settles.forIn
      intro pair state
      split
      · split
        · exact Settles.rejected _
        · exact Settles.pure _
      · exact Settles.rejected _
    · intro state
      split <;> exact Settles.pure _

end ComparisonGroups

namespace ComparisonElimination
open ComparisonPartialPropagation.Fuel

theorem run_settles (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (templates : ComparisonSkeleton.Templates)
    (reduced : ComparisonReduction.State) :
    Settles (fun fuel => run fuel p shapes templates reduced) := by
  unfold run
  apply Settles.bind (ComparisonGroups.collect_settles _ _ _ _)
  intro groups
  apply Settles.bind
  · apply Settles.forIn
    intro g state
    apply Settles.bind (group_settles _ _ _)
    intro result
    exact Settles.pure _
  · intro state
    exact Settles.pure _

theorem run_terminates (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (templates : ComparisonSkeleton.Templates)
    (reduced : ComparisonReduction.State) :
    ∃ n result, result ≠ .exhausted ∧ ∀ fuel ≥ n, run fuel p shapes templates reduced = result :=
  (run_settles p shapes templates reduced).2

theorem run_stable {small large : Nat} {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {result : RunResult Result}
    (h : run small p shapes templates reduced = result) (hr : result ≠ .exhausted)
    (hle : small ≤ large) : run large p shapes templates reduced = result :=
  (run_settles p shapes templates reduced).1 hle h hr

end ComparisonElimination
namespace ComparisonChecker
open ComparisonPartialPropagation.Fuel

theorem propagate_settles (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (shared : Bool) (before : Substitution) :
    Settles (fun fuel => propagate fuel p shapes shared before) := by
  simp only [propagate, bind, pure, RunResult.bind]
  apply Settles.bind (knownTotal_settles _ _)
  intro known
  apply Settles.bind ⟨ComparisonReduction.prepare_fuel_stable _ _ _ _ _,
    ComparisonReduction.prepare_fuel_terminates _ _ _ _ _⟩
  intro reduced
  apply Settles.bind (ComparisonElimination.run_settles _ _ _ _)
  intro types
  apply Settles.bind (modes_settles _ _)
  intro modes
  apply Settles.bind (backend_settles _)
  intro report
  split
  · exact Settles.rejected _
  · exact Settles.pure _

theorem variants_settles (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (before : Substitution) :
    Settles (fun fuel => variants fuel p shapes before) := by
  refine Settles.congr (Settles.recover (g := fun fuel reason =>
    match propagate fuel p shapes true before with
    | .success result => .success result
    | .exhausted => .exhausted
    | .rejected _ => .rejected reason) (propagate_settles p shapes false before) ?_) ?_
  · intro reason
    refine Settles.congr (Settles.recover (g := fun _ _ => .rejected reason)
      (propagate_settles p shapes true before) (fun _ => Settles.rejected reason)) ?_
    intro fuel
    dsimp only
    cases propagate fuel p shapes true before <;> rfl
  · intro fuel
    unfold variants
    cases propagate fuel p shapes false before <;> rfl

theorem refineContexts_settles (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (before : Substitution) :
    Settles (fun fuel => refineContexts fuel p shapes before) := by
  let input := ComparisonExactContext.rewrite p before
  let continuation := fun fuel reason => do
    let known ← ComparisonBody.knownTotal fuel input.assumptions
      (ComparisonAnnotations.expressions input.sourceType ++
        ComparisonAnnotations.expressions input.targetType)
    let absorption := ComparisonAbsorption.plan input (ComparisonBody.isTotal known)
    let context := { input with sourceType := absorption.body }
    let modes : RunResult Evidence :=
      match ComparisonContext.prepare context (ComparisonBody.isTotal known) with
      | some selected =>
          if selected.modes.isEmpty then .rejected reason
          else variants fuel p shapes (selected.compose before)
      | none => .rejected reason
    match modes with
    | .rejected _ =>
        match ComparisonExactContext.prepare context (ComparisonBody.isTotal known) with
        | some selected =>
            if selected.types.isEmpty && selected.modes.isEmpty then .rejected reason
            else variants fuel p shapes (selected.compose before)
        | none => .rejected reason
    | result => result
  refine Settles.congr (Settles.recover (g := continuation) (variants_settles p shapes before) ?_) ?_
  · intro reason
    dsimp only [continuation]
    apply Settles.bind (knownTotal_settles _ _)
    intro known
    let context := { input with sourceType :=
      (ComparisonAbsorption.plan input (ComparisonBody.isTotal known)).body }
    let selectedModes : Nat → RunResult Evidence := fun fuel =>
      match ComparisonContext.prepare context (ComparisonBody.isTotal known) with
      | some selected => if selected.modes.isEmpty then .rejected reason
          else variants fuel p shapes (selected.compose before)
      | none => .rejected reason
    let selectedTypes : Nat → RunResult Evidence := fun fuel =>
      match ComparisonExactContext.prepare context (ComparisonBody.isTotal known) with
      | some selected => if selected.types.isEmpty && selected.modes.isEmpty then .rejected reason
          else variants fuel p shapes (selected.compose before)
      | none => .rejected reason
    have hm : Settles selectedModes := by
      dsimp only [selectedModes]
      split
      · split
        · exact Settles.rejected _
        · exact variants_settles _ _ _
      · exact Settles.rejected _
    have ht : Settles selectedTypes := by
      dsimp only [selectedTypes]
      split
      · split
        · exact Settles.rejected _
        · exact variants_settles _ _ _
      · exact Settles.rejected _
    refine Settles.congr (Settles.recover (g := fun fuel _ => selectedTypes fuel) hm (fun _ => ht)) ?_
    intro fuel
    change (match selectedModes fuel with
      | .rejected _ => selectedTypes fuel
      | result => result) = _
    cases selectedModes fuel <;> rfl
  · intro fuel
    dsimp only [refineContexts, continuation, input]
    cases variants fuel p shapes before <;> rfl

theorem core_settles (source target : Scheme) :
    Settles (fun fuel => core fuel source target) := by
  simp only [core, bind, pure, RunResult.bind]
  apply Settles.bind
    ⟨fun hle h hr => ComparisonInstance.attempt_stable h hr _ hle,
      ComparisonInstance.attempt_terminates _⟩
  intro instanceResult
  cases instanceResult with
  | some result => exact Settles.pure _
  | none =>
    apply Settles.bind ⟨shapePrepare_stable _, ComparisonShapeSolver.prepare_eventually _⟩
    intro shapeResult
    cases shapeResult with
    | infeasibleAssumptions => exact Settles.rejected _
    | solved shapes =>
      refine Settles.congr (Settles.recover (g := fun fuel reason =>
        let p := SchemePreparation.prepare [] source target
        let before := ComparisonExactContext.neutral p
        if before.modes.isEmpty then .rejected reason
        else refineContexts fuel p shapes before)
        (refineContexts_settles (SchemePreparation.prepare [] source target) shapes {}) ?_) ?_
      · intro reason
        dsimp only
        split
        · exact Settles.rejected _
        · exact refineContexts_settles _ _ _
      · intro fuel
        dsimp only
        cases refineContexts fuel (SchemePreparation.prepare [] source target) shapes {} <;> rfl

theorem run_settles (source target : Scheme) :
    Settles (fun fuel => run fuel source target) := by
  refine Settles.congr (Settles.recover (g := fun fuel reason => do
    let p := SchemePreparation.prepare [] source target
    match ← ComparisonPartialPropagation.attempt fuel p with
    | some result => return partialEvidence p result
    | none => .rejected reason) (core_settles source target) ?_) ?_
  · intro reason
    apply Settles.bind
      ⟨fun hle h hr => ComparisonPartialPropagation.attempt_stable h hr hle,
        ComparisonPartialPropagation.attempt_terminates _⟩
    intro partialResult
    cases partialResult with
    | some result => exact Settles.pure _
    | none => exact Settles.rejected _
  · intro fuel
    unfold run
    cases core fuel source target <;> rfl

theorem propagate_terminates (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (shared : Bool) (before : Substitution) :
    ∃ n result, result ≠ .exhausted ∧
      ∀ fuel ≥ n, propagate fuel p shapes shared before = result :=
  (propagate_settles p shapes shared before).2

theorem propagate_stable {small large : Nat} {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {shared : Bool} {before : Substitution}
    {result : RunResult Evidence} (h : propagate small p shapes shared before = result)
    (hr : result ≠ .exhausted) (hle : small ≤ large) :
    propagate large p shapes shared before = result :=
  (propagate_settles p shapes shared before).1 hle h hr

theorem core_terminates (source target : Scheme) :
    ∃ n result, result ≠ .exhausted ∧ ∀ fuel ≥ n, core fuel source target = result :=
  (core_settles source target).2

theorem core_stable {small large : Nat} {source target : Scheme} {result : RunResult Evidence}
    (h : core small source target = result) (hr : result ≠ .exhausted) (hle : small ≤ large) :
    core large source target = result := (core_settles source target).1 hle h hr

/-- Every source/target input eventually has a fixed completed outcome. This
statement permits rejection and asserts no semantic completeness implication. -/
theorem run_terminates (source target : Scheme) :
    ∃ n result, result ≠ .exhausted ∧ ∀ fuel ≥ n, run fuel source target = result :=
  (run_settles source target).2

theorem run_stable {small large : Nat} {source target : Scheme} {result : RunResult Evidence}
    (h : run small source target = result) (hr : result ≠ .exhausted) (hle : small ≤ large) :
    run large source target = result := (run_settles source target).1 hle h hr

theorem run_monotone {small large : Nat} {source target : Scheme} {result : Evidence}
    (h : run small source target = .success result) (hle : small ≤ large) :
    run large source target = .success result := run_stable h (by simp) hle

end ComparisonChecker

theorem checkSubsumption_terminates (source target : Scheme) :
    ∃ n result, result ≠ .exhausted ∧ ∀ fuel ≥ n, checkSubsumption fuel source target = result :=
  ComparisonChecker.run_terminates source target

theorem checkSubsumption_stable {small large : Nat} {source target : Scheme}
    {result : RunResult SubsumptionEvidence} (h : checkSubsumption small source target = result)
    (hr : result ≠ .exhausted) (hle : small ≤ large) :
    checkSubsumption large source target = result := ComparisonChecker.run_stable h hr hle

theorem checkSubsumption_monotone {small large : Nat} {source target : Scheme}
    {result : SubsumptionEvidence} (h : checkSubsumption small source target = .success result)
    (hle : small ≤ large) : checkSubsumption large source target = .success result :=
  ComparisonChecker.run_monotone h hle

end ModalityInference
