import ModalityInference.Proofs.ComparisonPartialPropagationFuel
import ModalityInference.Proofs.ComparisonShapeSolver
import ModalityInference.Proofs.CNFNormalization

/-! Finite completion and fuel stability of partial-envelope propagation.
The proof follows the executed shape, scalar, and graph phases. It makes no
claim that the envelope grammar represents every legal partial witness. -/

namespace ModalityInference.ComparisonPartialPropagation

namespace Fuel

def Stable {α : Type} (f : Nat → RunResult α) : Prop :=
  ∀ {small large result}, small ≤ large → f small = result → result ≠ .exhausted → f large = result

def Terminates {α : Type} (f : Nat → RunResult α) : Prop :=
  ∃ n result, result ≠ .exhausted ∧ ∀ fuel ≥ n, f fuel = result

theorem Stable.const {α : Type} (result : RunResult α) : Stable (fun _ => result) :=
  fun _ h _ => h

theorem Stable.pure {α : Type} (value : α) : Stable (fun _ => .success value) :=
  fun _ h _ => h

theorem Stable.bind {α β : Type} {f : Nat → RunResult α} {g : Nat → α → RunResult β}
    (hf : Stable f) (hg : ∀ a, Stable (fun fuel => g fuel a)) :
    Stable (fun fuel => (f fuel).bind (g fuel)) := by
  intro small large result hle h hr
  cases hs : f small with
  | success a =>
    have hs' := hf hle hs (by simp)
    simp only [hs, RunResult.bind] at h
    simpa only [hs', RunResult.bind] using hg a hle h hr
  | rejected reason =>
    have hs' := hf hle hs (by simp)
    simpa only [hs, hs', RunResult.bind] using h
  | exhausted =>
    simp only [hs, RunResult.bind] at h
    exact False.elim (hr h.symm)

theorem Terminates.pure {α : Type} (value : α) : Terminates (fun _ => .success value) :=
  ⟨0, .success value, by simp, fun _ _ => rfl⟩

theorem Terminates.bind {α β : Type} {f : Nat → RunResult α}
    {g : Nat → α → RunResult β} (hf : Terminates f)
    (hg : ∀ a, Terminates (fun fuel => g fuel a)) :
    Terminates (fun fuel => (f fuel).bind (g fuel)) := by
  obtain ⟨n, result, hr, hf⟩ := hf
  cases result with
  | success a =>
    obtain ⟨m, result, hr, hg⟩ := hg a
    exact ⟨max n m, result, hr, fun fuel h => by
      simpa only [hf fuel ((Nat.le_max_left _ _).trans h), RunResult.bind] using
        hg fuel ((Nat.le_max_right _ _).trans h)⟩
  | rejected reason =>
    exact ⟨n, .rejected reason, by simp, fun fuel h => by
      simp only [hf fuel h, RunResult.bind]⟩
  | exhausted => exact False.elim (hr rfl)

theorem Stable.forIn {α β : Type} (xs : List α)
    (f : Nat → α → β → RunResult (ForInStep β))
    (hf : ∀ a b, Stable (fun fuel => f fuel a b)) (b : β) :
    Stable (fun fuel => forIn xs b (f fuel)) := by
  induction xs generalizing b with
  | nil =>
    simp only [List.forIn_nil]
    exact Stable.pure b
  | cons a xs ih =>
    simp only [List.forIn_cons]
    apply Stable.bind (hf a b)
    intro step
    cases step with
    | done b => exact Stable.pure b
    | yield b => exact ih b

theorem Terminates.forIn {α β : Type} (xs : List α)
    (f : Nat → α → β → RunResult (ForInStep β))
    (hf : ∀ a b, Terminates (fun fuel => f fuel a b)) (b : β) :
    Terminates (fun fuel => forIn xs b (f fuel)) := by
  induction xs generalizing b with
  | nil =>
    simp only [List.forIn_nil]
    exact Terminates.pure b
  | cons a xs ih =>
    simp only [List.forIn_cons]
    apply Terminates.bind (hf a b)
    intro step
    cases step with
    | done b => exact Terminates.pure b
    | yield b => exact ih b

private theorem toCNF_not_rejected (fuel : Nat) (positive : Bool) (e : BoolExpr)
    (message : String) : toCNF fuel positive e ≠ .rejected message := by
  induction fuel generalizing positive e message with
  | zero => simp [toCNF]
  | succ fuel ih =>
    cases positive <;> cases e
    all_goals simp only [toCNF, bind, pure, RunResult.bind, cnfOr]
    all_goals repeat' (split <;> try contradiction)
    all_goals simp_all

theorem backend_stable (e : BoolExpr) :
    Stable (fun fuel => ConcreteBackend.decideFormula fuel e) := by
  intro small large result hle h hr
  cases hc : toCNF small true e with
  | success cs =>
    simpa only [ConcreteBackend.decideFormula, hc, toCNF_monotone hc large hle] using h
  | rejected message => exact False.elim (toCNF_not_rejected small true e message hc)
  | exhausted =>
    simp [ConcreteBackend.decideFormula, hc, bind, RunResult.bind] at h
    exact False.elim (hr h.symm)

private theorem decideClauses_not_exhausted (atoms : List Nat) (cs : CNF) (initial : Bool) :
    ConcreteBackend.decideClauses atoms cs initial ≠ .exhausted := by
  induction cs generalizing initial with
  | nil => simp [ConcreteBackend.decideClauses]
  | cons c cs ih =>
    simp only [ConcreteBackend.decideClauses]
    split
    · simp
    · exact ih _

theorem backend_terminates (e : BoolExpr) :
    Terminates (fun fuel => ConcreteBackend.decideFormula fuel e) := by
  obtain ⟨n, cs, hn⟩ := toCNF_complete e true
  refine ⟨n, (ConcreteBackend.decideClauses (e.atoms.mergeSort (· ≤ ·)) cs true).bind
      (fun valid => .success ⟨e.atoms.mergeSort (· ≤ ·), cs, valid⟩), ?_, ?_⟩
  · cases hd : ConcreteBackend.decideClauses (e.atoms.mergeSort (· ≤ ·)) cs true <;>
      simp [RunResult.bind]
    exact False.elim (decideClauses_not_exhausted _ _ _ hd)
  · intro fuel hf
    simp [ConcreteBackend.decideFormula, hn fuel hf, bind, pure, RunResult.bind]

open ComparisonShapeSolver in
theorem shapeUnify_stable (allowed : TypeVar → Bool) (ps : Pairs) :
    Stable (fun fuel => unify fuel allowed ps) := by
  intro small large result hle h hr
  induction small generalizing large ps result with
  | zero => exact False.elim (hr h.symm)
  | succ small ih =>
    cases large with
    | zero => omega
    | succ large =>
      have hle' : small ≤ large := by omega
      cases ps with
      | nil => simpa only [unify] using h
      | cons pair rest =>
        rcases pair with ⟨a, b⟩
        simp only [unify] at h ⊢
        split at h
        · next he => simpa only [he, ↓reduceIte] using ih _ hle' h hr
        · next he =>
          simp only [he]
          cases hp : choose allowed a b with
          | none =>
            simp only [hp] at h ⊢
            cases a <;> cases b <;> simp only at h ⊢
            all_goals first | exact h | exact ih _ hle' h hr
          | some pair =>
            rcases pair with ⟨v, t⟩
            simp only [hp] at h ⊢
            split at h
            · next ho => simpa only [ho, ↓reduceIte] using h
            · next ho =>
              simp only [ho]
              cases hs : unify small allowed (mapPairs (replace v t) rest) with
              | success s =>
                have hs' := ih _ hle' hs (by simp)
                simpa only [hs, hs', bind, pure, RunResult.bind] using h
              | rejected message =>
                have hs' := ih _ hle' hs (by simp)
                simpa only [hs, hs', bind, pure, RunResult.bind] using h
              | exhausted =>
                simp only [hs, bind, RunResult.bind] at h
                exact False.elim (hr h.symm)

theorem shapePrepare_stable (p : SchemePreparation.Prepared) :
    Stable (fun fuel => ComparisonShapeSolver.prepare fuel p) := by
  intro small large result hle h hr
  cases hs : ComparisonShapeSolver.unify small (fun _ => true)
      (ComparisonShape.pairs p.assumptions) with
  | success fixed =>
    have hs' := shapeUnify_stable _ _ hle hs (by simp)
    simp only [ComparisonShapeSolver.prepare, hs, hs'] at h ⊢
    exact (Stable.bind
      (shapeUnify_stable (ComparisonShapeSolver.sourceAllowed p)
        (ComparisonShapeSolver.mapPairs (ComparisonShapeSolver.action fixed)
          (ComparisonShapeSolver.sourcePairs p)))
      (fun source => Stable.pure (ComparisonShapeSolver.Result.solved ⟨fixed, source⟩))) hle h hr
  | rejected reason =>
    have hs' := shapeUnify_stable _ _ hle hs (by simp)
    simpa only [ComparisonShapeSolver.prepare, hs, hs'] using h
  | exhausted =>
    simp only [ComparisonShapeSolver.prepare, hs] at h
    exact False.elim (hr h.symm)

end Fuel
theorem modeEdges_fuel_stable (assumptions : Bounds) (labels : List ModExpr) :
    Fuel.Stable (fun fuel => modeEdges fuel assumptions labels) := by
  unfold modeEdges
  apply Fuel.Stable.bind
  · apply Fuel.Stable.forIn
    intro a result
    apply Fuel.Stable.bind
    · apply Fuel.Stable.forIn
      intro b result
      apply Fuel.Stable.bind (Fuel.backend_stable _)
      intro report
      exact Fuel.Stable.const _
    · intro result
      exact Fuel.Stable.pure _
  · intro result
    exact Fuel.Stable.pure _

theorem modeEdges_fuel_terminates (assumptions : Bounds) (labels : List ModExpr) :
    Fuel.Terminates (fun fuel => modeEdges fuel assumptions labels) := by
  unfold modeEdges
  apply Fuel.Terminates.bind
  · apply Fuel.Terminates.forIn
    intro a result
    apply Fuel.Terminates.bind
    · apply Fuel.Terminates.forIn
      intro b result
      apply Fuel.Terminates.bind (Fuel.backend_terminates _)
      intro report
      simp only [bind, pure, RunResult.bind]
      split <;> exact Fuel.Terminates.pure _
    · intro result
      exact Fuel.Terminates.pure _
  · intro result
    exact Fuel.Terminates.pure _

theorem modeEdges_stable {small large : Nat} {assumptions : Bounds}
    {labels : List ModExpr} {result : RunResult (List (ModExpr × ModExpr))}
    (h : modeEdges small assumptions labels = result) (hr : result ≠ .exhausted)
    (hle : small ≤ large) : modeEdges large assumptions labels = result :=
  modeEdges_fuel_stable assumptions labels hle h hr

theorem modeEdges_terminates (assumptions : Bounds) (labels : List ModExpr) :
    ∃ n result, result ≠ .exhausted ∧ ∀ fuel ≥ n, modeEdges fuel assumptions labels = result :=
  modeEdges_fuel_terminates assumptions labels

theorem saturate_not_rejected (mode : ModExpr → ModExpr → Bool) (left right : CompareTy)
    (fuel : Nat) (g : Graph) (reason : String) :
    saturate mode left right fuel g ≠ .rejected reason := by
  induction fuel generalizing g with
  | zero => simp [saturate]
  | succ fuel ih =>
    simp only [saturate]
    split
    · simp
    · split
      · simp
      · exact ih _

theorem saturate_fuel_stable (mode : ModExpr → ModExpr → Bool)
    (left right : CompareTy) (g : Graph) :
    Fuel.Stable (fun fuel => saturate mode left right fuel g) := by
  intro small large result hle h hr
  cases result with
  | success result => exact saturate_monotone hle h
  | rejected reason => exact False.elim (saturate_not_rejected _ _ _ _ _ _ h)
  | exhausted => exact False.elim (hr rfl)

theorem saturate_fuel_terminates (mode : ModExpr → ModExpr → Bool)
    (left right : CompareTy) (g : Graph) :
    Fuel.Terminates (fun fuel => saturate mode left right fuel g) := by
  obtain ⟨result, hr⟩ := saturate_finite_bound mode left right g
  exact ⟨g.edges.size + 1, .success result, by simp,
    fun _ hf => saturate_monotone hf hr⟩

/-- Every envelope attempt eventually returns one fixed completed result. This
is termination of the finite certificate phase, not completeness of its images. -/
theorem attempt_terminates (p : SchemePreparation.Prepared) :
    ∃ n result, result ≠ .exhausted ∧ ∀ fuel ≥ n, attempt fuel p = result := by
  change Fuel.Terminates (fun fuel => attempt fuel p)
  simp only [attempt, bind, pure, RunResult.bind]
  split
  · exact Fuel.Terminates.pure _
  · split
    · exact Fuel.Terminates.pure _
    · apply Fuel.Terminates.bind (ComparisonShapeSolver.prepare_eventually p)
      intro solved
      cases solved with
      | infeasibleAssumptions => exact Fuel.Terminates.pure _
      | solved shapes =>
        dsimp only
        split
        · exact Fuel.Terminates.pure _
        · apply Fuel.Terminates.bind (modeEdges_fuel_terminates _ _)
          intro edges
          apply Fuel.Terminates.bind (saturate_fuel_terminates _ _ _ _)
          intro certificate
          cases certificate with
          | none => exact Fuel.Terminates.pure _
          | some certificate =>
            dsimp only
            split
            · exact Fuel.Terminates.pure _
            · apply Fuel.Terminates.bind (Fuel.backend_terminates _)
              intro backend
              split <;> exact Fuel.Terminates.pure _

/-- A completed attempt, including rejection or lack of a certificate, does
not change when its fuel increases. -/
theorem attempt_stable {small large : Nat} {p : SchemePreparation.Prepared}
    {result : RunResult (Option Result)} (h : attempt small p = result)
    (hr : result ≠ .exhausted) (hle : small ≤ large) : attempt large p = result := by
  have stable : Fuel.Stable (fun fuel => attempt fuel p) := by
    simp only [attempt, bind, pure, RunResult.bind]
    split
    · exact Fuel.Stable.pure _
    · split
      · exact Fuel.Stable.pure _
      · apply Fuel.Stable.bind (Fuel.shapePrepare_stable p)
        intro solved
        cases solved with
        | infeasibleAssumptions => exact Fuel.Stable.pure _
        | solved shapes =>
          dsimp only
          split
          · exact Fuel.Stable.pure _
          · apply Fuel.Stable.bind (modeEdges_fuel_stable _ _)
            intro edges
            apply Fuel.Stable.bind (saturate_fuel_stable _ _ _ _)
            intro certificate
            cases certificate with
            | none => exact Fuel.Stable.pure _
            | some certificate =>
              dsimp only
              split
              · exact Fuel.Stable.pure _
              · apply Fuel.Stable.bind (Fuel.backend_stable _)
                intro backend
                split <;> exact Fuel.Stable.pure _
  exact stable hle h hr

theorem attempt_monotone {small large : Nat} {p : SchemePreparation.Prepared}
    {result : Option Result} (h : attempt small p = .success result)
    (hle : small ≤ large) : attempt large p = .success result :=
  attempt_stable h (by simp) hle

end ModalityInference.ComparisonPartialPropagation
