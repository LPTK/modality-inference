import ModalityInference.ComparisonInstance
import ModalityInference.Proofs.SchemePreparedScope
import ModalityInference.Proofs.SchemePreparation
import ModalityInference.Proofs.Backend
import ModalityInference.Proofs.CNFNormalization
import ModalityInference.Proofs.Projection
import ModalityInference.Proofs.SyntacticEquality
import ModalityInference.Proofs.SubstitutionSupport

namespace ModalityInference.ComparisonInstance

theorem candidate_spec {p : Prepared} {action : Substitution}
    (h : candidate p = some action) :
    targetFresh p = true ∧ ∃ matched,
      matchType p p.sourceType p.targetType {} = some matched ∧
      action = complete p matched ∧ action.ty p.sourceType = p.targetType := by
  cases hf : targetFresh p <;> simp [candidate, hf] at h
  cases hm : matchType p p.sourceType p.targetType {} <;> simp [hm] at h
  obtain ⟨hbody, rfl⟩ := h
  exact ⟨rfl, _, rfl, rfl, hbody⟩

theorem complete_domain (p : Prepared) (action : Substitution) :
    (complete p action).types.map Prod.fst = List.range' p.firstType (p.nextType - p.firstType) ∧
    (complete p action).modes.map Prod.fst = List.range' p.firstMode (p.nextMode - p.firstMode) := by
  simp [complete, List.map_map, Function.comp_def]

theorem complete_type_fixed (p : Prepared) (action : Substitution) (v : TypeVar)
    (h : typeAllowed p v = false) : (complete p action).type v = .var v := by
  cases v with
  | rigid n => rfl
  | flex n =>
    apply Substitution.type_fresh
    rw [(complete_domain p action).1]
    simp only [List.mem_range']
    simp [typeAllowed] at h
    omega

theorem complete_mode_fixed (p : Prepared) (action : Substitution) (v : ModVar)
    (h : modeAllowed p v = false) : (complete p action).mode v = .var v := by
  cases v with
  | rigid n => rfl
  | flex n =>
    apply Substitution.mode_fresh
    rw [(complete_domain p action).2]
    simp only [List.mem_range']
    simp [modeAllowed] at h
    omega

theorem candidate_body {p : Prepared} {action : Substitution}
    (h : candidate p = some action) : action.ty p.sourceType = p.targetType := by
  obtain ⟨_, _, _, _, hbody⟩ := candidate_spec h
  exact hbody

theorem candidate_domain {p : Prepared} {action : Substitution}
    (h : candidate p = some action) :
    action.types.map Prod.fst = List.range' p.firstType (p.nextType - p.firstType) ∧
    action.modes.map Prod.fst = List.range' p.firstMode (p.nextMode - p.firstMode) := by
  obtain ⟨_, matched, _, rfl, _⟩ := candidate_spec h
  exact complete_domain p matched

theorem candidate_type_fixed {p : Prepared} {action : Substitution}
    (h : candidate p = some action) (v : TypeVar) (hv : typeAllowed p v = false) :
    action.type v = .var v := by
  obtain ⟨_, matched, _, rfl, _⟩ := candidate_spec h
  exact complete_type_fixed p matched v hv

theorem candidate_mode_fixed {p : Prepared} {action : Substitution}
    (h : candidate p = some action) (v : ModVar) (hv : modeAllowed p v = false) :
    action.mode v = .var v := by
  obtain ⟨_, matched, _, rfl, _⟩ := candidate_spec h
  exact complete_mode_fixed p matched v hv

theorem run_spec {fuel : Nat} {p : Prepared} {result : Result}
    (h : run fuel p = some result) :
    candidate p = some result.action ∧
      ((result.action.bounds p.sourceBounds).assumptions).all (structural p.assumptions) = true ∧
      result.query = .imp (boundsModeFormula p.assumptions)
        (boundsModeFormula (result.action.bounds p.sourceBounds).assumptions) ∧
      ConcreteBackend.decideFormula fuel result.query = .success result.backend ∧
      result.backend.valid = true := by
  cases hc : candidate p <;> simp only [run, attempt, hc] at h
  · cases h
  rename_i action
  cases hs : ((action.bounds p.sourceBounds).assumptions).all (structural p.assumptions) <;>
    simp [hs] at h
  cases hr : ConcreteBackend.decideFormula fuel (.imp (boundsModeFormula p.assumptions)
      (boundsModeFormula (action.bounds p.sourceBounds).assumptions)) <;>
    simp [hr, bind, pure, RunResult.bind] at h
  obtain ⟨hv, rfl⟩ := h
  exact ⟨rfl, hs, rfl, hr, hv⟩

theorem structural_sub {Δ : Bounds} {a b : Ty}
    (h : structural Δ (.sub a b) = true) : Subtype Δ a b := by
  simp [structural] at h
  rcases h with rfl | hb
  · exact .refl
  · exact .bound hb

theorem run_guards {fuel : Nat} {p : Prepared} {result : Result}
    (h : run fuel p = some result) :
    ∀ η, ModeModels p.assumptions η →
      ModeModels (result.action.bounds p.sourceBounds).assumptions η := by
  intro η hη
  obtain ⟨_, _, hquery, hreport, hv⟩ := run_spec h
  have he := (ConcreteBackend.decideFormula_correct hreport).mp hv (encodeModes η)
  rw [hquery] at he
  have ha : (boundsModeFormula p.assumptions).eval (encodeModes η) = true := by
    simpa only [boundsModeFormula_correct, projectedModes_encodeModes] using hη
  have hb : (boundsModeFormula (result.action.bounds p.sourceBounds).assumptions).eval
      (encodeModes η) = true := by simpa [BoolExpr.eval, ha] using he
  simpa only [boundsModeFormula_correct, projectedModes_encodeModes] using hb

private theorem constraint_certified {Δ : Bounds} {c : Constraint}
    (hs : ∀ a b, .sub a b ∈ c.assumptions → Subtype Δ a b)
    (hm : ∀ η, ModeModels Δ η → ModeModels c.assumptions η) : Entails Δ c := by
  cases c with
  | sub a b =>
    exact ⟨hs a b (by simp [Constraint.assumptions]),
      fun η hη d hd => hm η hη d (by simp [Constraint.assumptions, hd]),
      fun η hη d hd => hm η hη d (by simp [Constraint.assumptions, hd])⟩
  | equiv a b =>
    exact ⟨hs a b (by simp [Constraint.assumptions]), hs b a (by simp [Constraint.assumptions]),
      fun η hη d hd => hm η hη d (by simp [Constraint.assumptions, hd]),
      fun η hη d hd => hm η hη d (by simp [Constraint.assumptions, hd])⟩
  | equal v a =>
    exact ⟨hs (.var v) a (by simp [Constraint.assumptions]),
      hs a (.var v) (by simp [Constraint.assumptions]),
      fun η hη d hd => hm η hη d (by simp [Constraint.assumptions, hd])⟩
  | mode a b => exact .valid fun η hη => hm η hη (.mode a b) (by simp [Constraint.assumptions])
  | defined m => exact fun η hη => hm η hη (.defined m) (by simp [Constraint.assumptions])

theorem run_entails {fuel : Nat} {p : Prepared} {result : Result}
    (h : run fuel p = some result) :
    EntailsAll p.assumptions (result.action.bounds p.sourceBounds) := by
  intro c hc
  apply constraint_certified
  · intro a b hab
    exact structural_sub ((List.all_eq_true.mp (run_spec h).2.1) _
      (List.mem_flatMap.mpr ⟨c, hc, hab⟩))
  · intro η hη d hd
    exact run_guards h η hη d (List.mem_flatMap.mpr ⟨c, hc, hd⟩)

theorem run_body {fuel : Nat} {p : Prepared} {result : Result}
    (h : run fuel p = some result) : result.action.ty p.sourceType = p.targetType :=
  candidate_body (run_spec h).1

theorem run_prepared_type_fixed {fuel : Nat} {ambient : Bounds} {source target : Scheme}
    {result : Result} (h : run fuel (SchemePreparation.prepare ambient source target) = some result)
    (v : TypeVar) (hv : v ∈ source.body.typeVars ∪ source.bounds.typeVars) :
    result.action.type v = .var v := by
  apply candidate_type_fixed (run_spec h).1
  have hi : v.index < (SchemePreparation.prepare ambient source target).firstType :=
    SchemePreparation.original_type_lt_first (by
      have hv' := Finset.mem_union.mp hv
      simp only [SchemePreparation.originalTypeIds, List.mem_append,
        TypeExpr.mem_typeVariables, Bounds.mem_typeVariables]
      tauto)
  cases v <;> simp [typeAllowed]
  simp only [TypeVar.index] at hi
  omega

theorem run_prepared_mode_fixed {fuel : Nat} {ambient : Bounds} {source target : Scheme}
    {result : Result} (h : run fuel (SchemePreparation.prepare ambient source target) = some result)
    (v : ModVar) (hv : v ∈ source.body.modVars ∪ source.bounds.modVars) :
    result.action.mode v = .var v := by
  apply candidate_mode_fixed (run_spec h).1
  have hi : v.index < (SchemePreparation.prepare ambient source target).firstMode :=
    SchemePreparation.original_mode_lt_first (by
      have hv' := Finset.mem_union.mp hv
      simp only [SchemePreparation.originalModeIds, List.mem_append,
        TypeExpr.mem_modeVariables, Bounds.mem_modeVariables]
      tauto)
  cases v <;> simp [modeAllowed]
  simp only [ModVar.index] at hi
  omega

/-- Every positive syntactic certificate proves ordinary scheme subsumption.
Partial images are allowed in bare bodies; all written bounds are checked with
their original guards. No residual-target or empty-ambient premise is needed. -/
theorem run_sound {fuel : Nat} {ambient : Bounds} {source target : Scheme} {result : Result}
    (h : run fuel (SchemePreparation.prepare ambient source target) = some result) :
    Subsumes ambient source target := by
  apply SchemePreparation.reconstruct_sound ambient source target result.action
  · exact run_prepared_type_fixed h
  · exact run_prepared_mode_fixed h
  · exact run_entails h
  · rw [run_body h]
    exact .refl


theorem attempt_some_iff {fuel : Nat} {p : Prepared} {result : Result} :
    attempt fuel p = .success (some result) ↔ run fuel p = some result := by
  cases h : attempt fuel p <;> simp [run, h]

theorem attempt_success_run {fuel : Nat} {p : Prepared} {result : Option Result}
    (h : attempt fuel p = .success result) : run fuel p = result := by
  simp [run, h]

private theorem toCNF_not_rejected (fuel : Nat) (positive : Bool) (e : BoolExpr)
    (message : String) : toCNF fuel positive e ≠ .rejected message := by
  induction fuel generalizing positive e message with
  | zero => simp [toCNF]
  | succ fuel ih =>
    cases positive <;> cases e
    all_goals simp only [toCNF, bind, pure, RunResult.bind, cnfOr]
    all_goals repeat' (split <;> try contradiction)
    all_goals simp_all

private theorem decideFormula_stable {n : Nat} {e : BoolExpr}
    {result : RunResult ConcreteBackend.Report}
    (h : ConcreteBackend.decideFormula n e = result) (hr : result ≠ .exhausted)
    (fuel : Nat) (hf : n ≤ fuel) : ConcreteBackend.decideFormula fuel e = result := by
  cases hc : toCNF n true e with
  | success cs =>
    simpa only [ConcreteBackend.decideFormula, hc, toCNF_monotone hc fuel hf] using h
  | rejected message => exact False.elim (toCNF_not_rejected n true e message hc)
  | exhausted =>
    simp [ConcreteBackend.decideFormula, hc, bind, RunResult.bind] at h
    exact False.elim (hr h.symm)

/-- Every completed attempt, including absence of a certificate, is stable when
its budget increases. An applicable exhausted certificate cannot select fallback. -/
theorem attempt_stable {n : Nat} {p : Prepared} {result : RunResult (Option Result)}
    (h : attempt n p = result) (hr : result ≠ .exhausted)
    (fuel : Nat) (hf : n ≤ fuel) : attempt fuel p = result := by
  cases hc : candidate p <;> simp only [attempt, hc] at h ⊢
  · exact h
  rename_i action
  cases hs : ((action.bounds p.sourceBounds).assumptions).all (structural p.assumptions) <;>
    simp only [hs, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      if_true, if_false] at h ⊢
  · exact h
  cases hd : ConcreteBackend.decideFormula n (.imp (boundsModeFormula p.assumptions)
      (boundsModeFormula (action.bounds p.sourceBounds).assumptions)) with
  | success backend =>
    rw [decideFormula_stable hd (by simp) fuel hf]
    simpa only [hd] using h
  | rejected message =>
    rw [decideFormula_stable hd (by simp) fuel hf]
    simpa only [hd] using h
  | exhausted =>
    simp [hd, bind, RunResult.bind] at h
    exact False.elim (hr h.symm)

theorem attempt_monotone {n : Nat} {p : Prepared} {result : Option Result}
    (h : attempt n p = .success result) (fuel : Nat) (hf : n ≤ fuel) :
    attempt fuel p = .success result := attempt_stable h (by simp) fuel hf

theorem attempt_exhausted_iff {fuel : Nat} {p : Prepared} :
    attempt fuel p = .exhausted ↔ ∃ action,
      candidate p = some action ∧
      ((action.bounds p.sourceBounds).assumptions).all (structural p.assumptions) = true ∧
      ConcreteBackend.decideFormula fuel (.imp (boundsModeFormula p.assumptions)
        (boundsModeFormula (action.bounds p.sourceBounds).assumptions)) = .exhausted := by
  cases hc : candidate p <;> simp only [attempt, hc]
  · simp
  rename_i action
  simp only [Option.some.injEq, exists_eq_left']
  cases hs : ((action.bounds p.sourceBounds).assumptions).all (structural p.assumptions) <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_true, if_false,
      false_and, true_and, bind, pure, RunResult.bind]
  · simp
  cases hr : ConcreteBackend.decideFormula fuel (.imp (boundsModeFormula p.assumptions)
      (boundsModeFormula (action.bounds p.sourceBounds).assumptions)) <;> simp

private theorem decideClauses_not_exhausted (atoms : List Nat) (cs : CNF) (initial : Bool) :
    ConcreteBackend.decideClauses atoms cs initial ≠ .exhausted := by
  induction cs generalizing initial with
  | nil => simp [ConcreteBackend.decideClauses]
  | cons c cs ih =>
    simp only [ConcreteBackend.decideClauses]
    split
    · simp
    · exact ih _

private theorem decideFormula_terminates (e : BoolExpr) :
    ∃ n result, result ≠ .exhausted ∧
      ∀ fuel ≥ n, ConcreteBackend.decideFormula fuel e = result := by
  obtain ⟨n, cs, hn⟩ := toCNF_complete e true
  refine ⟨n, (ConcreteBackend.decideClauses (e.atoms.mergeSort (· ≤ ·)) cs true).bind
      (fun valid => .success ⟨e.atoms.mergeSort (· ≤ ·), cs, valid⟩), ?_, ?_⟩
  · cases hd : ConcreteBackend.decideClauses (e.atoms.mergeSort (· ≤ ·)) cs true <;>
      simp [RunResult.bind]
    exact False.elim (decideClauses_not_exhausted _ _ _ hd)
  · intro fuel hf
    simp [ConcreteBackend.decideFormula, hn fuel hf, bind, pure, RunResult.bind]

/-- The attempt eventually returns a fixed non-exhausted result. -/
theorem attempt_terminates (p : Prepared) :
    ∃ n result, result ≠ .exhausted ∧ ∀ fuel ≥ n, attempt fuel p = result := by
  cases hc : candidate p
  · exact ⟨0, .success none, by simp, fun _ _ => by simp [attempt, hc]⟩
  rename_i action
  cases hs : ((action.bounds p.sourceBounds).assumptions).all (structural p.assumptions)
  · exact ⟨0, .success none, by simp, fun _ _ => by simp [attempt, hc, hs]⟩
  obtain ⟨n, report, hr, hn⟩ := decideFormula_terminates (.imp (boundsModeFormula p.assumptions)
    (boundsModeFormula (action.bounds p.sourceBounds).assumptions))
  refine ⟨n, report.bind (fun backend => .success (if backend.valid then
    some ⟨action, .imp (boundsModeFormula p.assumptions)
      (boundsModeFormula (action.bounds p.sourceBounds).assumptions), backend⟩ else none)), ?_, ?_⟩
  · cases report <;> simp_all [RunResult.bind]
  · intro fuel hf
    simp [attempt, hc, hs, hn fuel hf, bind, pure]

theorem attempt_sound {fuel : Nat} {ambient : Bounds} {source target : Scheme} {result : Result}
    (h : attempt fuel (SchemePreparation.prepare ambient source target) = .success (some result)) :
    Subsumes ambient source target := run_sound (attempt_some_iff.mp h)

end ModalityInference.ComparisonInstance
