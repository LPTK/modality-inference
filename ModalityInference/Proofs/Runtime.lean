import ModalityInference.Runtime
import ModalityInference.Proofs.Annotations

/-! Exact correspondence between source execution and the internal annotated
proof representation, including diagnostics and exhaustion. -/
namespace ModalityInference

theorem ValueErasure.symm {v u} (h : ValueErasure v u) : ValueErasure u v := by
  induction h using ValueErasure.rec
    (motive_2 := fun γ δ _ => List.Forall₂ ValueErasure δ γ)
  all_goals solve_by_elim [ValueErasure.unit, ValueErasure.credit, ValueErasure.pair,
    ValueErasure.inl, ValueErasure.inr, ValueErasure.closure, List.Forall₂.nil,
    List.Forall₂.cons, Eq.symm]

end ModalityInference

namespace ModalityInference.Runtime

theorem trimEnvironment_erase (γ : ModalityInference.Environment) (used : Finset Nat) :
    (ModalityInference.trimEnvironment γ used).map eraseValue =
      trimEnvironment (γ.map eraseValue) used := by
  apply List.ext_getElem?
  intro i
  cases h : γ[i]? <;> by_cases hi : i ∈ used <;>
    simp [ModalityInference.trimEnvironment, trimEnvironment, List.getElem?_map,
      List.getElem?_mapIdx, h, hi, eraseValue]

/-- All outcomes, including rejection and fuel exhaustion, agree exactly. -/
theorem evalFuel_erase (fuel : Nat) (s : Supplies)
    (γ : ModalityInference.Environment) (t : AnnotatedTerm) :
    evalFuel fuel s (γ.map eraseValue) t.erase =
      eraseResult (ModalityInference.evalFuel fuel s γ t) := by
  induction fuel generalizing s γ t
  case zero => rfl
  case succ fuel ih =>
    simp only [Term.erase] at ih
    cases t <;> simp only [evalFuel, ModalityInference.evalFuel, Term.erase,
      Term.mapAnnotation, ih]
    case app f a =>
      cases ModalityInference.evalFuel fuel (s.branch 3 0) γ f <;>
        simp only [eraseResult, Bind.bind, RunResult.bind]
      case success vf =>
        cases ModalityInference.evalFuel fuel (s.branch 3 1) γ a <;>
          dsimp
        case success va =>
          cases vf <;> simp only [eraseValue, ← List.map_cons, Term.erase, ih]
          all_goals rfl
    case split a body =>
      cases ModalityInference.evalFuel fuel (s.branch 2 0) γ a <;>
        simp only [eraseResult, Bind.bind, RunResult.bind]
      case success v =>
        cases v <;> simp only [eraseValue]
        case pair l x y =>
          simpa only [List.map_cons, eraseValue, eraseResult] using
            ih (s.branch 2 1) (.credit l :: x :: y :: γ) body
    case defn rhs body =>
      rw [show evalFuel fuel (s.branch 2 0) [] (rhs.mapAnnotation fun _ => ()) =
        eraseResult (ModalityInference.evalFuel fuel (s.branch 2 0) [] rhs) from
        ih (s.branch 2 0) [] rhs]
      cases ModalityInference.evalFuel fuel (s.branch 2 0) [] rhs <;>
        simp only [eraseResult, Bind.bind, RunResult.bind, ← List.map_cons, ih]
    case case a left right =>
      cases ModalityInference.evalFuel fuel (s.branch 3 0) γ a <;>
        simp only [eraseResult, Bind.bind, RunResult.bind]
      case success v =>
        cases v <;> simp only [eraseValue, ← List.map_cons, ih]
        all_goals rfl
    case reuse credit first second =>
      cases ModalityInference.evalFuel fuel (s.branch 3 0) γ credit <;>
        simp only [eraseResult, Bind.bind, RunResult.bind]
      case success v =>
        cases ModalityInference.evalFuel fuel (s.branch 3 1) γ first <;>
          cases ModalityInference.evalFuel fuel (s.branch 3 2) γ second <;>
          cases v <;> simp [eraseValue, Pure.pure]
    case pair a b =>
      cases ModalityInference.evalFuel fuel (s.afterHeap.branch 2 0) γ a <;>
        cases ModalityInference.evalFuel fuel (s.afterHeap.branch 2 1) γ b <;>
        simp [eraseResult, eraseValue, Bind.bind, Pure.pure, RunResult.bind]
    case stackPair a b =>
      cases ModalityInference.evalFuel fuel (s.afterStack.branch 2 0) γ a <;>
        cases ModalityInference.evalFuel fuel (s.afterStack.branch 2 1) γ b <;>
        simp [eraseResult, eraseValue, Bind.bind, Pure.pure, RunResult.bind]
    case inl a | inr a =>
      cases ModalityInference.evalFuel fuel s γ a <;>
        simp [eraseResult, eraseValue, Bind.bind, Pure.pure, RunResult.bind]
    case var i => cases h : γ[i]? <;> simp [List.getElem?_map, h, eraseResult]
    case unit => simp [eraseResult, eraseValue]
    case lam => simp [eraseResult, eraseValue, Term.freeVars_mapAnnotation,
      trimEnvironment_erase, Term.erase]

@[simp] theorem erase_annotateTerm (t : RawTerm) : (annotateTerm t).erase = t := by
  induction t <;> simp_all [annotateTerm, Term.erase, Term.mapAnnotation]

@[simp] theorem eraseValue_annotate (v : Value) : eraseValue v.annotate = v := by
  induction v using Value.rec
    (motive_2 := fun γ => (γ.map Value.annotate).map eraseValue = γ)
  all_goals simp_all [Value.annotate, eraseValue]

theorem annotate_erasure (v : ModalityInference.Value) :
    ValueErasure v (eraseValue v).annotate := by
  induction v using ModalityInference.Value.rec
    (motive_2 := fun γ => List.Forall₂ ValueErasure γ ((γ.map eraseValue).map Value.annotate))
  all_goals simp only [eraseValue, Value.annotate, List.map_cons, List.map_nil]
  all_goals solve_by_elim [ValueErasure.unit, ValueErasure.credit, ValueErasure.pair,
    ValueErasure.inl, ValueErasure.inr, ValueErasure.closure, List.Forall₂.nil,
    List.Forall₂.cons, Eq.symm, erase_annotateTerm]

theorem evalFuel_sound {fuel supplies γ t v}
    (h : evalFuel fuel supplies γ t = .success v) : Eval supplies γ t v := by
  induction fuel generalizing supplies γ t v
  case zero => simp [evalFuel] at h
  case succ n ih =>
    cases t
    all_goals simp only [evalFuel, Bind.bind, Pure.pure, RunResult.bind] at h
    all_goals repeat' (split at h <;> try contradiction)
    all_goals try simp_all only [RunResult.success.injEq]
    all_goals try subst v
    all_goals solve_by_elim (config := {maxDepth := 8}) [Eval.var, Eval.unit, Eval.lam, Eval.app, Eval.pair, Eval.stackPair,
      Eval.inl, Eval.inr, Eval.defn, Eval.split, Eval.caseLeft, Eval.caseRight, Eval.reuse,
      Eval.region, ih]

theorem Eval.fuel_complete {supplies γ t v} (h : Eval supplies γ t v) :
    ∃ n, ∀ fuel ≥ n, evalFuel fuel supplies γ t = .success v := by
  induction h
  case app hf hx hb ihf ihx ihb | reuse hf hx hb ihf ihx ihb =>
    rcases And.intro ihf (And.intro ihx ihb) with ⟨⟨nf, hf⟩, ⟨nx, hx⟩, ⟨nb, hb⟩⟩
    refine ⟨nf + nx + nb + 1, ?_⟩
    rintro (_ | fuel) hFuel
    · omega
    · simp only [evalFuel, hf fuel (by omega), hx fuel (by omega), hb fuel (by omega),
        Bind.bind, Pure.pure, RunResult.bind]
  case pair h₁ h₂ ih₁ ih₂ | stackPair h₁ h₂ ih₁ ih₂ | defn h₁ h₂ ih₁ ih₂ |
      split h₁ h₂ ih₁ ih₂ | caseLeft h₁ h₂ ih₁ ih₂ | caseRight h₁ h₂ ih₁ ih₂ =>
    rcases And.intro ih₁ ih₂ with ⟨⟨n₁, h₁⟩, ⟨n₂, h₂⟩⟩
    refine ⟨n₁ + n₂ + 1, ?_⟩
    rintro (_ | fuel) hFuel
    · omega
    · simp only [evalFuel, h₁ fuel (by omega), h₂ fuel (by omega),
        Bind.bind, Pure.pure, RunResult.bind]
  case inl h ih | inr h ih | region h ih =>
    rcases ih with ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    rintro (_ | fuel) hFuel
    · omega
    · simp only [evalFuel, hn fuel (by omega), Bind.bind, Pure.pure, RunResult.bind]
  all_goals refine ⟨1, ?_⟩
  all_goals rintro (_ | fuel) hFuel
  all_goals simp_all [evalFuel]

theorem Eval.deterministic {supplies γ t v u}
    (hv : Eval supplies γ t v) (hu : Eval supplies γ t u) : v = u := by
  rcases And.intro hv.fuel_complete hu.fuel_complete with ⟨⟨n, hn⟩, ⟨m, hm⟩⟩
  exact RunResult.success.inj ((hn (max n m) (le_max_left _ _)).symm.trans
    (hm (max n m) (le_max_right _ _)))

/-- Increasing fuel preserves both successful results and genuine diagnostics.
Exhaustion is the only result that may change. -/
theorem evalFuel_stable {n supplies γ t r}
    (hr : r ≠ .exhausted) (h : evalFuel n supplies γ t = r) :
    ∀ fuel ≥ n, evalFuel fuel supplies γ t = r := by
  induction n generalizing supplies γ t r
  case zero => exact False.elim (hr h.symm)
  case succ n ih =>
    rintro (_ | fuel) hFuel
    · omega
    have step (s γ t r) (hs : evalFuel n s γ t = r) (hne : r ≠ .exhausted) :
        evalFuel fuel s γ t = r := ih hne hs fuel (Nat.le_of_succ_le_succ hFuel)
    cases t
    all_goals simp only [evalFuel, Bind.bind, Pure.pure, RunResult.bind] at h ⊢
    all_goals repeat' (split at h <;> try exact False.elim (hr h.symm))
    all_goals simp_all
    all_goals cases h
    all_goals rfl

theorem evalFuel_monotone {n supplies γ t v}
    (h : evalFuel n supplies γ t = .success v) :
    ∀ fuel ≥ n, evalFuel fuel supplies γ t = .success v := by
  exact evalFuel_stable (by simp) h

theorem Eval.no_rejection {supplies γ t v} (h : Eval supplies γ t v)
    (fuel : Nat) (diagnostic : String) : evalFuel fuel supplies γ t ≠ .rejected diagnostic := by
  rcases h.fuel_complete with ⟨n, hn⟩
  intro reject
  have stable := evalFuel_stable (by simp) reject (max n fuel) (le_max_right _ _)
  simp [hn (max n fuel) (le_max_left _ _)] at stable

theorem eval_erase {s γ t v} (h : ModalityInference.Eval s γ t v) :
    Eval s (γ.map eraseValue) t.erase (eraseValue v) := by
  obtain ⟨fuel, hf⟩ := h.fuel_complete
  exact evalFuel_sound (by rw [evalFuel_erase, hf fuel le_rfl]; rfl)

theorem References.closure_iff {γ body l} :
    References (.closure γ body) l ↔ EnvironmentReferences γ l :=
  ⟨fun h => by cases h with | closure hv hr => exact ⟨_, hv, hr⟩,
    fun ⟨_, hv, hr⟩ => .closure hv hr⟩

theorem references_erase (v : ModalityInference.Value) (l : Location) :
    References (eraseValue v) l ↔ ModalityInference.References v l := by
  induction v using ModalityInference.Value.rec
    (motive_2 := fun γ => ∀ l, EnvironmentReferences (γ.map eraseValue) l ↔
      ModalityInference.EnvironmentReferences γ l) generalizing l
  all_goals try simp only [eraseValue]
  case closure γ cap body ih =>
    exact (References.closure_iff.trans (ih l)).trans ModalityInference.References.closure_iff.symm
  case nil => simp [EnvironmentReferences, ModalityInference.EnvironmentReferences]
  case cons v γ ihv ihγ l =>
    simpa only [List.map_cons, EnvironmentReferences, ModalityInference.EnvironmentReferences,
      List.mem_cons, exists_prop, or_and_right, exists_or, exists_eq_left] using
      or_congr (ihv _) (ihγ _)
  all_goals constructor <;> intro h <;> cases h
  all_goals aesop (add 50% constructors References) (add 50% constructors ModalityInference.References)

@[simp] theorem environmentReferences_erase (γ : ModalityInference.Environment) (l : Location) :
    EnvironmentReferences (γ.map eraseValue) l ↔ ModalityInference.EnvironmentReferences γ l := by
  simp [EnvironmentReferences, ModalityInference.EnvironmentReferences, references_erase]

@[simp] theorem validValue_erase (w : World) (v : ModalityInference.Value) :
    ValidValue w (eraseValue v) ↔ w.ValidValue v := by
  simp only [ValidValue, World.ValidValue, references_erase]

@[simp] theorem compatible_erase (w : World) (s : Supplies) (γ : ModalityInference.Environment) :
    Compatible w s (γ.map eraseValue) ↔ w.Compatible s γ := by
  simp only [Compatible, World.Compatible, environmentReferences_erase]

/-- Every unannotated execution has an execution of any chosen proof
representation with exactly the same erased result. -/
theorem eval_iff {s γ t v} :
    Eval s (γ.map eraseValue) t.erase v ↔
      ∃ u, ModalityInference.Eval s γ t u ∧ eraseValue u = v := by
  constructor
  · intro h
    obtain ⟨fuel, hf⟩ := h.fuel_complete
    have he := evalFuel_erase fuel s γ t
    rw [hf fuel le_rfl] at he
    cases hresult : ModalityInference.evalFuel fuel s γ t <;> simp [hresult, eraseResult] at he
    exact ⟨_, ModalityInference.evalFuel_sound hresult, he.symm⟩
  · rintro ⟨u, hu, rfl⟩
    exact eval_erase hu

theorem evalFuel_success_iff (fuel s γ t v) :
    evalFuel fuel s (γ.map eraseValue) t.erase = .success v ↔
      ∃ u, ModalityInference.evalFuel fuel s γ t = .success u ∧ eraseValue u = v := by
  rw [evalFuel_erase]
  cases ModalityInference.evalFuel fuel s γ t <;> simp [eraseResult]

theorem evalFuel_rejected_iff (fuel s γ t diagnostic) :
    evalFuel fuel s (γ.map eraseValue) t.erase = .rejected diagnostic ↔
      ModalityInference.evalFuel fuel s γ t = .rejected diagnostic := by
  rw [evalFuel_erase]
  cases ModalityInference.evalFuel fuel s γ t <;> simp [eraseResult]

theorem evalFuel_exhausted_iff (fuel s γ t) :
    evalFuel fuel s (γ.map eraseValue) t.erase = .exhausted ↔
      ModalityInference.evalFuel fuel s γ t = .exhausted := by
  rw [evalFuel_erase]
  cases ModalityInference.evalFuel fuel s γ t <;> simp [eraseResult]

/-- Every raw program and environment can use the same exact correspondence. -/
theorem evalFuel_annotate (fuel s γ t) :
    evalFuel fuel s γ t =
      eraseResult (ModalityInference.evalFuel fuel s (γ.map Value.annotate) (annotateTerm t)) := by
  simpa [Function.comp_def] using evalFuel_erase fuel s (γ.map Value.annotate) (annotateTerm t)

theorem eval_annotate_iff {s γ t v} :
    Eval s γ t v ↔ ∃ u, ModalityInference.Eval s (γ.map Value.annotate) (annotateTerm t) u ∧
      eraseValue u = v := by
  simpa [Function.comp_def] using
    (eval_iff (s := s) (γ := γ.map Value.annotate) (t := annotateTerm t) (v := v))

end ModalityInference.Runtime
