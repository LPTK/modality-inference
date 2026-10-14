import ModalityInference.Proofs.TypeVariablePredicates

/-! Historical capture-annotation fixture for a body that shares a binding below
a lock. Current inference returns the source term unchanged; the explicit
annotation below records the discarded eager-capture construction. -/
namespace ModalityInference.SharingLockCapture

def α (n : Nat) : Ty := .var (.flex n)
def μ (n : Nat) : ModExpr := .var (.flex n)
def context : Context := [some (.mono (α 0))]
def term : RawTerm := .lam () (.pair (.var 1) (.var 1))
def captured : Scheme := (Scheme.mono (α 0)).lock (μ 0)
/-- The historical eager capture annotation; not an output of current inference. -/
def elaborated : AnnotatedTerm := .lam [some captured] (.pair (.var 1) (.var 1))
def aliasCapture : ModExpr := .compose (.const Mode.aliased) (.capture (μ 0))
def aliasFuture : ModExpr := .compose (.const Mode.aliased) (.future (μ 0))
def residual : Bounds :=
  [.sub (.modal (α 0) aliasCapture) (.modal (α 3) (μ 1)), .defined (μ 1),
   .defined aliasCapture, .sub (.modal (α 0) aliasCapture) (.modal (α 2) (μ 1)),
   .defined (.capture (μ 0)), .defined aliasFuture,
   .sub (.modal (α 0) (.const Mode.aliased)) (.modal (α 0) aliasFuture),
   .sub (.modal (α 0) .epsilon) (.modal (α 0) (.const Mode.many))]

private theorem infer_from_stages {fuel Γ t g s witness}
    (hg : generate fuel (Γ.map ContextEntry.binding) t (initialInferenceState Γ) =
      .success g)
    (hr : runSolver fuel
      {pending := g.state.constraints, nextType := g.state.nextType,
       nextMode := g.state.nextMode} = .success s)
    (hw : satisfiableModes fuel s.bounds = .success witness) :
    ∃ result, infer fuel Γ t = .success result ∧ result.residual = s.bounds ∧
      result.elaborated = g.term ∧ result.substitution = s.substitution ∧
      result.scheme.body = s.substitution.ty g.type := by
  have hc : solveFrom fuel g.state.nextType g.state.nextMode g.state.constraints =
      .success ⟨s.substitution, s.bounds, witness, s.nextType, s.nextMode, s.trace.reverse⟩ := by
    unfold solveFrom
    rw [hr]
    simp only [bind, RunResult.bind]
    rw [hw]
    rfl
  unfold infer
  rw [hg]
  simp only [bind, RunResult.bind]
  rw [hc]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 5000000 in
theorem succeeds_with_type : ∃ result, infer 100 context term = .success result ∧
    result.residual = residual ∧ result.elaborated = term ∧ result.substitution = {} ∧
    result.scheme.body = .modal (.fn (α 1) (.modal (.prod (α 2) (α 3)) (μ 1))) (μ 0) := by
  have hdomain : HornPropagation.domain (boundsModeFormula residual) = [] := by
    simp [HornPropagation.domain, boundsModeFormula, residual, constraintModeFormula,
      ModExpr.project, μ, aliasCapture, aliasFuture, BoolExpr.all, BoolExpr.atoms]
  have hpolar : (boundsModeFormula residual).IsHorn := by
    dsimp [boundsModeFormula, residual, constraintModeFormula, ModExpr.project,
      μ, aliasCapture, aliasFuture, BoolExpr.all]
    repeat constructor
  have hsuccess : (satisfiableModes 100 residual).isSuccess = true := by
    obtain ⟨model, hm⟩ := HornPropagation.checkFormula_complete hpolar
      ⟨fun _ => false, by decide⟩
    have hf : HornPropagation.requiredFuel (boundsModeFormula residual) ≤ 100 := by
      simp only [HornPropagation.requiredFuel, hdomain]
      decide
    simp [satisfiableModes, ModeConsistency.solve_of_polarized hpolar,
      HornPropagation.satisfiableModes, hm 100 hf, bind, pure, RunResult.bind, RunResult.isSuccess]
  cases hs : satisfiableModes 100 residual <;> simp [hs, RunResult.isSuccess] at hsuccess
  rename_i witness
  let shared : Constraint := .sub (α 0) (.modal (α 0) (.const Mode.many))
  let crossing : Constraint := .sub (.modal (α 0) (.const Mode.aliased))
    (.modal (.modal (α 0) (.const Mode.aliased)) (.future (μ 0)))
  let use : Nat → Constraint := fun n => .sub
    (.modal (.modal (α 0) (.const Mode.aliased)) (.capture (μ 0)))
    (.modal (α n) (μ 1))
  let g : Generated :=
    ⟨.modal (.fn (α 1) (.modal (.prod (α 2) (α 3)) (μ 1))) (μ 0), term,
      {nextType := 4, nextMode := 2, constraints :=
        [shared, crossing, .defined (.const Mode.aliased), .defined (.capture (μ 0)),
         shared, crossing, .defined (.const Mode.aliased), .defined (.capture (μ 0)),
         use 2, use 3]}⟩
  have hg : generate 100 (context.map ContextEntry.binding) term
      (initialInferenceState context) = .success g := by rfl
  have hterm : g.term = term := by rfl
  have hp : (match runSolver 100
      {pending := g.state.constraints, nextType := g.state.nextType,
       nextMode := g.state.nextMode} with
    | .success s => decide (s.bounds = residual) && decide (s.substitution = {})
    | _ => false) = true := by decide
  cases hr : runSolver 100
      {pending := g.state.constraints, nextType := g.state.nextType,
       nextMode := g.state.nextMode} <;> simp only [hr, Bool.and_eq_true,
         decide_eq_true_eq, Bool.false_eq_true] at hp
  rename_i s
  obtain ⟨hb, hsub⟩ := hp
  have hw : satisfiableModes 100 s.bounds = .success witness := by rw [hb]; exact hs
  obtain ⟨result, hi, hb', ht', hs', hbody⟩ := infer_from_stages hg hr hw
  refine ⟨result, hi, hb'.trans hb, ht'.trans hterm, hs'.trans hsub, ?_⟩
  rw [hbody, hsub]
  rfl

theorem succeeds : ∃ result, infer 100 context term = .success result ∧
    result.residual = residual ∧ result.elaborated = term ∧ result.substitution = {} := by
  obtain ⟨result, hi, hb, ht, hs, _⟩ := succeeds_with_type
  exact ⟨result, hi, hb, ht, hs⟩

def modes : ModVar → Mode
  | .flex 0 => Mode.global
  | _ => Mode.aliased

def predicate (_ : TypeVar) (m : Mode) : Prop := m.unique = true → m.isLocal = true

theorem predicate_mono (v : TypeVar) (m n : Mode) (hmn : m.le n = true) :
    predicate v m → predicate v n := by
  exact fun h hn => ((Mode.le_iff m n).mp hmn).1 (h (((Mode.le_iff m n).mp hmn).2.2 hn))

theorem mode_models : ModeModels residual modes := by
  simp [residual, ModeModels, ModeSatisfies, ModExpr.WellFormed, μ,
    aliasCapture, aliasFuture, ModExpr.eval, modes]

theorem bounds_preserve (a b : Ty) (hc : Constraint.sub a b ∈ residual) (k : Mode) :
    a.variablePredicate predicate modes k → b.variablePredicate predicate modes k := by
  simp only [residual, List.mem_cons, List.not_mem_nil, or_false,
    reduceCtorEq, Constraint.sub.injEq, false_or] at hc
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals simp [TypeExpr.variablePredicate, α, μ, predicate, modes, aliasCapture, aliasFuture,
    ModExpr.eval, ModExpr.epsilon, Mode.compose, Mode.global, Mode.aliased,
    Mode.many, Mode.identity, Mode.future, Mode.capture]

theorem missing_crossing : ¬ Subtype residual (α 0) (.modal (α 0) (.future (μ 0))) := by
  intro h
  have hp := h.variablePredicate predicate_mono mode_models bounds_preserve Mode.identity
    (show (α 0).variablePredicate predicate modes Mode.identity from fun _ => rfl)
  simp [TypeExpr.variablePredicate, α, μ, predicate, modes, ModExpr.eval,
    Mode.future, Mode.global, Mode.identity, Mode.compose] at hp

theorem residual_defined : residual.TypeBoundsDefined := by
  intro a b hc
  simp only [residual, List.mem_cons, List.not_mem_nil, or_false,
    reduceCtorEq, Constraint.sub.injEq, false_or] at hc
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals simp [TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels,
    ModeSatisfies, ModExpr.WellFormed, ModExpr.eval, α, μ,
    aliasCapture, aliasFuture, ModExpr.epsilon]

theorem capture_not_admissible : ¬ captured.Admissible residual := by
  rintro ⟨θ, hi, hb, hd⟩
  simp [Instantiates, captured, Scheme.mono, Scheme.lock] at hi
  exact missing_crossing (by
    simpa [captured, Scheme.mono, Scheme.lock, Substitution.bounds, Substitution.constraint,
      Substitution.ty, Substitution.type, Substitution.mode, TypeExpr.subst, ModExpr.subst,
      hi.1, hi.2, α, μ] using (hb _ (List.mem_map.mpr ⟨_, List.mem_singleton_self _, rfl⟩)).1)

theorem not_typable {Γ a} : ¬ Typing residual Γ elaborated a := by
  intro h
  obtain ⟨s, hs, ha⟩ := h.lam_capture_admissible residual_defined (i := 0)
    (by simp [Term.freeVars])
  exact capture_not_admissible ((show captured = s by simpa using hs).symm ▸ ha)

theorem context_scoped : Context.Scoped {types := {.flex 0}} context := by
  simp [Context.Scoped, context, Scheme.Scoped, Scheme.mono,
    Scheme.freeTypes, Scheme.freeModes, α, TypeExpr.typeVars, TypeExpr.modVars,
    Bounds.typeVars, Bounds.modVars]

/-- No typing derivation validates this historical, unrefined annotation. -/
theorem no_unshared_capture_typing : ¬ ∃ Γ a, Typing residual Γ elaborated a := by
  rintro ⟨Γ, a, h⟩
  exact not_typable h

end ModalityInference.SharingLockCapture
