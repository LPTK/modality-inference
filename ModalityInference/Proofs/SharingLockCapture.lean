import ModalityInference.Proofs.TypeVariablePredicates

/-! A focused check of capture metadata when a body shares a binding below a lock. -/
namespace ModalityInference.SharingLockCapture

def α (n : Nat) : Ty := .var (.flex n)
def μ (n : Nat) : ModExpr := .var (.flex n)
def context : Context := [some (.mono (α 0))]
def term : RawTerm := .lam () (.pair (.var 1) (.var 1))
def captured : Scheme := (Scheme.mono (α 0)).lock (μ 0)
def elaborated : AnnotatedTerm := .lam [some captured] (.pair (.var 1) (.var 1))
def aliasCapture : ModExpr := .compose (.const Mode.aliased) (.capture (μ 0))
def aliasFuture : ModExpr := .compose (.const Mode.aliased) (.future (μ 0))
def residual : Bounds :=
  [.sub (.modal (α 0) aliasCapture) (.modal (α 3) (μ 1)), .defined (μ 1),
   .defined aliasCapture, .sub (.modal (α 0) aliasCapture) (.modal (α 2) (μ 1)),
   .defined (.capture (μ 0)), .defined aliasFuture,
   .sub (.modal (α 0) (.const Mode.aliased)) (.modal (α 0) aliasFuture),
   .sub (.modal (α 0) .epsilon) (.modal (α 0) (.const Mode.many))]

theorem succeeds : ∃ result, infer 100 context term = .success result ∧
    result.residual = residual ∧ result.elaborated = elaborated ∧ result.substitution = {} :=
  ⟨_, rfl, rfl, rfl, rfl⟩

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

def UnsharedCaptureInferenceSoundness : Prop := ∀ {fuel Γ t result scope},
  Context.Scoped scope Γ → infer fuel Γ t = .success result →
    result.elaborated.erase = t ∧
      Typing result.residual (Γ.subst result.substitution) result.elaborated result.scheme.body

theorem no_unshared_capture_inference_soundness : ¬ UnsharedCaptureInferenceSoundness := by
  intro h
  obtain ⟨result, hs, hr, he, _⟩ := succeeds
  exact not_typable (by simpa only [hr, he] using (h context_scoped hs).2)

end ModalityInference.SharingLockCapture
