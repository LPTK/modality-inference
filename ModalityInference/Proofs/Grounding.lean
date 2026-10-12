import ModalityInference.Semantics

/-! Scheme quantifiers bind assignments, including identifiers used only in capture metadata. -/
namespace ModalityInference

theorem GroundInstantiates.self {ρ s} (h : GroundModels ρ s.bounds) :
    GroundInstantiates ρ s ρ := ⟨fun _ _ => rfl, fun _ _ => rfl, h⟩

theorem GroundInstantiates.mono_iff {ρ η t} :
    GroundInstantiates ρ (.mono t) η ↔ η = ρ := by
  cases ρ; cases η
  simp [GroundInstantiates, Scheme.mono, GroundModels, funext_iff]

theorem GroundInstantiates.modal_iff {ρ η s m} :
    GroundInstantiates ρ (s.modal m) η ↔ GroundInstantiates ρ s η := Iff.rfl

theorem SchemeInterpretation.mono_iff {ρ w a v} :
    SchemeInterpretation ρ w (.mono a) v ↔
      ∀ t, a.realize ρ = some t → ValueInterpretation ρ w t Mode.identity v := by
  simp [SchemeInterpretation, GroundInstantiates.mono_iff]
  exact ⟨fun h t ht => h ρ t rfl ht, fun h η t he ht => by subst η; exact h t ht⟩

theorem BindingOwns.mono_iff {ρ v a l} :
    BindingOwns ρ v (.mono a) l ↔ ∃ t, a.realize ρ = some t ∧ Owns ρ v t l := by
  simp only [BindingOwns, GroundInstantiates.mono_iff]
  simp [Scheme.mono]

theorem EnvironmentInterpretation.singleton {ρ w s v}
    (h : SchemeInterpretation ρ w s v) : EnvironmentInterpretation ρ w [some s] [v] := by
  constructor
  · intro i t ht
    cases i <;> simp at ht
    cases ht
    exact ⟨v, rfl, h⟩
  · intro i j s t v u l hij hi hj _ _
    cases i <;> cases j <;> simp_all

namespace AmbientCaptureScope

def scheme : Scheme := .mono (.fn .unit .unit)
def ambient : GroundAssignment := ⟨fun _ => .unit Mode.identity, fun _ => Mode.aliased⟩
def changed : GroundAssignment :=
  {ambient with modes := fun v => if v = .flex 0 then Mode.identity else ambient.modes v}

/-- The former free-variable-only condition admitted this change, although μ₀
can still be a free identifier in a closure's typed capture metadata. -/
theorem former_condition :
    (∀ v ∈ scheme.freeTypes, changed.types v = ambient.types v) ∧
    (∀ v ∈ scheme.freeModes, changed.modes v = ambient.modes v) ∧
    GroundModels changed scheme.bounds := by
  simp [scheme, Scheme.mono, Scheme.freeTypes, Scheme.freeModes, TypeExpr.typeVars,
    TypeExpr.modVars, Bounds.typeVars, Bounds.modVars, GroundModels]

theorem unquantified_change_rejected : ¬ GroundInstantiates ambient scheme changed := by
  intro h
  have hm := h.2.1 (.flex 0) (by simp [scheme, Scheme.mono])
  simp [changed, ambient, Mode.identity, Mode.aliased] at hm

end AmbientCaptureScope
end ModalityInference
