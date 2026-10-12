import ModalityInference.Proofs.Grounding

/-! A quantified modality must not be captured by ambient bounds in a context rule. -/
namespace ModalityInference.ContextScoping

def μ : ModExpr := .var (.flex 0)
def scheme : Scheme := {modParams := [0], body := .modal .credit μ}
def bounds : Bounds := [.mode (.const Mode.aliased) μ]
def ambient : GroundAssignment := ⟨fun _ => .unit Mode.identity, fun _ => Mode.aliased⟩
def uniqueInstance : GroundAssignment :=
  {ambient with modes := fun v => if v = .flex 0 then Mode.identity else ambient.modes v}

theorem ambient_models : GroundModels ambient bounds := by
  simp [GroundModels, bounds, GroundSatisfies, ModExpr.Below, ModExpr.eval, μ,
    ambient, Mode.le, Mode.aliased]

theorem sharing_premise :
    Subtype (bounds ++ scheme.bounds) (.modal scheme.body (.const Mode.aliased)) scheme.body := by
  apply Subtype.trans Subtype.compose
  apply Subtype.congr Subtype.refl
  apply Submode.valid
  intro η hη
  simp [ModeModels, ModeSatisfies, bounds, scheme, μ, ModExpr.Below, ModExpr.eval,
    Mode.le, Mode.aliased] at hη
  simp [ModExpr.Below, ModExpr.eval, μ, Mode.compose, Mode.aliased, Mode.le, hη.1.1, hη.1.2, hη.2]

theorem input_interpreted (w : World) :
    SchemeInterpretation ambient w (scheme.modal (.const Mode.many)) (.credit (.heap 0)) := by
  intro η t _ ht
  simp [scheme, Scheme.modal, TypeExpr.realize, μ, ModExpr.eval, GroundTy.modal] at ht
  cases ht
  exact ⟨fun _ h => by cases h; trivial, Or.inr trivial⟩

theorem unique_instantiates : GroundInstantiates ambient scheme uniqueInstance := by
  simp [GroundInstantiates, scheme, uniqueInstance, GroundModels]
  exact fun _ h he => (h he).elim

theorem component_owns : EnvironmentOwns ambient [.credit (.heap 0)] [some scheme] (.heap 0) := by
  exact ⟨0, scheme, .credit (.heap 0), rfl, rfl, uniqueInstance, .credit Mode.identity,
    unique_instantiates, rfl, .credit rfl⟩

/-- The old sharing premise is satisfied, yet its two proposed components both
own the same cell. The ambient bound constrains μ₀; the scheme binds that name. -/
theorem old_sharing_premise_insufficient (w : World) :
    GroundModels ambient bounds ∧
    EnvironmentInterpretation ambient w [some (scheme.modal (.const Mode.many))]
      [.credit (.heap 0)] ∧
    Subtype (bounds ++ scheme.bounds) (.modal scheme.body (.const Mode.aliased)) scheme.body ∧
    ¬ (∀ l, ¬ (EnvironmentOwns ambient [.credit (.heap 0)] [some scheme] l ∧
      EnvironmentOwns ambient [.credit (.heap 0)] [some scheme] l)) := by
  exact ⟨ambient_models, .singleton (input_interpreted w), sharing_premise,
    fun h => h (.heap 0) ⟨component_owns, component_owns⟩⟩

/-- The corrected rule rejects precisely the bound/quantifier collision. -/
theorem not_fresh : ¬ scheme.FreshForBounds bounds := by
  simp [Scheme.FreshForBounds, scheme, bounds, μ, Bounds.modVars, Constraint.modVars,
    ModExpr.vars]

theorem lock_not_fresh : ¬ scheme.FreshForMode μ := by
  simp [Scheme.FreshForMode, scheme, μ, ModExpr.vars]

/-- Alpha-renaming restores the intended polymorphic scope; the restriction
does not require making the binding monomorphic. -/
theorem renamed_fresh : (scheme.subst {}).FreshForBounds bounds ∧
    (scheme.subst {}).FreshForMode μ := by
  have renamed : scheme.subst {} =
      {modParams := [1], body := .modal .credit (.var (.flex 1))} := rfl
  simp [renamed, Scheme.FreshForBounds, Scheme.FreshForMode, bounds, μ,
    Bounds.modVars, Constraint.modVars, ModExpr.vars]

end ModalityInference.ContextScoping
