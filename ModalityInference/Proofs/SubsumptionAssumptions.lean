import ModalityInference.Proofs.SchemeBounds

/-! Target scheme bounds must expose equality directions and written guards
as assumptions when checking scheme subsumption. -/
namespace ModalityInference

theorem Subtype.of_trivial_bounds {Δ a b} (h : Subtype Δ a b)
    (hb : ∀ x y, Constraint.sub x y ∉ Δ) (hm : ∀ η, ModeModels Δ η) : Subtype [] a b := by
  induction h
  case bound a b hc => exact False.elim (hb a b hc)
  all_goals first
    | exact .refl
    | exact .trans ‹_› ‹_›
    | exact .identity
    | exact .identityRev
    | exact .compose
    | exact .composeRev
    | exact .congr ‹_› (.valid fun η _ => Submode.denote ‹_› (hm η))
    | exact .prod ‹_› ‹_›
    | exact .sum ‹_› ‹_›
    | exact .fn ‹_› ‹_› (.valid fun η _ => Submode.denote ‹_› (hm η))
    | exact .credit (.valid fun η _ => Submode.denote ‹_› (hm η))

namespace SubsumptionAssumptions

def RawTargetSubsumes (Δ : Bounds) (source target : Scheme) : Prop :=
  let (nt, nm) := source.subsumptionIndices Δ target
  let (assumptions, t) := target.instantiate nt nm true
  ∃ σ, Instantiates source σ ∧ EntailsAll (Δ ++ assumptions) (σ.bounds source.bounds) ∧
    Subtype (Δ ++ assumptions) (σ.ty source.body) t

theorem RawTargetSubsumes.corrected {Δ source target} (h : RawTargetSubsumes Δ source target) :
    Subsumes Δ source target := by
  obtain ⟨σ, hi, hb, ht⟩ := h
  exact ⟨σ, hi, fun c hc => (hb c hc).assumptions_right, ht.assumptions_right⟩

def scheme : Scheme :=
  {typeParams := [0], bounds := [.equal (.flex 0) .unit], body := .var (.flex 0)}

theorem scheme_unit_instance :
    ∃ θ, Instantiates scheme θ ∧ EntailsAll [] (θ.bounds scheme.bounds) ∧ θ.ty scheme.body = .unit := by
  refine ⟨{types := [(0, .unit)]}, by simp [Instantiates, scheme], ?_, rfl⟩
  simp [scheme, Substitution.bounds, Substitution.constraint, Substitution.ty, TypeExpr.subst,
    EntailsAll, Entails, TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]
  exact .refl

theorem raw_not_reflexive : ¬ RawTargetSubsumes [] scheme scheme := by
  rintro ⟨σ, _, hb, ht⟩
  change EntailsAll [.equiv (.var (.rigid 1)) .unit] (σ.bounds [.equal (.flex 0) .unit]) at hb
  change Subtype [.equiv (.var (.rigid 1)) .unit] (σ.type (.flex 0)) (.var (.rigid 1)) at ht
  have he := (σ.equal_entails [.equiv (.var (.rigid 1)) .unit] (.flex 0) .unit).mp
    (hb _ (by simp [Substitution.bounds]))
  have hh : Subtype [] .unit (.var (.rigid 1)) := (he.2.1.trans ht).of_trivial_bounds
    (by simp) (by simp [ModeModels, ModeSatisfies])
  exact (hh.semantic (ρ := ⟨fun _ => .credit Mode.identity, fun _ => Mode.identity⟩)
    (w := ⟨∅⟩) (v := .unit) (ambient := Mode.identity) (by simp [GroundModels]) rfl rfl
    ⟨(fun _ hr => nomatch hr), trivial⟩).1.2

theorem corrected_reflexive : Subsumes [] scheme scheme := Subsumes.refl _ _

end SubsumptionAssumptions
end ModalityInference
