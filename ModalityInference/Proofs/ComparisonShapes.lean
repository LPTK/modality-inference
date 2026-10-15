import ModalityInference.ComparisonShapes
import ModalityInference.Proofs.ComparisonTypes
import ModalityInference.Proofs.SchemeReconstructionClosed

namespace ModalityInference

@[simp] theorem CompareTy.shape_ofTy (a : Ty) :
    (ofTy a).shape = ComparisonShape.ofTy a := by
  induction a <;> simp_all [ofTy, shape, ComparisonShape.ofTy]

@[simp] theorem CompareTy.wellShaped_ofTy (a : Ty) (Δ : Bounds) :
    (ofTy a).WellShaped Δ := by
  induction a <;> simp_all [ofTy, WellShaped]

/-- Forgetting shape evidence yields unrestricted comparison subtyping. -/
theorem ShapedSubtype.to_compare {Δ a b} (h : ShapedSubtype Δ a b) :
    CompareSubtype Δ a b := by
  induction h
  all_goals first
    | exact .refl
    | exact .trans ‹_› ‹_›
    | exact .bound ‹_›
    | exact .identity
    | exact .identityRev
    | exact .compose
    | exact .composeRev
    | exact .congr ‹_› ‹_›
    | exact .prod ‹_› ‹_›
    | exact .sum ‹_› ‹_›
    | exact .fn ‹_› ‹_› ‹_›
    | exact .joinLeft
    | exact .joinRight
    | exact .joinLeast ‹_› ‹_›
    | exact .meetLeft
    | exact .meetRight
    | exact .meetGreatest ‹_› ‹_›

theorem ShapedSubtype.shape_invariant {Δ a b} (h : ShapedSubtype Δ a b) :
    a.WellShaped Δ ∧ b.WellShaped Δ ∧ ComparisonShape.Equivalent Δ a.shape b.shape := by
  induction h
  all_goals simp_all [CompareTy.WellShaped, CompareTy.shape, ComparisonShape.Equivalent,
    ComparisonShape.subst]
  case bound a b h =>
    exact fun ρ hρ => hρ (_, _) (List.mem_flatMap.mpr ⟨.sub a b, h, by simp⟩)

theorem ShapedSubtype.wellShaped_left {Δ a b} (h : ShapedSubtype Δ a b) :
    a.WellShaped Δ := h.shape_invariant.1

theorem ShapedSubtype.wellShaped_right {Δ a b} (h : ShapedSubtype Δ a b) :
    b.WellShaped Δ := h.shape_invariant.2.1

theorem ShapedSubtype.shape_equivalent {Δ a b} (h : ShapedSubtype Δ a b) :
    ComparisonShape.Equivalent Δ a.shape b.shape := h.shape_invariant.2.2

/-- Shape admissibility preserves every ordinary syntactic subtype derivation. -/
theorem Subtype.to_shaped {Δ a b} (h : Subtype Δ a b) :
    ShapedSubtype Δ (CompareTy.ofTy a) (CompareTy.ofTy b) := by
  induction h
  all_goals first
    | exact .refl (CompareTy.wellShaped_ofTy _ _)
    | exact .trans ‹_› ‹_›
    | exact .bound ‹_›
    | exact .identity (CompareTy.wellShaped_ofTy _ _)
    | exact .identityRev (CompareTy.wellShaped_ofTy _ _)
    | exact .compose (CompareTy.wellShaped_ofTy _ _)
    | exact .composeRev (CompareTy.wellShaped_ofTy _ _)
    | exact .congr ‹_› ‹_›
    | exact .prod ‹_› ‹_›
    | exact .sum ‹_› ‹_›
    | exact .fn ‹_› ‹_› ‹_›

theorem Entails.to_shaped {Δ c} (h : Entails Δ c) :
    ShapedEntails Δ (CompareConstraint.ofConstraint c) := by
  cases c <;> simp only [Entails, CompareConstraint.ofConstraint, ShapedEntails,
    CompareTy.definedUnder_ofTy] at *
  all_goals first
    | exact h
    | exact ⟨h.1.to_shaped, h.2⟩
    | exact ⟨h.1.to_shaped, h.2.1.to_shaped, h.2.2⟩

theorem EntailsAll.to_shaped {Δ cs} (h : EntailsAll Δ cs) :
    ShapedEntailsAll Δ (cs.map CompareConstraint.ofConstraint) :=
  fun _ hc => match List.mem_map.mp hc with
    | ⟨d, hd, he⟩ => he ▸ (h d hd).to_shaped

theorem CompareSubstitution.wellShaped_ofSubstitution (σ : Substitution) (Δ : Bounds) :
    (ofSubstitution σ).WellShaped Δ := by
  simp only [WellShaped, ofSubstitution, List.forall_mem_map]
  exact fun _ _ => CompareTy.wellShaped_ofTy _ _

/-- The restriction preserves every witness of ordinary syntactic subsumption,
without requiring satisfiable declared assumptions. -/
theorem Subsumes.to_shaped {Δ source target} (h : Subsumes Δ source target) :
    ShapedSubsumes Δ source target := by
  obtain ⟨σ, hσ, hb, ht⟩ := h
  refine ⟨CompareSubstitution.ofSubstitution σ, hσ.to_compare,
    CompareSubstitution.wellShaped_ofSubstitution _ _, ?_, ?_⟩
  all_goals first
    | simpa only [CompareSubstitution.ofSubstitution_bounds] using hb.to_shaped
    | simpa only [CompareSubstitution.ofSubstitution_ty] using ht.to_shaped

theorem ShapedEntails.to_compare {Δ c} (h : ShapedEntails Δ c) : CompareEntails Δ c := by
  cases c <;> simp only [ShapedEntails, CompareEntails] at *
  all_goals first
    | exact h
    | exact ⟨h.1.to_compare, h.2⟩
    | exact ⟨h.1.to_compare, h.2.1.to_compare, h.2.2⟩

theorem ShapedEntailsAll.to_compare {Δ cs} (h : ShapedEntailsAll Δ cs) :
    CompareEntailsAll Δ cs := fun c hc => (h c hc).to_compare

theorem ShapedSubsumes.to_compare {Δ source target} (h : ShapedSubsumes Δ source target) :
    CompareSubsumes Δ source target :=
  match h with | ⟨σ, hσ, _, hb, ht⟩ => ⟨σ, hσ, hb.to_compare, ht.to_compare⟩

theorem ComparisonShape.Equivalent.refl {Δ a} : Equivalent Δ a a := fun _ _ => rfl

theorem ComparisonShape.Equivalent.symm {Δ a b} (h : Equivalent Δ a b) :
    Equivalent Δ b a := fun ρ hρ => (h ρ hρ).symm

theorem ComparisonShape.Equivalent.trans {Δ a b c} (hab : Equivalent Δ a b)
    (hbc : Equivalent Δ b c) : Equivalent Δ a c := fun ρ hρ => (hab ρ hρ).trans (hbc ρ hρ)

theorem ComparisonShape.Equivalent.of_sub {Δ a b} (h : Constraint.sub a b ∈ Δ) :
    Equivalent Δ (ofTy a) (ofTy b) :=
  fun ρ hρ => hρ (_, _) (List.mem_flatMap.mpr ⟨.sub a b, h, by simp⟩)

theorem CompareTy.not_wellShaped_unit_join_credit {Δ} (ρ : TypeVar → ComparisonShape)
    (hρ : ComparisonShape.Models Δ ρ) : ¬(CompareTy.join .unit .credit).WellShaped Δ :=
  fun h => ComparisonShape.noConfusion (h.2.2 ρ hρ)

theorem CompareTy.not_wellShaped_unit_meet_credit {Δ} (ρ : TypeVar → ComparisonShape)
    (hρ : ComparisonShape.Models Δ ρ) : ¬(CompareTy.meet .unit .credit).WellShaped Δ :=
  fun h => ComparisonShape.noConfusion (h.2.2 ρ hρ)

theorem ShapedSubtype.no_unit_credit_upper {Δ a} (ρ : TypeVar → ComparisonShape)
    (hρ : ComparisonShape.Models Δ ρ) (hu : ShapedSubtype Δ .unit a)
    (hc : ShapedSubtype Δ .credit a) : False :=
  ComparisonShape.noConfusion ((hu.shape_equivalent ρ hρ).trans (hc.shape_equivalent ρ hρ).symm)

theorem ShapedSubtype.join_interpolant {Δ : Bounds} {a b c d : CompareTy}
    (hac : ShapedSubtype Δ a c) (had : ShapedSubtype Δ a d)
    (hbc : ShapedSubtype Δ b c) (hbd : ShapedSubtype Δ b d) :
    ShapedSubtype Δ a (.join a b) ∧ ShapedSubtype Δ b (.join a b) ∧
      ShapedSubtype Δ (.join a b) c ∧ ShapedSubtype Δ (.join a b) d :=
  let hw : (CompareTy.join a b).WellShaped Δ :=
    ⟨hac.wellShaped_left, hbc.wellShaped_left,
      hac.shape_equivalent.trans hbc.shape_equivalent.symm⟩
  ⟨.joinLeft hw, .joinRight hw, .joinLeast hac hbc, .joinLeast had hbd⟩

/-- Declared bounds force the four rigid endpoints to share one shape, so the
internal join is admissible without identifying source goals with assumptions. -/
theorem ShapedSubsumes.bowtie {Δ : Bounds} (a b c d : Nat)
    (hac : Constraint.sub (.var (.rigid a)) (.var (.rigid c)) ∈ Δ)
    (had : Constraint.sub (.var (.rigid a)) (.var (.rigid d)) ∈ Δ)
    (hbc : Constraint.sub (.var (.rigid b)) (.var (.rigid c)) ∈ Δ)
    (hbd : Constraint.sub (.var (.rigid b)) (.var (.rigid d)) ∈ Δ) :
    ShapedSubsumes Δ
      { typeParams := [0]
        bounds := [.sub (.var (.rigid a)) (.var (.flex 0)),
          .sub (.var (.rigid b)) (.var (.flex 0)),
          .sub (.var (.flex 0)) (.var (.rigid c)),
          .sub (.var (.flex 0)) (.var (.rigid d))]
        body := .unit }
      (Scheme.mono .unit) := by
  refine ⟨{ types := [(0, .join (.var (.rigid a)) (.var (.rigid b)))] }, ?_, ?_, ?_, ?_⟩
  case refine_3 =>
    simp [ShapedEntailsAll, ShapedEntails, CompareSubstitution.bounds,
      CompareSubstitution.constraint, CompareSubstitution.ty, CompareTy.ofTy,
      CompareTy.subst, CompareSubstitution.type, Scheme.mono, Substitution.bounds,
      Bounds.assumptions, CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels]
    exact ShapedSubtype.join_interpolant (.bound hac) (.bound had) (.bound hbc) (.bound hbd)
  case refine_2 =>
    simp [CompareSubstitution.WellShaped, CompareTy.WellShaped, CompareTy.shape,
      Scheme.mono, Substitution.bounds, Bounds.assumptions]
    exact (ComparisonShape.Equivalent.of_sub hac).trans (ComparisonShape.Equivalent.of_sub hbc).symm
  all_goals first
    | exact ⟨List.Perm.refl _, List.Perm.refl _⟩
    | exact .refl trivial

theorem ShapedSubsumes.not_mixed_unit_credit : ¬ShapedSubsumes []
    { typeParams := [0]
      bounds := [.sub .unit (.var (.flex 0)), .sub .credit (.var (.flex 0))]
      body := .unit }
    (Scheme.mono .unit) := by
  rintro ⟨σ, _, _, hb, _⟩
  change ShapedEntailsAll [] (σ.bounds [.sub .unit (.var (.flex 0)),
    .sub .credit (.var (.flex 0))]) at hb
  exact ShapedSubtype.no_unit_credit_upper (fun _ => .unit)
    (by simp [ComparisonShape.Models, ComparisonShape.pairs])
    (hb (σ.constraint (.sub .unit (.var (.flex 0))))
      (by simp [CompareSubstitution.bounds])).1
    (hb (σ.constraint (.sub .credit (.var (.flex 0))))
      (by simp [CompareSubstitution.bounds])).1

theorem ShapedSubtype.fn_congr {Δ a b c d} (ha : ShapedSubtype Δ c a)
    (hb : ShapedSubtype Δ b d) : ShapedSubtype Δ (.fn a b) (.fn c d) :=
  (ShapedSubtype.identityRev (a := .fn a b) ⟨ha.wellShaped_right, hb.wellShaped_left⟩).trans
    ((ShapedSubtype.fn ha hb (.valid fun _ _ =>
      ⟨Mode.identity, Mode.identity.compose Mode.top, rfl, rfl, by decide⟩)).trans
      (.identity ⟨ha.wellShaped_left, hb.wellShaped_right⟩))

theorem ShapedSubtype.prod_congr {Δ a b c d} (ha : ShapedSubtype Δ a c)
    (hb : ShapedSubtype Δ b d) : ShapedSubtype Δ (.prod a b) (.prod c d) :=
  (ShapedSubtype.identityRev (a := .prod a b) ⟨ha.wellShaped_left, hb.wellShaped_left⟩).trans
    ((ShapedSubtype.prod
      ((ShapedSubtype.identity ha.wellShaped_left).trans (ha.trans (.identityRev ha.wellShaped_right)))
      ((ShapedSubtype.identity hb.wellShaped_left).trans (hb.trans (.identityRev hb.wellShaped_right)))).trans
      (.identity ⟨ha.wellShaped_right, hb.wellShaped_right⟩))

private theorem closed_join_wellShaped :
    (CompareTy.join (.var (.rigid 4)) (.var (.rigid 5))).WellShaped SchemeReconstructionClosed.bounds :=
  ⟨trivial, trivial,
    (ComparisonShape.Equivalent.of_sub (a := .var (.rigid 4)) (b := .var (.rigid 6))
      (by simp [SchemeReconstructionClosed.bounds])).trans
    (ComparisonShape.Equivalent.of_sub (a := .var (.rigid 5)) (b := .var (.rigid 6))
      (by simp [SchemeReconstructionClosed.bounds])).symm⟩

theorem ShapedSubsumes.closed_bowtie : ShapedSubsumes []
    SchemeReconstructionClosed.source SchemeReconstructionClosed.target := by
  refine ⟨{ types := [(0, .join (.var (.rigid 4)) (.var (.rigid 5)))] }, ?_, ?_, ?_, ?_⟩
  case refine_4 =>
    change ShapedSubtype SchemeReconstructionClosed.bounds
      (.fn (.join (.var (.rigid 4)) (.var (.rigid 5)))
        (.fn (.join (.var (.rigid 4)) (.var (.rigid 5)))
          (.prod (.join (.var (.rigid 4)) (.var (.rigid 5)))
            (.join (.var (.rigid 4)) (.var (.rigid 5))))))
      (.fn (.var (.rigid 4)) (.fn (.var (.rigid 5))
        (.prod (.var (.rigid 6)) (.var (.rigid 7)))))
    refine ShapedSubtype.fn_congr (.joinLeft closed_join_wellShaped)
      (.fn_congr (.joinRight closed_join_wellShaped)
        (.prod_congr (.joinLeast ?_ ?_) (.joinLeast ?_ ?_)))
    all_goals
      exact .bound (a := .var _) (b := .var _) (by simp [SchemeReconstructionClosed.bounds])
  case refine_2 =>
    simpa [CompareSubstitution.WellShaped] using closed_join_wellShaped
  all_goals first
    | exact ⟨List.Perm.refl _, List.Perm.refl _⟩
    | simp [ShapedEntailsAll, CompareSubstitution.bounds, SchemeReconstructionClosed.source]

end ModalityInference
