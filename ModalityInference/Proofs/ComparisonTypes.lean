import ModalityInference.ComparisonTypes
import ModalityInference.Proofs.Substitution

namespace ModalityInference

@[simp] theorem CompareTy.wellFormedBounds_ofTy (a : Ty) :
    (ofTy a).wellFormedBounds = a.wellFormedBounds := by
  induction a <;> simp_all [ofTy, wellFormedBounds, TypeExpr.wellFormedBounds]

/-- Ordinary syntactic subtyping embeds into internal comparison subtyping. -/
theorem Subtype.to_compare {Δ a b} (h : Subtype Δ a b) :
    CompareSubtype Δ (CompareTy.ofTy a) (CompareTy.ofTy b) := by
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

@[simp] theorem CompareTy.definedUnder_ofTy (a : Ty) (Δ : Bounds) :
    (ofTy a).DefinedUnder Δ ↔ a.DefinedUnder Δ := by
  simp [DefinedUnder, TypeExpr.DefinedUnder]

theorem Entails.to_compare {Δ c} (h : Entails Δ c) :
    CompareEntails Δ (CompareConstraint.ofConstraint c) := by
  cases c <;> simp only [Entails, CompareConstraint.ofConstraint, CompareEntails,
    CompareTy.definedUnder_ofTy] at *
  all_goals first
    | exact h
    | exact ⟨h.1.to_compare, h.2⟩
    | exact ⟨h.1.to_compare, h.2.1.to_compare, h.2.2⟩

@[simp] theorem CompareSubstitution.ofSubstitution_type (σ : Substitution) (v : TypeVar) :
    (ofSubstitution σ).type v = CompareTy.ofTy (σ.type v) := by
  cases v <;> simp only [ofSubstitution, type, Substitution.type, lookup_map_values]
  case flex n => cases σ.types.lookup n <;> rfl
  case rigid => rfl

@[simp] theorem CompareSubstitution.ofSubstitution_mode (σ : Substitution) :
    (ofSubstitution σ).mode = σ.mode := rfl

@[simp] theorem CompareSubstitution.ofSubstitution_ty (σ : Substitution) (a : Ty) :
    (ofSubstitution σ).ty a = CompareTy.ofTy (σ.ty a) := by
  induction a <;> simp_all [ty, CompareTy.ofTy, CompareTy.subst, Substitution.ty, TypeExpr.subst]

@[simp] theorem CompareSubstitution.ofSubstitution_constraint (σ : Substitution) (c : Constraint) :
    (ofSubstitution σ).constraint c = CompareConstraint.ofConstraint (σ.constraint c) := by
  cases c <;> simp only [constraint, Substitution.constraint, Constraint.subst,
    ofSubstitution_ty, ofSubstitution_mode, CompareConstraint.ofConstraint]
  case equal v t =>
    cases v <;> simp only [ofSubstitution, lookup_map_values]
    case flex n => cases σ.types.lookup n <;> rfl
  all_goals rfl

@[simp] theorem CompareSubstitution.ofSubstitution_bounds (σ : Substitution) (cs : Bounds) :
    (ofSubstitution σ).bounds cs = (σ.bounds cs).map CompareConstraint.ofConstraint := by
  simp [bounds, Substitution.bounds, List.map_map, Function.comp_def]

theorem Instantiates.to_compare {s σ} (h : Instantiates s σ) :
    CompareInstantiates s (CompareSubstitution.ofSubstitution σ) := by
  simpa [Instantiates, CompareInstantiates, CompareSubstitution.ofSubstitution,
    List.map_map, Function.comp_def] using h

theorem EntailsAll.to_compare {Δ cs} (h : EntailsAll Δ cs) :
    CompareEntailsAll Δ (cs.map CompareConstraint.ofConstraint) := by
  intro c hc
  obtain ⟨c, hd, rfl⟩ := List.mem_map.mp hc
  exact (h c hd).to_compare

/-- Every witness of the original syntactic scheme relation remains available. -/
theorem Subsumes.to_compare {Δ source target} (h : Subsumes Δ source target) :
    CompareSubsumes Δ source target := by
  obtain ⟨σ, hσ, hb, ht⟩ := h
  refine ⟨CompareSubstitution.ofSubstitution σ, hσ.to_compare, ?_, ?_⟩
  · simpa only [CompareSubstitution.ofSubstitution_bounds] using hb.to_compare
  · simpa only [CompareSubstitution.ofSubstitution_ty] using ht.to_compare

/-- A join supplies a common interpolant for two lower bounds and two upper bounds. -/
theorem CompareSubtype.join_interpolant {Δ : Bounds} {a b c d : CompareTy}
    (hac : CompareSubtype Δ a c) (had : CompareSubtype Δ a d)
    (hbc : CompareSubtype Δ b c) (hbd : CompareSubtype Δ b d) :
    CompareSubtype Δ a (.join a b) ∧ CompareSubtype Δ b (.join a b) ∧
      CompareSubtype Δ (.join a b) c ∧ CompareSubtype Δ (.join a b) d := by
  exact ⟨.joinLeft, .joinRight, .joinLeast hac hbc, .joinLeast had hbd⟩

/-- Internal joins reconstruct an instantiation between all four sides of a bowtie. -/
theorem CompareSubsumes.bowtie {Δ : Bounds} (a b c d : Nat)
    (hac : Constraint.sub (.var (.rigid a)) (.var (.rigid c)) ∈ Δ)
    (had : Constraint.sub (.var (.rigid a)) (.var (.rigid d)) ∈ Δ)
    (hbc : Constraint.sub (.var (.rigid b)) (.var (.rigid c)) ∈ Δ)
    (hbd : Constraint.sub (.var (.rigid b)) (.var (.rigid d)) ∈ Δ) :
    CompareSubsumes Δ
      { typeParams := [0]
        bounds := [.sub (.var (.rigid a)) (.var (.flex 0)),
          .sub (.var (.rigid b)) (.var (.flex 0)),
          .sub (.var (.flex 0)) (.var (.rigid c)),
          .sub (.var (.flex 0)) (.var (.rigid d))]
        body := .unit }
      (Scheme.mono .unit) := by
  refine ⟨{ types := [(0, .join (.var (.rigid a)) (.var (.rigid b)))] }, ?_, ?_, ?_⟩
  case refine_2 =>
    simp [CompareEntailsAll, CompareEntails, CompareSubstitution.bounds,
      CompareSubstitution.constraint, CompareSubstitution.ty, CompareTy.ofTy,
      CompareTy.subst, CompareSubstitution.type, Scheme.mono, Substitution.bounds,
      Bounds.assumptions, CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels]
    exact CompareSubtype.join_interpolant (.bound hac) (.bound had) (.bound hbc) (.bound hbd)
  case refine_1 => exact ⟨List.Perm.refl _, List.Perm.refl _⟩
  case refine_3 => exact .refl

end ModalityInference
