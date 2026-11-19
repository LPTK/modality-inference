import ModalityInference.Proofs.ComparisonTotalDerivation

/-! Defined comparisons can avoid partial intermediates whenever each declared
subtype edge has equally defined endpoints. Partial edges need not be reflexive
or redundant, and their shape equations remain in the original context. -/
namespace ModalityInference.ComparisonBalancedDerivation

open ComparisonDefinedCovers ComparisonTotalDerivation

/-- A raw edge does not cross between defined and partial public types. -/
def Balanced (Δ : Bounds) : Prop :=
  ∀ a b, Constraint.sub a b ∈ Δ → (a.DefinedUnder Δ ↔ b.DefinedUnder Δ)

noncomputable section
attribute [local instance] Classical.propDecidable

theorem normal_public (Δ : Bounds) (lower : Bool) (a : Ty) :
    normal Δ lower (.ofTy a) = if a.DefinedUnder Δ then some (.ofTy a) else none := by
  induction a generalizing lower with
  | var | unit | credit =>
    simp [CompareTy.ofTy, normal, TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    simp only [CompareTy.ofTy, normal, iha, ihb]
    split_ifs <;> simp_all [strict, ← CompareTy.definedUnder_ofTy, CompareTy.ofTy,
      CompareTy.definedUnder_prod_iff, CompareTy.definedUnder_sum_iff, CompareTy.definedUnder_fn_iff]
  | modal a m ih =>
    simp only [CompareTy.ofTy, normal, ih]
    split_ifs <;> simp_all [← CompareTy.definedUnder_ofTy, CompareTy.ofTy,
      CompareTy.definedUnder_modal_iff]

theorem bound_lift {Δ a b} (hΔ : Balanced Δ) (h : Constraint.sub a b ∈ Δ)
    (lower : Bool) :
    Lift Δ lower (normal Δ lower (.ofTy a)) (normal Δ lower (.ofTy b)) := by
  by_cases ha : a.DefinedUnder Δ
  · simpa only [normal_public, if_pos ha, if_pos ((hΔ _ _ h).mp ha), Lift] using
      Derivation.bound h ((CompareTy.definedUnder_ofTy _ _).mpr ha)
        ((CompareTy.definedUnder_ofTy _ _).mpr ((hΔ _ _ h).mp ha))
  · simp only [normal_public, if_neg ha, if_neg (fun hb => ha ((hΔ _ _ h).mpr hb)), Lift]

/-- The same context is retained, including partial edges and all shape facts;
every term of the resulting derivation is defined at every structural depth. -/
theorem derivation {Δ a b} (hΔ : Balanced Δ)
    (ha : CompareTy.DefinedUnder a Δ) (hb : CompareTy.DefinedUnder b Δ)
    (h : AlgebraSubtype Δ a b) : Derivation Δ a b :=
  derivation_of_bounds (fun _ _ => bound_lift hΔ) ha hb h

theorem derivation_iff {Δ a b} (hΔ : Balanced Δ)
    (ha : CompareTy.DefinedUnder a Δ) (hb : CompareTy.DefinedUnder b Δ) :
    Derivation Δ a b ↔ AlgebraSubtype Δ a b :=
  ⟨Derivation.subtype, derivation hΔ ha hb⟩

/-- A defined source cannot reach a partial public target without an ambient
edge that crosses the definedness boundary. -/
theorem public_defined_right {Δ : Bounds} (hΔ : Balanced Δ) {a : CompareTy} {b : Ty}
    (ha : a.DefinedUnder Δ) (h : AlgebraSubtype Δ a (.ofTy b)) : b.DefinedUnder Δ := by
  by_contra hb
  simpa only [normal_defined ha, normal_public, if_neg hb, Lift, Bool.true_eq_false] using
    normal_derivation_of_bounds (fun _ _ => bound_lift hΔ) h true

theorem public_defined_left {Δ : Bounds} (hΔ : Balanced Δ) {a : Ty} {b : CompareTy}
    (hb : b.DefinedUnder Δ) (h : AlgebraSubtype Δ (.ofTy a) b) : a.DefinedUnder Δ := by
  by_contra ha
  simpa only [normal_public, if_neg ha, normal_defined hb, Lift, Bool.false_eq_true] using
    normal_derivation_of_bounds (fun _ _ => bound_lift hΔ) h false

theorem of_typeBoundsDefined {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) : Balanced Δ :=
  fun _ _ h => ⟨fun _ => (hΔ _ _ h).2, fun _ => (hΔ _ _ h).1⟩

end
end ModalityInference.ComparisonBalancedDerivation
