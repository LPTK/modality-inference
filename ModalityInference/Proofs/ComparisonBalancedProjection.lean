import ModalityInference.Proofs.ComparisonBalancedContext

/-! Retain shape information separately from the subtype edges used by a
defined derivation. These are already prepared algebra contexts: `equiv`
entries supply shape equations, while `ShapedSubtype.bound` reads only `sub`.
Applying `Bounds.assumptions` again would change this representation. -/
namespace ModalityInference.ComparisonBalancedProjection

open ComparisonBalancedDerivation

def shapeFact : Constraint → Constraint
  | .sub a b => .equiv a b
  | c => c

def shapeShadow (Δ : Bounds) : Bounds := Δ.map shapeFact

noncomputable def project (Δ : Bounds) : Bounds :=
  ComparisonBalancedContext.prune Δ ++ shapeShadow Δ

theorem pairs_shadow (Δ : Bounds) :
    ComparisonShape.pairs (shapeShadow Δ) = ComparisonShape.pairs Δ := by
  simp only [shapeShadow, ComparisonShape.pairs, List.flatMap_map]
  congr 1
  exact funext fun c => by cases c <;> rfl

theorem mode_shapeFact (η : ModVar → Mode) (c : Constraint) :
    ModeSatisfies η (shapeFact c) = ModeSatisfies η c := by
  cases c <;> rfl

theorem modeModels_shadow (Δ : Bounds) (η : ModVar → Mode) :
    ModeModels (shapeShadow Δ) η ↔ ModeModels Δ η := by
  simp only [ModeModels, shapeShadow, List.forall_mem_map, mode_shapeFact]

theorem sub_not_mem_shadow (Δ : Bounds) (a b : Ty) :
    Constraint.sub a b ∉ shapeShadow Δ := by
  simp only [shapeShadow, List.mem_map, not_exists, not_and]
  intro c _
  cases c <;> simp [shapeFact]

@[simp] theorem sub_mem_project (Δ : Bounds) (a b : Ty) :
    Constraint.sub a b ∈ project Δ ↔
      Constraint.sub a b ∈ Δ ∧ a.DefinedUnder Δ ∧ b.DefinedUnder Δ := by
  simp only [project, List.mem_append, sub_not_mem_shadow, or_false,
    ComparisonBalancedContext.sub_mem_prune]

theorem modeModels_project (Δ : Bounds) (η : ModVar → Mode) :
    ModeModels (project Δ) η ↔ ModeModels Δ η := by
  simp only [project, ModeModels, List.mem_append, or_imp, forall_and]
  change (ModeModels (ComparisonBalancedContext.prune Δ) η ∧ ModeModels (shapeShadow Δ) η) ↔
    ModeModels Δ η
  simp only [ComparisonBalancedContext.modeModels_prune, modeModels_shadow, and_self]

theorem shapeModels_shadow (Δ : Bounds) (ρ : TypeVar → ComparisonShape) :
    ComparisonShape.Models (shapeShadow Δ) ρ ↔ ComparisonShape.Models Δ ρ := by
  simp only [ComparisonShape.Models, pairs_shadow]

theorem shapeModels_project (Δ : Bounds) (ρ : TypeVar → ComparisonShape) :
    ComparisonShape.Models (project Δ) ρ ↔ ComparisonShape.Models Δ ρ := by
  simp only [project, ComparisonShape.Models, ComparisonShape.pairs,
    List.flatMap_append, List.mem_append, or_imp, forall_and]
  change (ComparisonShape.Models (ComparisonBalancedContext.prune Δ) ρ ∧
    ComparisonShape.Models (shapeShadow Δ) ρ) ↔ _
  exact ⟨fun h => (shapeModels_shadow Δ ρ).mp h.2,
    fun h => ⟨(ComparisonBalancedContext.unprune_hom Δ).shapes ρ h,
      (shapeModels_shadow Δ ρ).mpr h⟩⟩

theorem project_defined (Δ : Bounds) : (project Δ).TypeBoundsDefined :=
  fun a b h => ⟨fun η hη => ((sub_mem_project Δ a b).mp h).2.1 η
    ((modeModels_project Δ η).mp hη), fun η hη => ((sub_mem_project Δ a b).mp h).2.2 η
      ((modeModels_project Δ η).mp hη)⟩

theorem project_hom (Δ : Bounds) : ComparisonBalancedContext.Hom Δ (project Δ) where
  modes η := (modeModels_project Δ η).mp
  shapes ρ := (shapeModels_project Δ ρ).mp
  bounds a b h ha hb := .shaped (.bound ((sub_mem_project Δ a b).mpr
    ⟨h, (CompareTy.definedUnder_ofTy _ _).mp ha, (CompareTy.definedUnder_ofTy _ _).mp hb⟩))

theorem unproject_hom (Δ : Bounds) : ComparisonRawContext.Hom (project Δ) Δ where
  modes η := (modeModels_project Δ η).mpr
  shapes ρ := (shapeModels_project Δ ρ).mpr
  bounds a b h := .shaped (.bound ((sub_mem_project Δ a b).mp h).1)

theorem algebra_project_iff {Δ : Bounds} (hΔ : Balanced Δ)
    {a b : CompareTy} (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) :
    AlgebraSubtype (project Δ) a b ↔ AlgebraSubtype Δ a b :=
  ⟨(unproject_hom Δ).algebra, (project_hom Δ).algebra hΔ ha hb⟩

noncomputable def prepared (p : SchemePreparation.Prepared) : SchemePreparation.Prepared :=
  {p with assumptions := project p.assumptions}

/-- Keep every original shape equation, scalar guard, and shared witness;
no separate shape-preservation premise is needed. -/
theorem prepared_witness_iff (p : SchemePreparation.Prepared) (σ : CompareSubstitution)
    (hΔ : Balanced p.assumptions) :
    ComparisonPreparation.PreparedWitnessUnder (prepared p) σ ↔
      ComparisonPreparation.PreparedWitnessUnder p σ :=
  ⟨(unproject_hom p.assumptions).witness, (project_hom p.assumptions).witness hΔ⟩

end ModalityInference.ComparisonBalancedProjection
