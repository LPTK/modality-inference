import ModalityInference.ComparisonRawContext
import ModalityInference.Proofs.ComparisonRawModeTransport
import ModalityInference.Proofs.ComparisonDefinedPreparation

namespace ModalityInference.ComparisonRawContext

/-- A raw context maps to another by preserving scalar and shape models and
certifying its whole declared edges. No endpoint guard is added. -/
structure Hom (Δ Γ : Bounds) : Prop where
  modes : ∀ η, ModeModels Γ η → ModeModels Δ η
  shapes : ∀ ρ, ComparisonShape.Models Γ ρ → ComparisonShape.Models Δ ρ
  bounds : ∀ a b, Constraint.sub a b ∈ Δ → AlgebraSubtype Γ (.ofTy a) (.ofTy b)

theorem Hom.equivalent {Δ Γ} (h : Hom Δ Γ) {a b : ComparisonShape}
    (he : ComparisonShape.Equivalent Δ a b) : ComparisonShape.Equivalent Γ a b :=
  fun ρ hρ => he ρ (h.shapes ρ hρ)

theorem Hom.wellShaped {Δ Γ} (h : Hom Δ Γ) {a : CompareTy}
    (ha : a.WellShaped Δ) : a.WellShaped Γ := by
  induction a with
  | var | unit | credit => trivial
  | prod _ _ iha ihb | sum _ _ iha ihb | fn _ _ iha ihb => exact ⟨iha ha.1,ihb ha.2⟩
  | modal _ _ ih => exact ih ha
  | join _ _ iha ihb | meet _ _ iha ihb =>
    exact ⟨iha ha.1,ihb ha.2.1,h.equivalent ha.2.2⟩

theorem Hom.defined {Δ Γ} (h : Hom Δ Γ) {a : CompareTy}
    (ha : a.DefinedUnder Δ) : a.DefinedUnder Γ :=
  fun η hη => ha η (h.modes η hη)

theorem Hom.mode_defined {Δ Γ} (h : Hom Δ Γ) {m : ModExpr}
    (hm : Entails Δ (.defined m)) : Entails Γ (.defined m) :=
  fun η hη => hm η (h.modes η hη)

theorem Hom.submode {Δ Γ} (h : Hom Δ Γ) {m n : ModExpr}
    (hm : Submode Δ m n) : Submode Γ m n :=
  .valid fun η hη => hm.denote (h.modes η hη)

theorem Hom.compatible {Δ Γ} (h : Hom Δ Γ) {a b : CompareTy}
    (hc : ComparisonAlgebra.Compatible Δ a b) : ComparisonAlgebra.Compatible Γ a b :=
  ⟨h.wellShaped hc.1,h.defined hc.2.1,h.defined hc.2.2⟩

theorem Hom.equation {Δ Γ} (h : Hom Δ Γ) {a b : CompareTy}
    (he : ComparisonAlgebra.Equation Δ a b) : ComparisonAlgebra.Equation Γ a b := by
  cases he with
  | distrib p hab hac => exact .distrib p (h.compatible hab) (h.compatible hac)
  | modal p hab hm => exact .modal p (h.compatible hab) (h.mode_defined hm)
  | scalar p hs ha hm hn =>
    exact .scalar p (h.wellShaped hs) (h.defined ha) (h.mode_defined hm) (h.mode_defined hn)
  | prod p hac hbd => exact .prod p (h.compatible hac) (h.compatible hbd)
  | sum p hac hbd => exact .sum p (h.compatible hac) (h.compatible hbd)
  | fn p hac hbd => exact .fn p (h.compatible hac) (h.compatible hbd)

theorem Hom.shaped {Δ Γ} (h : Hom Δ Γ) {a b : CompareTy}
    (hab : ShapedSubtype Δ a b) : AlgebraSubtype Γ a b := by
  induction hab with
  | refl ha => exact .refl (h.wellShaped ha)
  | trans _ _ iha ihb => exact .trans iha ihb
  | bound hb => exact h.bounds _ _ hb
  | identity ha => exact .identity (h.wellShaped ha)
  | identityRev ha => exact .identityRev (h.wellShaped ha)
  | compose ha => exact .compose (h.wellShaped ha)
  | composeRev ha => exact .composeRev (h.wellShaped ha)
  | congr _ hm ih => exact .congr ih (h.submode hm)
  | prod _ _ iha ihb => exact .prod iha ihb
  | sum _ _ iha ihb => exact .sum iha ihb
  | fn _ _ hm iha ihb => exact .fn iha ihb (h.submode hm)
  | joinLeft hs => exact .shaped (.joinLeft (h.wellShaped hs))
  | joinRight hs => exact .shaped (.joinRight (h.wellShaped hs))
  | meetLeft hs => exact .shaped (.meetLeft (h.wellShaped hs))
  | meetRight hs => exact .shaped (.meetRight (h.wellShaped hs))
  | joinLeast _ _ iha ihb => exact .joinLeast iha ihb
  | meetGreatest _ _ iha ihb => exact .meetGreatest iha ihb

/-- Whole-edge transport is closed under every guarded algebraic rule. -/
theorem Hom.algebra {Δ Γ} (h : Hom Δ Γ) {a b : CompareTy}
    (hab : AlgebraSubtype Δ a b) : AlgebraSubtype Γ a b := by
  induction hab with
  | shaped hh => exact h.shaped hh
  | trans _ _ iha ihb => exact .trans iha ihb
  | equation he => exact .equation (h.equation he)
  | equationRev he => exact .equationRev (h.equation he)
  | congr _ hm ih => exact .congr ih (h.submode hm)
  | prod _ _ iha ihb => exact .prod iha ihb
  | sum _ _ iha ihb => exact .sum iha ihb
  | fn _ _ hm iha ihb => exact .fn iha ihb (h.submode hm)
  | joinLeast _ _ iha ihb => exact .joinLeast iha ihb
  | meetGreatest _ _ iha ihb => exact .meetGreatest iha ihb
  | clamp hab hat hm _ _ ihb iht =>
    exact .clamp (h.compatible hab) (h.compatible hat) (h.mode_defined hm) ihb iht
  | clampRev hab hat hm _ _ ihb iht =>
    exact .clampRev (h.compatible hab) (h.compatible hat) (h.mode_defined hm) ihb iht

theorem prune_subset (Δ : Bounds) : prune Δ ⊆ Δ := fun _ h => (List.mem_filter.mp h).1

@[simp] theorem modeModels_prune (Δ : Bounds) (η : ModVar → Mode) :
    ModeModels (prune Δ) η ↔ ModeModels Δ η := by
  constructor
  · intro h c hc
    by_cases hk : keep c = true
    · exact h c (List.mem_filter.mpr ⟨hc,hk⟩)
    · cases c <;> simp_all [keep,ModeSatisfies]
  · intro h c hc
    exact h c (prune_subset Δ hc)

@[simp] theorem shapeModels_prune (Δ : Bounds) (ρ : TypeVar → ComparisonShape) :
    ComparisonShape.Models (prune Δ) ρ ↔ ComparisonShape.Models Δ ρ := by
  constructor
  · intro h p hp
    obtain ⟨c,hc,hp⟩ := List.mem_flatMap.mp hp
    by_cases hk : keep c = true
    · exact h p (List.mem_flatMap.mpr ⟨c,List.mem_filter.mpr ⟨hc,hk⟩,hp⟩)
    · cases c with
      | sub a b | equiv a b =>
        have hab : a=b := by simpa only [keep,decide_eq_true_eq,not_not] using hk
        subst b
        simp only [List.mem_singleton] at hp
        subst p
        rfl
      | equal v a =>
        have ha : a=(TypeExpr.var v : Ty) := by simpa only [keep,decide_eq_true_eq,not_not] using hk
        subst a
        simp only [List.mem_singleton] at hp
        subst p
        rfl
      | mode | defined => simp [keep] at hk
  · intro h p hp
    obtain ⟨c,hc,hp⟩ := List.mem_flatMap.mp hp
    exact h p (List.mem_flatMap.mpr ⟨c,prune_subset Δ hc,hp⟩)

/-- Reflexive type edges need no definedness guard and add no scalar or shape
information. Removing them preserves the raw comparison context. -/
theorem prune_hom (Δ : Bounds) : Hom Δ (prune Δ) where
  modes η := (modeModels_prune Δ η).mp
  shapes ρ := (shapeModels_prune Δ ρ).mp
  bounds a b hb := by
    by_cases hab : a=b
    · subst b; exact .refl (CompareTy.wellShaped_ofTy _ _)
    · exact .shaped (.bound (List.mem_filter.mpr ⟨hb,by simpa only [keep,decide_eq_true_eq]⟩))

theorem unprune_hom (Δ : Bounds) : Hom (prune Δ) Δ where
  modes η := (modeModels_prune Δ η).mpr
  shapes ρ := (shapeModels_prune Δ ρ).mpr
  bounds _ _ hb := .shaped (.bound (prune_subset Δ hb))

@[simp] theorem algebra_prune_iff (Δ : Bounds) (a b : CompareTy) :
    AlgebraSubtype (prune Δ) a b ↔ AlgebraSubtype Δ a b :=
  ⟨(unprune_hom Δ).algebra,(prune_hom Δ).algebra⟩


theorem Hom.entails {Δ Γ} (h : Hom Δ Γ) {c : CompareConstraint}
    (hc : AlgebraEntails Δ c) : AlgebraEntails Γ c := by
  cases c with
  | sub a b => exact ⟨h.algebra hc.1,h.defined hc.2.1,h.defined hc.2.2⟩
  | mode m n => exact h.submode hc
  | defined m => exact h.mode_defined hc
  | equal v a => exact ⟨h.algebra hc.1,h.algebra hc.2.1,h.defined hc.2.2⟩
  | equiv a b => exact ⟨h.algebra hc.1,h.algebra hc.2.1,h.defined hc.2.2.1,h.defined hc.2.2.2⟩

theorem Hom.witness {p : SchemePreparation.Prepared} {Γ : Bounds}
    (h : Hom p.assumptions Γ) {σ : CompareSubstitution}
    (hw : ComparisonPreparation.PreparedWitnessUnder p σ) :
    ComparisonPreparation.PreparedWitnessUnder {p with assumptions:=Γ} σ := by
  obtain ⟨⟨hd,hs,hb,ht⟩,hi,hbody⟩ := hw
  refine ⟨⟨hd,fun entry he => h.wellShaped (hs entry he),
    fun c hc => h.entails (hb c hc),h.algebra ht⟩,
    hi.of_models h.modes,h.defined hbody⟩

/-- Context normalization leaves the entire shared witness, fresh domains,
source obligations, and target body unchanged. -/
def prepared (p : SchemePreparation.Prepared) : SchemePreparation.Prepared :=
  {p with assumptions:=prune p.assumptions}

@[simp] theorem prepared_witness_iff (p : SchemePreparation.Prepared) (σ : CompareSubstitution) :
    ComparisonPreparation.PreparedWitnessUnder (prepared p) σ ↔
      ComparisonPreparation.PreparedWitnessUnder p σ := by
  constructor
  · intro h
    simpa only [prepared] using (unprune_hom p.assumptions).witness (p := prepared p) h
  · intro h
    exact (prune_hom p.assumptions).witness h

@[simp] theorem prune_append (Δ Γ : Bounds) : prune (Δ++Γ)=prune Δ++prune Γ :=
  List.filter_append _ _

@[simp] theorem prune_sub_refl (a : Ty) : prune [Constraint.sub a a]=[] := by
  simp [prune,keep]

@[simp] theorem prune_equiv_refl (a : Ty) : prune [Constraint.equiv a a]=[] := by
  simp [prune,keep]

@[simp] theorem prune_equal_refl (v : TypeVar) : prune [Constraint.equal v (.var v)]=[] := by
  simp [prune,keep]

end ModalityInference.ComparisonRawContext
