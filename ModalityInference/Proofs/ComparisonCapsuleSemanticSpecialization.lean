import ModalityInference.Proofs.ComparisonCapsuleFrozenBody
import ModalityInference.Proofs.ComparisonContextSpecialization
import ModalityInference.Proofs.ComparisonCapsuleLocalActions
import ModalityInference.Proofs.ComparisonExactMatchingCoverage
import ModalityInference.Proofs.ComparisonCapsuleSemanticParameterization

namespace ModalityInference.ComparisonCapsuleContext

open ComparisonPartialCarrier ComparisonInstance ComparisonPreparation
open ComparisonCapsuleIntervals ComparisonBody ComparisonInterpolation ComparisonPartialCapsule

/-- Frozen names after substitution come either from an inserted image or
from an original name enclosed by a partial substituted annotation. -/
theorem frozenTypeSupport_subst_mem (total : ModExpr → Bool)
    (types : TypeVar → Ty) (modes : ModVar → ModExpr) (body : Ty) (v : TypeVar)
    (hv : v ∈ frozenTypeSupport total (body.subst types modes)) :
    (∃ w ∈ body.typeVars, v ∈ frozenTypeSupport total (types w)) ∨
      (∃ w ∈ frozenTypeSupport (fun m => total (m.subst modes)) body,
        v ∈ (types w).typeVars) := by
  induction body with
  | var w => exact Or.inl ⟨w, Finset.mem_singleton_self _, hv⟩
  | unit | credit => simp [TypeExpr.subst, frozenTypeSupport] at hv
  | prod a b ia ib | sum a b ia ib | fn a b ia ib =>
    simp only [TypeExpr.subst, frozenTypeSupport, Finset.mem_union] at hv
    rcases hv with hv | hv
    · rcases ia hv with ⟨w, hw, hv⟩ | ⟨w, hw, hv⟩
      · exact Or.inl ⟨w, Finset.mem_union_left _ hw, hv⟩
      · exact Or.inr ⟨w, Finset.mem_union_left _ hw, hv⟩
    · rcases ib hv with ⟨w, hw, hv⟩ | ⟨w, hw, hv⟩
      · exact Or.inl ⟨w, Finset.mem_union_right _ hw, hv⟩
      · exact Or.inr ⟨w, Finset.mem_union_right _ hw, hv⟩
  | modal a m ia =>
    simp only [TypeExpr.subst, frozenTypeSupport] at hv ⊢
    split at hv
    · next hm =>
      simp only [hm, if_true]
      exact ia hv
    · next hm =>
      simp only [hm]
      exact Or.inr ((TypeExpr.mem_typeVars_subst _ _ _ _).mp hv)

private theorem lookup_entry {α : Type} {entries : List (Nat × α)} {n : Nat} {a : α}
    (h : entries.lookup n = some a) : (n, a) ∈ entries := by
  obtain ⟨left, right, he, _⟩ := List.lookup_eq_some_iff.mp h
  rw [he]
  exact List.mem_append_right _ List.mem_cons_self

/-- A scoped literal image never introduces a fresh frozen type key. -/
theorem scoped_image_frozen_fixed {p : Prepared} {before : Substitution}
    (hs : ComparisonExactContext.Scoped p before) (total : ModExpr → Bool)
    (v : TypeVar) :
    ∀ w ∈ frozenTypeSupport total (before.type v), typeAllowed p w = false := by
  cases v with
  | rigid n => simp [Substitution.type, frozenTypeSupport]
  | flex n =>
    cases he : before.types.lookup n with
    | none => simp [Substitution.type, he, frozenTypeSupport]
    | some image =>
      intro w hw
      have hh := (hs.1 n image (lookup_entry he)).2.1
      apply hh w
      exact frozenTypes_subset total image (by simpa only [Substitution.type, he, Option.getD_some] using hw)

/-- Selected literal type images contain only fixed names. Unselected fixed
keys remain fixed as well. -/
theorem scoped_image_fixed_of_covered {p : Prepared} {before : Substitution}
    (hs : ComparisonExactContext.Scoped p before) (v : TypeVar)
    (hc : typeAllowed p v = true → v.index ∈ before.types.map Prod.fst) :
    ∀ w ∈ (before.type v).typeVars, typeAllowed p w = false := by
  cases v with
  | rigid n =>
    intro w hw
    have hw : w = .rigid n := Finset.mem_singleton.mp hw
    subst w
    rfl
  | flex n =>
    cases he : before.types.lookup n with
    | none =>
      have hn : typeAllowed p (.flex n) = false := by
        apply Bool.eq_false_iff.mpr
        intro ha
        have hm := hc ha
        obtain ⟨entry, hm, hn⟩ := List.mem_map.mp hm
        have hne := List.lookup_eq_none_iff.mp he entry hm
        simp [hn, TypeVar.index] at hne
      intro w hw
      have hw : w = .flex n := by simpa only [Substitution.type, he, Option.getD_none,
        TypeExpr.typeVars, Finset.mem_singleton] using hw
      exact hw ▸ hn
    | some image =>
      intro w hw
      exact (hs.1 n image (lookup_entry he)).2.1 w
        (by simpa only [Substitution.type, he, Option.getD_some] using hw)


private theorem modality_subst_support (Q : ModVar → Prop) (images : ModVar → ModExpr)
    (m : ModExpr) (h : ∀ v ∈ m.vars, ∀ w ∈ (images v).vars, Q w) :
    ∀ w ∈ (m.subst images).vars, Q w := by
  induction m with
  | var v => exact h v (Finset.mem_singleton_self _)
  | const mode => simp [ModExpr.subst, ModExpr.vars]
  | compose a b ia ib | meet a b ia ib | join a b ia ib
  | leftResidual a b ia ib | rightResidual a b ia ib =>
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact ia (fun v hv => h v (Finset.mem_union_left _ hv)) w hw
    · exact ib (fun v hv => h v (Finset.mem_union_right _ hv)) w hw
  | close a ia | closeInv a ia | future a ia | capture a ia => exact ia h

private theorem type_subst_mode_support (Q : ModVar → Prop)
    (types : TypeVar → Ty) (modes : ModVar → ModExpr) (body : Ty)
    (ht : ∀ v ∈ body.typeVars, ∀ w ∈ (types v).modVars, Q w)
    (hm : ∀ v ∈ body.modVars, ∀ w ∈ (modes v).vars, Q w) :
    ∀ w ∈ (body.subst types modes).modVars, Q w := by
  induction body with
  | var v => exact ht v (Finset.mem_singleton_self _)
  | unit | credit => simp [TypeExpr.subst, TypeExpr.modVars]
  | prod a b ia ib | sum a b ia ib | fn a b ia ib =>
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact ia (fun v hv => ht v (Finset.mem_union_left _ hv))
        (fun v hv => hm v (Finset.mem_union_left _ hv)) w hw
    · exact ib (fun v hv => ht v (Finset.mem_union_right _ hv))
        (fun v hv => hm v (Finset.mem_union_right _ hv)) w hw
  | modal a m ia =>
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact ia ht (fun v hv => hm v (Finset.mem_union_left _ hv)) w hw
    · exact modality_subst_support Q modes m (fun v hv => hm v (Finset.mem_union_right _ hv)) w hw

theorem annotation_mode_support (body : Ty) {m : ModExpr}
    (hm : m ∈ ComparisonAnnotations.expressions body) : m.vars ⊆ body.modVars := by
  induction body with
  | var | unit | credit => simp [ComparisonAnnotations.expressions] at hm
  | prod a b ia ib | sum a b ia ib | fn a b ia ib =>
    rcases List.mem_append.mp hm with hm | hm
    · exact (ia hm).trans Finset.subset_union_left
    · exact (ib hm).trans Finset.subset_union_right
  | modal a n ia =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact Finset.subset_union_right
    · exact (ia hm).trans Finset.subset_union_left

theorem scoped_type_image_modes_fixed {p : Prepared} {before : Substitution}
    (hs : ComparisonExactContext.Scoped p before) (v : TypeVar) :
    ∀ w ∈ (before.type v).modVars, modeAllowed p w = false := by
  cases v with
  | rigid n => simp [Substitution.type, TypeExpr.modVars]
  | flex n =>
    cases he : before.types.lookup n with
    | none => simp [Substitution.type, he, TypeExpr.modVars]
    | some image =>
      intro w hw
      exact (hs.1 n image (lookup_entry he)).2.2 w
        (by simpa only [Substitution.type, he, Option.getD_some] using hw)

theorem scoped_mode_image_fixed_of_covered {p : Prepared} {before : Substitution}
    (hs : ComparisonExactContext.Scoped p before) (v : ModVar)
    (hc : modeAllowed p v = true → v.index ∈ before.modes.map Prod.fst) :
    ∀ w ∈ (before.mode v).vars, modeAllowed p w = false := by
  cases v with
  | rigid n =>
    intro w hw
    have hw : w = .rigid n := Finset.mem_singleton.mp hw
    subst w
    rfl
  | flex n =>
    cases he : before.modes.lookup n with
    | none =>
      have hn : modeAllowed p (.flex n) = false := by
        apply Bool.eq_false_iff.mpr
        intro ha
        obtain ⟨entry, hm, hn⟩ := List.mem_map.mp (hc ha)
        have hne := List.lookup_eq_none_iff.mp he entry hm
        simp [hn, ModVar.index] at hne
      intro w hw
      have hw : w = .flex n := by simpa only [Substitution.mode, he, Option.getD_none,
        ModExpr.vars, Finset.mem_singleton] using hw
      exact hw ▸ hn
    | some image =>
      intro w hw
      exact (hs.2 n image (lookup_entry he)).2 w
        (by simpa only [Substitution.mode, he, Option.getD_some] using hw)

/-- Covering the source mode keys makes every residual source annotation
literal syntax over fixed names, even if some of those expressions are partial. -/
theorem specialized_annotations_fixed {p : Prepared} {before : Substitution}
    {σ : CompareSubstitution}
    (hs : ComparisonExactContext.Scoped p before)
    (hm : ∀ v, modeAllowed p v = false → σ.mode v = .var v)
    (hc : ∀ v ∈ p.sourceType.modVars,
      modeAllowed p v = true → v.index ∈ before.modes.map Prod.fst) :
    ∀ m ∈ ComparisonAnnotations.expressions (before.ty p.sourceType), m.subst σ.mode = m := by
  have hf : ∀ w ∈ (before.ty p.sourceType).modVars, modeAllowed p w = false :=
    type_subst_mode_support _ before.type before.mode p.sourceType
      (fun v _ => scoped_type_image_modes_fixed hs v)
      (fun v hv => scoped_mode_image_fixed_of_covered hs v (hc v hv))
  intro m he
  have he := ModExpr.subst_congr m (fun v hv => hm v (hf v (annotation_mode_support _ he hv)))
  simpa only [ModExpr.subst_id] using he

noncomputable section
open Classical

/-- Once exact specialization covers the semantic frozen keys, the rewritten
source contains no mutable key below a partial instantiated annotation. -/
theorem specialized_semantic_frozen_fixed {p : Prepared} {before : Substitution}
    {σ : CompareSubstitution}
    (hs : ComparisonExactContext.Scoped p before)
    (ha : AgreesWith before σ.type σ.mode)
    (hm : ∀ v, modeAllowed p v = false → σ.mode v = .var v)
    (hc : ∀ v ∈ frozenTypeSupport (fun m => decide (Entails p.assumptions
      (.defined (m.subst σ.mode)))) p.sourceType,
      typeAllowed p v = true → v.index ∈ before.types.map Prod.fst) :
    ∀ v ∈ frozenTypeSupport (fun m => decide (Entails p.assumptions
      (.defined (m.subst σ.mode)))) (before.ty p.sourceType), typeAllowed p v = false := by
  intro v hv
  have he (m : ModExpr) : (m.subst before.mode).subst σ.mode = m.subst σ.mode := by
    rw [← ComparisonExactContext.finish_modality]
    exact ModExpr.subst_congr m (fun v _ => ha.finish_mode hs hm v)
  rcases frozenTypeSupport_subst_mem _ before.type before.mode p.sourceType v hv with
    ⟨w, _, hw⟩ | ⟨w, hw, hv⟩
  · exact scoped_image_frozen_fixed hs _ w v hw
  · have hw' : w ∈ frozenTypeSupport (fun m => decide (Entails p.assumptions
        (.defined (m.subst σ.mode)))) p.sourceType := by
      simpa only [he] using hw
    exact scoped_image_fixed_of_covered hs w (hc w hw') v hv


/-- Every actual interval emitted after the literal specialization lies
outside the semantic frozen mask, without inspecting its chosen suffix. -/
theorem rewritten_binding_semantically_unfrozen {p : Prepared} {before : Substitution}
    {σ : CompareSubstitution}
    (hs : ComparisonExactContext.Scoped p before)
    (ha : AgreesWith before σ.type σ.mode)
    (hm : ∀ v, modeAllowed p v = false → σ.mode v = .var v)
    (hc : ∀ v ∈ frozenTypeSupport (fun m => decide (Entails p.assumptions
      (.defined (m.subst σ.mode)))) p.sourceType,
      typeAllowed p v = true → v.index ∈ before.types.map Prod.fst)
    {total : ModExpr → Bool} {b : ComparisonCapsuleIntervals.Binding}
    (hb : b ∈ bindings (ComparisonExactContext.rewrite p before) total) :
    TypeVar.flex b.name ∉ frozenTypeSupport (fun m => decide (Entails p.assumptions
      (.defined (m.subst σ.mode)))) (before.ty p.sourceType) := by
  intro hf
  have hal := (mem_bindings hb).1
  have hfixed := specialized_semantic_frozen_fixed hs ha hm hc _ hf
  exact Bool.noConfusion (hal.symm.trans hfixed)


/-- On specialized source annotations, the executable totality test is exactly
the semantic classifier used by the witness normal form. -/
theorem known_frozenTypeSupport_eq_semantic {p : Prepared} {σ : CompareSubstitution}
    {fuel : Nat} {known : List ModExpr}
    (hknown : ComparisonBody.knownTotal fuel p.assumptions
      (ComparisonAnnotations.expressions p.sourceType ++
        ComparisonAnnotations.expressions p.targetType) = .success known)
    (hf : ∀ m ∈ ComparisonAnnotations.expressions p.sourceType, m.subst σ.mode = m) :
    frozenTypeSupport (ComparisonBody.isTotal known) p.sourceType =
      frozenTypeSupport (fun m => decide (Entails p.assumptions (.defined (m.subst σ.mode))))
        p.sourceType := by
  apply frozenTypeSupport_congr
  intro m hm
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, hf m hm]
  exact ⟨ComparisonBody.isTotal_defined (ComparisonBody.knownTotal_sound hknown),
    ComparisonBody.knownTotal_isTotal_complete hknown m (fun r hr =>
      List.mem_flatMap.mpr ⟨m, List.mem_append_left _ hm, hr⟩)⟩

/-- Once frozen operands and source scalar syntax have been specialized, the
actual executable selector retains every mixed interval of the rewritten body. -/
theorem rewritten_selector_exact {p : Prepared} {before : Substitution}
    {σ : CompareSubstitution}
    (hs : ComparisonExactContext.Scoped p before)
    (ha : AgreesWith before σ.type σ.mode)
    (hm : ∀ v, modeAllowed p v = false → σ.mode v = .var v)
    (hc : ∀ v ∈ frozenTypeSupport (fun m => decide (Entails p.assumptions
      (.defined (m.subst σ.mode)))) p.sourceType,
      typeAllowed p v = true → v.index ∈ before.types.map Prod.fst)
    {fuel : Nat} {known : List ModExpr}
    (hknown : ComparisonBody.knownTotal fuel p.assumptions
      (ComparisonAnnotations.expressions (before.ty p.sourceType) ++
        ComparisonAnnotations.expressions p.targetType) = .success known)
    (hf : ∀ m ∈ ComparisonAnnotations.expressions (before.ty p.sourceType), m.subst σ.mode = m) :
    unfrozenBindings (ComparisonExactContext.rewrite p before) (ComparisonBody.isTotal known) =
      mixedBindings (ComparisonExactContext.rewrite p before) (ComparisonBody.isTotal known) := by
  apply List.filter_eq_self.mpr
  intro b hb
  apply decide_eq_true
  rw [known_frozenTypeSupport_eq_semantic (p := ComparisonExactContext.rewrite p before) hknown hf]
  exact rewritten_binding_semantically_unfrozen hs ha hm hc (List.mem_filter.mp hb).1


/-- Coverage of the whole frozen operands supplies the exact key invariant
needed after shared literal matching. Function child resets do not lose keys. -/
theorem matched_semantic_frozen_keys {p : Prepared} {σ : CompareSubstitution}
    {requests : List (Ty × Ty)} {before : Substitution}
    (hmatched : ∀ request ∈ requests, MatchingCovers p request.1 before)
    (hcover : ∀ a ∈ semanticFrozenOperands p.assumptions σ.mode p.sourceType,
      ∃ request ∈ requests, a.typeVars ⊆ request.1.typeVars) :
    ∀ v ∈ frozenTypeSupport (fun m => decide (Entails p.assumptions
      (.defined (m.subst σ.mode)))) p.sourceType,
      typeAllowed p v = true → v.index ∈ before.types.map Prod.fst := by
  intro v hv ha
  obtain ⟨a, ha', hv⟩ := (semanticFrozenOperands_type_support _ _ _ _).mp hv
  obtain ⟨request, hr, hs⟩ := hcover a ha'
  cases v with
  | rigid n => contradiction
  | flex n => exact (hmatched request hr).types n (hs hv) ha

/-- The actual successful matching fold removes all mutable frozen keys from
the specialized body, using the original shared type and modality witness. -/
theorem matchTypes_semantic_frozen_fixed {p : Prepared} {σ : CompareSubstitution}
    (requests : List (Ty × Ty)) {initial before : Substitution}
    (hmatch : requests.foldlM (fun action request => matchType p request.1 request.2 action) initial = some before)
    (hs : ComparisonExactContext.Scoped p before)
    (ha : AgreesWith before σ.type σ.mode)
    (hm : ∀ v, modeAllowed p v = false → σ.mode v = .var v)
    (hcover : ∀ a ∈ semanticFrozenOperands p.assumptions σ.mode p.sourceType,
      ∃ request ∈ requests, a.typeVars ⊆ request.1.typeVars) :
    ∀ v ∈ frozenTypeSupport (fun m => decide (Entails p.assumptions
      (.defined (m.subst σ.mode)))) (before.ty p.sourceType), typeAllowed p v = false := by
  apply specialized_semantic_frozen_fixed hs ha hm
  exact matched_semantic_frozen_keys (matchTypes_extends_covers hmatch).2 hcover


/-- Exact coverage of frozen type keys and source mode keys is sufficient for
agreement of the executable selector with the complete mixed interval family. -/
theorem rewritten_selector_exact_of_covered {p : Prepared} {before : Substitution}
    {σ : CompareSubstitution}
    (hs : ComparisonExactContext.Scoped p before)
    (ha : AgreesWith before σ.type σ.mode)
    (hm : ∀ v, modeAllowed p v = false → σ.mode v = .var v)
    (htc : ∀ v ∈ frozenTypeSupport (fun m => decide (Entails p.assumptions
      (.defined (m.subst σ.mode)))) p.sourceType,
      typeAllowed p v = true → v.index ∈ before.types.map Prod.fst)
    (hmc : ∀ v ∈ p.sourceType.modVars,
      modeAllowed p v = true → v.index ∈ before.modes.map Prod.fst)
    {fuel : Nat} {known : List ModExpr}
    (hknown : ComparisonBody.knownTotal fuel p.assumptions
      (ComparisonAnnotations.expressions (before.ty p.sourceType) ++
        ComparisonAnnotations.expressions p.targetType) = .success known) :
    unfrozenBindings (ComparisonExactContext.rewrite p before) (ComparisonBody.isTotal known) =
      mixedBindings (ComparisonExactContext.rewrite p before) (ComparisonBody.isTotal known) :=
  rewritten_selector_exact hs ha hm htc hknown (specialized_annotations_fixed hs hm hmc)


/-- Actual selected groups after exact specialization share one suffix family
and preserve the complete original witness, including its guarded bounds. -/
theorem specialized_family_replacement {p : Prepared} {ρ : TypeVar → ComparisonShape}
    {before : Substitution} {σ : CompareSubstitution}
    (hΔ : p.assumptions.TypeBoundsDefined) (hR : Residual p.assumptions)
    (hρ : ComparisonShape.Models p.assumptions ρ)
    (h : PreparedWitness p σ)
    (hs : ComparisonExactContext.Scoped p before)
    (ha : AgreesWith before σ.type σ.mode)
    (ht : ∀ v, typeAllowed p v = false → σ.type v = .var v)
    (hm : ∀ v, modeAllowed p v = false → σ.mode v = .var v)
    (hc : ∀ v ∈ frozenTypeSupport (fun m => decide (Entails p.assumptions
      (.defined (m.subst σ.mode)))) p.sourceType,
      typeAllowed p v = true → v.index ∈ before.types.map Prod.fst)
    {fuel : Nat} {known : List ModExpr}
    (hknown : knownTotal fuel p.assumptions
      (ComparisonAnnotations.expressions (before.ty p.sourceType) ++
        ComparisonAnnotations.expressions p.targetType) = .success known)
    {P : TypeVar → Prop} {Q : ModVar → Prop}
    (hsupport : ∀ b ∈ unfrozenBindings (ComparisonExactContext.rewrite p before) (isTotal known),
      Supports P Q (σ.type (.flex b.name)))
    (hatomic : ∀ b ∈ unfrozenBindings (ComparisonExactContext.rewrite p before) (isTotal known),
      ∀ r ∈ b.requests, Atomic ((CompareTy.ofTy r.endpoint).shape.subst ρ)) :
    let input := ComparisonExactContext.rewrite p before
    let bs := unfrozenBindings input (isTotal known)
    ∃ suffix : Nat → ModExpr,
      (∀ b ∈ bs, ReplacementData input (isTotal known) σ Q b (suffix b.fresh)) ∧
      PreparedWitness input (replaceImages σ bs suffix) := by
  have hw : PreparedWitness (ComparisonExactContext.rewrite p before) σ :=
    ⟨h.1, h.2.1, (ha.rewrite_bounds hs ht hm _ _).mpr h.2.2.1,
      (ha.rewrite_ty hs ht hm p.sourceType).symm ▸ h.2.2.2⟩
  apply family_replacement_semantic (p := ComparisonExactContext.rewrite p before)
    hΔ hR hρ hknown hw _ List.filter_sublist _ hsupport hatomic
  intro b hb
  exact rewritten_binding_semantically_unfrozen hs ha hm hc
    (List.mem_filter.mp (List.mem_filter.mp hb).1).1

/-- The exact specialization and actual capsule selector factor through one
public derived source, with simultaneous original mode and suffix assignments. -/
theorem specialized_parameterized_witness {p : Prepared} {ρ : TypeVar → ComparisonShape}
    {before : Substitution} {σ : CompareSubstitution}
    (hΔ : p.assumptions.TypeBoundsDefined) (hR : Residual p.assumptions)
    (hρ : ComparisonShape.Models p.assumptions ρ)
    (h : PreparedWitness p σ)
    (hs : ComparisonExactContext.Scoped p before)
    (ha : AgreesWith before σ.type σ.mode)
    (ht : ∀ v, typeAllowed p v = false → σ.type v = .var v)
    (hm : ∀ v, modeAllowed p v = false → σ.mode v = .var v)
    (hc : ∀ v ∈ frozenTypeSupport (fun m => decide (Entails p.assumptions
      (.defined (m.subst σ.mode)))) p.sourceType,
      typeAllowed p v = true → v.index ∈ before.types.map Prod.fst)
    (horder : p.firstMode ≤ p.nextMode)
    (hsource : p.sourceType.Bounded p.nextType p.nextMode)
    (hbounds : p.sourceBounds.Bounded p.nextType p.nextMode)
    (htarget : p.targetType.Bounded p.firstType p.firstMode)
    (hbefore : before.Bounded p.nextType p.nextMode)
    {fuel : Nat} {known : List ModExpr}
    (hknown : knownTotal fuel p.assumptions
      (ComparisonAnnotations.expressions (before.ty p.sourceType) ++
        ComparisonAnnotations.expressions p.targetType) = .success known)
    {P : TypeVar → Prop} {Q : ModVar → Prop}
    (hsupport : ∀ b ∈ unfrozenBindings (ComparisonExactContext.rewrite p before) (isTotal known),
      Supports P Q (σ.type (.flex b.name)))
    (hatomic : ∀ b ∈ unfrozenBindings (ComparisonExactContext.rewrite p before) (isTotal known),
      ∀ r ∈ b.requests, Atomic ((CompareTy.ofTy r.endpoint).shape.subst ρ)) :
    let input := ComparisonExactContext.rewrite p before
    let bs := unfrozenBindings input (isTotal known)
    let derived := ComparisonParameterization.source input (symbolic bs) (bs.map Binding.fresh)
      (goals (isTotal known) bs)
    ∃ after : CompareSubstitution,
      CompareInstantiates derived after ∧ after.WellShaped p.assumptions ∧
        AlgebraEntailsAll p.assumptions (after.bounds derived.bounds) ∧
        AlgebraSubtype p.assumptions (after.ty derived.body) (.ofTy p.targetType) := by
  let input := ComparisonExactContext.rewrite p before
  let bs := unfrozenBindings input (isTotal known)
  have hw : PreparedWitness input σ :=
    ⟨h.1, h.2.1, (ha.rewrite_bounds hs ht hm _ _).mpr h.2.2.1,
      (ha.rewrite_ty hs ht hm p.sourceType).symm ▸ h.2.2.2⟩
  obtain ⟨suffix, hdata, hnew⟩ := specialized_family_replacement
    hΔ hR hρ h hs ha ht hm hc hknown hsupport hatomic
  have hbs : ∀ b ∈ bs, b ∈ bindings input (isTotal known) :=
    fun b hb => (List.mem_filter.mp (List.mem_filter.mp hb).1).1
  exact ⟨parameterAction input bs σ suffix, parameterized_witness hdata hw hnew horder
    (fun b hb => (mem_bindings (hbs b hb)).2) (hbefore.ty hsource)
    (hbefore.bounds hbounds) htarget hbs⟩

end

end ModalityInference.ComparisonCapsuleContext
