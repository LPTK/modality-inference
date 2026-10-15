import ModalityInference.Proofs.ComparisonCapsuleFamilyReplacement
import ModalityInference.Proofs.ComparisonPreparedBounds

namespace ModalityInference.ComparisonCapsuleContext

open ComparisonCapsuleIntervals ComparisonBody ComparisonPreparation

/-- A finite witness for the derived public scheme retains the original type
images and adds one simultaneous suffix coordinate for each selected group. -/
def parameterAction (p : Prepared) (bs : List Binding) (original : CompareSubstitution)
    (suffix : Nat → ModExpr) : CompareSubstitution :=
  { types := (List.range' p.firstType (p.nextType - p.firstType)).map
      (fun n => (n, original.type (.flex n)))
    modes := (modeIds p bs).map (fun n =>
      (n, jointModes original.mode (bs.map Binding.fresh) suffix (.flex n))) }

theorem parameterAction_instantiates (p : Prepared) (bs : List Binding)
    (original : CompareSubstitution) (suffix : Nat → ModExpr) (extra : Bounds) :
    CompareInstantiates (ComparisonParameterization.source p (symbolic bs) (bs.map Binding.fresh) extra)
      (parameterAction p bs original suffix) := by
  simp [CompareInstantiates, ComparisonParameterization.source, parameterAction,
    List.map_map, Function.comp_def, modeIds]

theorem parameterAction_wellShaped {p : Prepared} {bs : List Binding}
    {original : CompareSubstitution} {suffix : Nat → ModExpr}
    (h : original.WellShaped p.assumptions) :
    (parameterAction p bs original suffix).WellShaped p.assumptions := by
  intro entry he
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp he
  exact h.type (.flex n)

theorem parameterAction_domainsAbove (p : Prepared) (bs : List Binding)
    (original : CompareSubstitution) (suffix : Nat → ModExpr)
    (horder : p.firstMode ≤ p.nextMode) (hfresh : ∀ b ∈ bs, p.nextMode ≤ b.fresh) :
    (parameterAction p bs original suffix).DomainsAbove p.firstType p.firstMode := by
  constructor
  · intro entry he
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp he
    obtain ⟨i, _, rfl⟩ := List.mem_range'.mp hn
    omega
  · intro entry he
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp he
    rcases List.mem_append.mp hn with hn | hn
    · obtain ⟨i, _, rfl⟩ := List.mem_range'.mp hn
      omega
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hn
      exact horder.trans (hfresh b hb)

theorem parameterAction_type {p : Prepared} {bs : List Binding}
    {original : CompareSubstitution} {suffix : Nat → ModExpr}
    (h : original.DomainsAbove p.firstType p.firstMode)
    (horder : p.firstMode ≤ p.nextMode) (hfresh : ∀ b ∈ bs, p.nextMode ≤ b.fresh)
    {v : TypeVar} (hv : v.index < p.nextType) :
    (parameterAction p bs original suffix).type v = original.type v := by
  by_cases ht : v.index < p.firstType
  · rw [(parameterAction_domainsAbove p bs original suffix horder hfresh).type_fixed v ht,
      h.type_fixed v ht]
  · cases v with
    | rigid n => rfl
    | flex n =>
      have hn : n ∈ List.range' p.firstType (p.nextType - p.firstType) := by
        apply List.mem_range'.mpr
        exact ⟨n - p.firstType, by simp only [TypeVar.index] at hv ht; omega, by simp only [TypeVar.index] at ht; omega⟩
      simp only [parameterAction, CompareSubstitution.type, List.lookup_graph _ hn, Option.getD_some]

theorem parameterAction_mode {p : Prepared} {bs : List Binding}
    {original : CompareSubstitution} {suffix : Nat → ModExpr}
    (h : original.DomainsAbove p.firstType p.firstMode)
    (horder : p.firstMode ≤ p.nextMode) (hfresh : ∀ b ∈ bs, p.nextMode ≤ b.fresh)
    {v : ModVar} (hv : v.index < p.nextMode) :
    (parameterAction p bs original suffix).mode v = original.mode v := by
  by_cases hm : v.index < p.firstMode
  · rw [(parameterAction_domainsAbove p bs original suffix horder hfresh).mode_fixed v hm,
      h.mode_fixed v hm]
  · cases v with
    | rigid n => rfl
    | flex n =>
      have hn : n ∈ modeIds p bs := by
        apply List.mem_append_left
        apply List.mem_range'.mpr
        exact ⟨n - p.firstMode, by simp only [ModVar.index] at hv hm; omega, by simp only [ModVar.index] at hm; omega⟩
      simp only [parameterAction, CompareSubstitution.mode, List.lookup_graph _ hn, Option.getD_some]
      apply jointModes_old
      intro k hk he
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hk
      have hl := hfresh b hb
      cases he
      simp only [ModVar.index] at hv
      omega

theorem parameterAction_fresh (p : Prepared) (bs : List Binding)
    (original : CompareSubstitution) (suffix : Nat → ModExpr) {b : Binding} (hb : b ∈ bs) :
    (parameterAction p bs original suffix).mode (.flex b.fresh) = suffix b.fresh := by
  have hmem : b.fresh ∈ bs.map Binding.fresh := List.mem_map.mpr ⟨b, hb, rfl⟩
  have hn : b.fresh ∈ modeIds p bs := List.mem_append_right _ hmem
  simp only [parameterAction, CompareSubstitution.mode, List.lookup_graph _ hn, Option.getD_some]
  exact jointModes_fresh _ _ _ hmem

/-- Every selected base is literal target syntax; peeling changes only its
outer annotation spine. -/
theorem binding_base_support {p : Prepared} {total : ModExpr → Bool} {b : Binding}
    (hb : b ∈ bindings p total) :
    b.base.typeVars ⊆ p.targetType.typeVars ∧ b.base.modVars ⊆ p.targetType.modVars := by
  have hp := binding_plan hb
  have hn := (plan_spec hp).2.2.2.1
  obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hn
  have hm := binding_request_mem_collect hb hr
  rw [← (plan_spec hp).2.2.2.2 r hr]
  constructor
  · change (peel total r.endpoint).base.typeVars ⊆ _
    rw [peel, ComparisonBody.peelFuel_typeVars]
    exact (collect_support p total hm).2.2.2
  · exact (ComparisonBody.peelFuel_modeSupport total _ r.endpoint
      (fun v hv => (collect_support p total hm).2.2.1 hv)).1

theorem parameterAction_base {p : Prepared} {bs : List Binding}
    {original : CompareSubstitution} {suffix : Nat → ModExpr}
    (horder : p.firstMode ≤ p.nextMode) (hfresh : ∀ b ∈ bs, p.nextMode ≤ b.fresh)
    (htarget : p.targetType.Bounded p.firstType p.firstMode)
    {total : ModExpr → Bool} (hbs : ∀ b ∈ bs, b ∈ bindings p total)
    {b : Binding} (hb : b ∈ bs) :
    (parameterAction p bs original suffix).ty b.base = .ofTy b.base := by
  have hd := parameterAction_domainsAbove p bs original suffix horder hfresh
  have hs := binding_base_support (hbs b hb)
  have ht := (TypeExpr.bounded_iff _ _ _).mp htarget
  have he := ComparisonAbsorption.instantiate_congr b.base
    (fun v hv => hd.type_fixed v (ht.1 v (hs.1 hv)))
    (fun v hv => hd.mode_fixed v (ht.2 v (hs.2 hv)))
  simpa only [ComparisonAbsorption.instantiate, CompareSubstitution.ty, CompareTy.subst_id] using he

/-- Interpret the symbolic selected images with one suffix assignment. All
unselected images are supplied by the same original type substitution. -/
theorem symbolic_type_factor (original after : CompareSubstitution)
    (bs : List Binding) (suffix : Nat → ModExpr)
    (hbase : ∀ b ∈ bs, after.ty b.base = .ofTy b.base)
    (hfresh : ∀ b ∈ bs, after.mode (.flex b.fresh) = suffix b.fresh)
    (v : TypeVar) (hv : after.type v = original.type v) :
    after.ty ((symbolic bs).type v) = (replaceImages original bs suffix).type v := by
  have himages : (bs.map (fun b => (b.name, b.image))).map (fun pair => (pair.1, after.ty pair.2)) =
      bs.map (fun b => (b.name, CompareTy.modal (.ofTy b.base) (suffix b.fresh))) := by
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro b hb
    dsimp only
    congr 1
    change CompareTy.modal (after.ty b.base) (after.mode (.flex b.fresh)) = _
    rw [hbase b hb, hfresh b hb]
  cases v with
  | rigid n => rfl
  | flex n =>
    simp only [replaceImages, CompareSubstitution.type, List.lookup_append]
    rw [← himages, lookup_map_values]
    simp only [symbolic, Substitution.type]
    cases he : (bs.map (fun b => (b.name, b.image))).lookup n with
    | none => simpa only [he, Option.map_none, Option.none_or, Option.getD_none,
        CompareSubstitution.ty, CompareTy.ofTy, CompareTy.subst] using hv
    | some a => rfl


theorem parameterAction_finish_type {p : Prepared} {bs : List Binding}
    {original : CompareSubstitution} {suffix : Nat → ModExpr}
    (h : original.DomainsAbove p.firstType p.firstMode)
    (horder : p.firstMode ≤ p.nextMode) (hfresh : ∀ b ∈ bs, p.nextMode ≤ b.fresh)
    (htarget : p.targetType.Bounded p.firstType p.firstMode)
    {total : ModExpr → Bool} (hbs : ∀ b ∈ bs, b ∈ bindings p total)
    {v : TypeVar} (hv : v.index < p.nextType) :
    (ComparisonExactContext.finish (symbolic bs) (parameterAction p bs original suffix)).type v =
      (replaceImages original bs suffix).type v := by
  rw [ComparisonExactContext.finish_type]
  exact symbolic_type_factor original _ bs suffix
    (fun _ hb => parameterAction_base horder hfresh htarget hbs hb)
    (fun _ hb => parameterAction_fresh p bs original suffix hb) v
    (parameterAction_type h horder hfresh hv)

theorem parameterAction_finish_mode {p : Prepared} {bs : List Binding}
    {original : CompareSubstitution} {suffix : Nat → ModExpr}
    (h : original.DomainsAbove p.firstType p.firstMode)
    (horder : p.firstMode ≤ p.nextMode) (hfresh : ∀ b ∈ bs, p.nextMode ≤ b.fresh)
    {v : ModVar} (hv : v.index < p.nextMode) :
    (ComparisonExactContext.finish (symbolic bs) (parameterAction p bs original suffix)).mode v =
      (replaceImages original bs suffix).mode v := by
  rw [ComparisonExactContext.finish_mode]
  have he : (symbolic bs).mode v = .var v := by cases v <;> rfl
  rw [he]
  change (parameterAction p bs original suffix).mode v = original.mode v
  exact parameterAction_mode h horder hfresh hv

/-- The very same extended finite action satisfies every fresh scalar goal.
Original source modes and suffix coordinates are instantiated simultaneously. -/
theorem parameterAction_goals {p : Prepared} {bs : List Binding}
    {original : CompareSubstitution} {suffix : Nat → ModExpr} {total : ModExpr → Bool}
    {Q : ModVar → Prop} (hdata : ∀ b ∈ bs, ReplacementData p total original Q b (suffix b.fresh))
    (h : original.DomainsAbove p.firstType p.firstMode)
    (horder : p.firstMode ≤ p.nextMode) (hfresh : ∀ b ∈ bs, p.nextMode ≤ b.fresh)
    (hsource : p.sourceType.Bounded p.nextType p.nextMode)
    (htarget : p.targetType.Bounded p.firstType p.firstMode)
    (hbs : ∀ b ∈ bs, b ∈ bindings p total) :
    AlgebraEntailsAll p.assumptions
      ((parameterAction p bs original suffix).bounds (goals total bs)) := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨b, hb, hd⟩ := List.mem_flatMap.mp hd
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hd
  have hmem := binding_request_mem_collect (hbs b hb) hr
  have hs := collect_support p total hmem
  have hsrc := (TypeExpr.bounded_iff _ _ _).mp hsource
  have htgt := (TypeExpr.bounded_iff _ _ _).mp htarget
  have hd := parameterAction_domainsAbove p bs original suffix horder hfresh
  have he : (r.suffix total).subst (parameterAction p bs original suffix).mode = r.suffix total := by
    rw [ModExpr.subst_congr _ (τ := ModExpr.var) (fun v hv =>
      hd.mode_fixed v (htgt.2 v (hs.2.2.1 (r.suffix_support total v hv))))]
    exact ModExpr.subst_id _
  have ha : r.action.subst (parameterAction p bs original suffix).mode =
      r.action.subst original.mode :=
    ModExpr.subst_congr _ (fun v hv => parameterAction_mode h horder hfresh (hsrc.2 v (hs.2.1 hv)))
  have hq := parameterAction_fresh p bs original suffix hb
  have hg := (hdata b hb).goals r hr
  simp only [Request.suffix] at he
  cases hp : r.isLower <;>
    simpa only [Binding.bounds, Request.bound, hp, Bool.false_eq_true, if_false, if_true,
      CompareSubstitution.constraint, ModExpr.subst, hq, he, ha,
      Request.mapAction, Request.suffix, AlgebraEntails, Entails] using hg

/-- The rebuilt witness factors through the exact symbolic public source.
Both original guarded bounds and all fresh scalar obligations use this action. -/
theorem parameterized_witness {p : Prepared} {bs : List Binding}
    {original : CompareSubstitution} {suffix : Nat → ModExpr} {total : ModExpr → Bool}
    {Q : ModVar → Prop} (hdata : ∀ b ∈ bs, ReplacementData p total original Q b (suffix b.fresh))
    (h : PreparedWitness p original)
    (hnew : PreparedWitness p (replaceImages original bs suffix))
    (horder : p.firstMode ≤ p.nextMode) (hfresh : ∀ b ∈ bs, p.nextMode ≤ b.fresh)
    (hsource : p.sourceType.Bounded p.nextType p.nextMode)
    (hbounds : p.sourceBounds.Bounded p.nextType p.nextMode)
    (htarget : p.targetType.Bounded p.firstType p.firstMode)
    (hbs : ∀ b ∈ bs, b ∈ bindings p total) :
    let derived := ComparisonParameterization.source p (symbolic bs) (bs.map Binding.fresh) (goals total bs)
    let after := parameterAction p bs original suffix
    CompareInstantiates derived after ∧ after.WellShaped p.assumptions ∧
      AlgebraEntailsAll p.assumptions (after.bounds derived.bounds) ∧
      AlgebraSubtype p.assumptions (after.ty derived.body) (.ofTy p.targetType) := by
  refine ⟨parameterAction_instantiates p bs original suffix _, parameterAction_wellShaped h.2.1, ?_, ?_⟩
  · change AlgebraEntailsAll p.assumptions
      ((parameterAction p bs original suffix).bounds ((symbolic bs).bounds p.sourceBounds ++ goals total bs))
    intro c hc
    simp only [CompareSubstitution.bounds, List.map_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · have hcongr := CompareSubstitution.algebra_bounds_congr (Δ := p.assumptions)
        (ComparisonExactContext.finish (symbolic bs) (parameterAction p bs original suffix))
        (replaceImages original bs suffix) p.sourceBounds
        (fun c hc v hv => parameterAction_finish_type h.1 horder hfresh htarget hbs
          (((Constraint.bounded_iff c _ _).mp (hbounds c hc)).1 v hv))
        (fun c hc v hv => parameterAction_finish_mode h.1 horder hfresh
          (((Constraint.bounded_iff c _ _).mp (hbounds c hc)).2 v hv))
      have hh := hcongr.mpr hnew.2.2.1
      rw [ComparisonExactContext.finish_bounds] at hh
      exact hh c hc
    · exact parameterAction_goals hdata h.1 horder hfresh hsource htarget hbs c hc
  · change AlgebraSubtype p.assumptions
      ((parameterAction p bs original suffix).ty ((symbolic bs).ty p.sourceType)) (.ofTy p.targetType)
    rw [← ComparisonExactContext.finish_ty]
    have hs := (TypeExpr.bounded_iff _ _ _).mp hsource
    rw [CompareSubstitution.ty_congr_on _ (replaceImages original bs suffix) p.sourceType
      (fun v hv => parameterAction_finish_type h.1 horder hfresh htarget hbs (hs.1 v hv))
      (fun v hv => parameterAction_finish_mode h.1 horder hfresh (hs.2 v hv))]
    exact hnew.2.2.2

/-- The finite factorization is an actual witness of the public derived scheme,
with its monomorphic target and complete written bounds. -/
theorem parameterized_subsumes (source target : Scheme) {bs : List Binding}
    {original : CompareSubstitution} {suffix : Nat → ModExpr} {total : ModExpr → Bool}
    {Q : ModVar → Prop}
    (hdata : ∀ b ∈ bs, ReplacementData (SchemePreparation.prepare [] source target)
      total original Q b (suffix b.fresh))
    (h : PreparedWitness (SchemePreparation.prepare [] source target) original)
    (hnew : PreparedWitness (SchemePreparation.prepare [] source target)
      (replaceImages original bs suffix))
    (hbs : ∀ b ∈ bs, b ∈ bindings (SchemePreparation.prepare [] source target) total) :
    let p := SchemePreparation.prepare [] source target
    AlgebraSubsumes []
      (ComparisonParameterization.source p (symbolic bs) (bs.map Binding.fresh) (goals total bs))
      (ComparisonParameterization.target p target) := by
  let p := SchemePreparation.prepare [] source target
  have hw := parameterized_witness hdata h hnew
    (by dsimp [SchemePreparation.prepare]; omega)
    (fun b hb => (mem_bindings (hbs b hb)).2)
    (SchemePreparation.prepare_sourceType_bounded [] source target)
    (SchemePreparation.prepare_sourceBounds_bounded [] source target)
    (SchemePreparation.prepare_targetType_bounded_first [] source target) hbs
  have ht : ({} : Substitution).type = TypeExpr.var := by funext v; cases v <;> rfl
  have hm : ({} : Substitution).mode = ModExpr.var := by funext v; cases v <;> rfl
  simp only [AlgebraSubsumes, ComparisonParameterization.target, Scheme.instantiate,
    Scheme.freshSubstitution, List.zipIdx_nil, List.map_nil, Substitution.empty_bounds,
    Substitution.ty, ht, hm, TypeExpr.subst_id, List.nil_append]
  exact ⟨parameterAction p bs original suffix, hw⟩

/-- Every atomic mixed group selected outside frozen source contexts admits
one joint public parameterization. The original guarded constraints and body
are retained in the resulting algebraic scheme comparison. -/
theorem unfrozen_parameterized_subsumes (source target : Scheme)
    {ρ : TypeVar → ComparisonShape}
    (hR : Residual (SchemePreparation.prepare [] source target).assumptions)
    (hρ : ComparisonShape.Models (SchemePreparation.prepare [] source target).assumptions ρ)
    {fuel : Nat} {known : List ModExpr}
    (hknown : knownTotal fuel (SchemePreparation.prepare [] source target).assumptions
      (ComparisonAnnotations.expressions (SchemePreparation.prepare [] source target).sourceType ++
        ComparisonAnnotations.expressions (SchemePreparation.prepare [] source target).targetType) = .success known)
    {original : CompareSubstitution}
    (h : PreparedWitness (SchemePreparation.prepare [] source target) original)
    (hi : ComparisonModeRestriction.Fixed (SchemePreparation.prepare [] source target).assumptions original.mode)
    {P : TypeVar → Prop} {Q : ModVar → Prop}
    (hsupport : ∀ b ∈ unfrozenBindings (SchemePreparation.prepare [] source target) (isTotal known),
      ComparisonInterpolation.Supports P Q (original.type (.flex b.name)))
    (hatomic : ∀ b ∈ unfrozenBindings (SchemePreparation.prepare [] source target) (isTotal known),
      ∀ r ∈ b.requests, ComparisonPartialCapsule.Atomic ((CompareTy.ofTy r.endpoint).shape.subst ρ)) :
    let p := SchemePreparation.prepare [] source target
    let bs := unfrozenBindings p (isTotal known)
    AlgebraSubsumes []
      (ComparisonParameterization.source p (symbolic bs) (bs.map Binding.fresh) (goals (isTotal known) bs))
      (ComparisonParameterization.target p target) := by
  obtain ⟨suffix, hdata, hnew⟩ := unfrozen_family_replacement
    (SchemePreparation.prepared_typeBoundsDefined source target) hR hρ hknown h hi hsupport hatomic
  apply parameterized_subsumes source target hdata h hnew
  intro b hb
  exact (List.mem_filter.mp (List.mem_filter.mp hb).1).1

end ModalityInference.ComparisonCapsuleContext
