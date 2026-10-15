import ModalityInference.Proofs.ComparisonWitnessRestriction
import ModalityInference.Proofs.ComparisonDefinedTemplateWitness
import ModalityInference.Proofs.ComparisonSkeletonLeafCoordinates
import ModalityInference.Proofs.ComparisonDefinedReductionSetup
import ModalityInference.Proofs.ComparisonPropagationModes

/-! Fresh comparison coordinates can be removed from every image of one shared
witness. The projection retains declared guards and materializes source-mode
lookups before restricting their images. -/
namespace ModalityInference.ComparisonFixedModeWitness

open ComparisonModeRestriction ComparisonPreparation

/-- Names belonging to the fixed input namespace. -/
def names (cutoff : Nat) : Finset ModVar :=
  (Finset.range cutoff).image ModVar.flex ∪ (Finset.range cutoff).image ModVar.rigid

@[simp] theorem mem_names (v : ModVar) (cutoff : Nat) : v ∈ names cutoff ↔ v.index < cutoff := by
  cases v <;> simp [names, ModVar.index]

def inputModes (bounds : Bounds) (body : Ty) : Finset ModVar := bounds.modVars ∪ body.modVars

noncomputable def keys (cutoff : Nat) (bounds : Bounds) (body : Ty) : List Nat :=
  (inputModes bounds body).toList.filterMap fun v => match v with
    | .flex n => if cutoff ≤ n then some n else none
    | .rigid _ => none

@[simp] theorem mem_keys {cutoff n : Nat} {bounds : Bounds} {body : Ty} :
    n ∈ keys cutoff bounds body ↔ cutoff ≤ n ∧ .flex n ∈ inputModes bounds body := by
  simp only [keys, List.mem_filterMap, Finset.mem_toList]
  constructor
  · rintro ⟨v, hv, he⟩
    cases v with
    | rigid => contradiction
    | flex k =>
      dsimp only at he
      split at he <;> try contradiction
      cases he
      exact ⟨by assumption, hv⟩
  · intro h
    exact ⟨.flex n, h.2, by simp [h.1]⟩

noncomputable def project (cutoff : Nat) (bounds : Bounds) (body : Ty) (σ : CompareSubstitution) : CompareSubstitution :=
  { types := σ.types.map fun (n, a) => (n, a.subst CompareTy.var (restrict (names cutoff)))
    modes := (keys cutoff bounds body).map fun n => (n, (σ.mode (.flex n)).subst (restrict (names cutoff))) }

theorem project_type (cutoff : Nat) (bounds : Bounds) (body : Ty) (σ : CompareSubstitution)
    (v : TypeVar) :
    (project cutoff bounds body σ).type v = (σ.type v).subst CompareTy.var (restrict (names cutoff)) := by
  cases v <;> simp only [project, CompareSubstitution.type, lookup_map_values]
  case rigid => rfl
  case flex n => cases σ.types.lookup n <;> rfl

theorem project_mode_at {cutoff : Nat} {bounds : Bounds} {body : Ty} (σ : CompareSubstitution)
    {n : Nat} (hn : n ∈ keys cutoff bounds body) :
    (project cutoff bounds body σ).mode (.flex n) =
      (σ.mode (.flex n)).subst (restrict (names cutoff)) := by
  simp only [project, CompareSubstitution.mode, List.lookup_graph _ hn, Option.getD_some]

theorem project_mode_fixed {cutoff : Nat} {bounds : Bounds} {body : Ty} (σ : CompareSubstitution)
    {v : ModVar} (hv : v.index < cutoff) : (project cutoff bounds body σ).mode v = .var v := by
  cases v with
  | rigid => rfl
  | flex n =>
    have hn : n ∉ keys cutoff bounds body := by
      intro h
      have := (mem_keys.mp h).1
      simp only [ModVar.index] at hv
      omega
    have he : ((keys cutoff bounds body).map fun k =>
        (k, (σ.mode (.flex k)).subst (restrict (names cutoff)))).lookup n = none := by
      apply List.lookup_eq_none_iff.mpr
      intro entry he
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp he
      exact bne_iff_ne.mpr (fun he => hn (he ▸ hk))
    change (((keys cutoff bounds body).map fun k =>
      (k, (σ.mode (.flex k)).subst (restrict (names cutoff)))).lookup n).getD _ = _
    rw [he]
    rfl

/-- Public rigid names remain in the fixed namespace; flexible source and
auxiliary names are materialized by the image projection. -/
def RigidScoped (cutoff : Nat) (v : ModVar) : Prop :=
  match v with
  | .flex _ => True
  | .rigid n => n < cutoff

theorem project_mode {cutoff : Nat} {bounds : Bounds} {body : Ty} {σ : CompareSubstitution}
    (hf : ∀ v, v.index < cutoff → σ.mode v = .var v)
    (hs : ∀ v ∈ inputModes bounds body, RigidScoped cutoff v)
    {v : ModVar} (hv : v ∈ inputModes bounds body) :
    (project cutoff bounds body σ).mode v = (σ.mode v).subst (restrict (names cutoff)) := by
  by_cases hl : v.index < cutoff
  · rw [project_mode_fixed σ hl, hf v hl]
    simp [ModExpr.subst, restrict, hl]
  · cases v with
    | rigid n => exact False.elim (hl (hs _ hv))
    | flex n => exact project_mode_at σ (mem_keys.mpr ⟨by simpa only [ModVar.index] using Nat.le_of_not_gt hl, hv⟩)

theorem project_ty {cutoff : Nat} {bounds : Bounds} {body : Ty} {σ : CompareSubstitution}
    (hf : ∀ v, v.index < cutoff → σ.mode v = .var v)
    (hs : ∀ v ∈ inputModes bounds body, RigidScoped cutoff v)
    (a : Ty) (ha : a.modVars ⊆ inputModes bounds body) :
    (project cutoff bounds body σ).ty a =
      (σ.ty a).subst CompareTy.var (restrict (names cutoff)) := by
  induction a with
  | var v => exact project_type cutoff bounds body σ v
  | unit | credit => rfl
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    simp only [TypeExpr.modVars, Finset.union_subset_iff] at ha
    simpa only [CompareSubstitution.ty, CompareTy.ofTy, CompareTy.subst, CompareTy.prod.injEq,
      CompareTy.sum.injEq, CompareTy.fn.injEq] using And.intro (iha ha.1) (ihb ha.2)
  | modal a m ih =>
    simp only [TypeExpr.modVars, Finset.union_subset_iff] at ha
    have hm : m.subst (project cutoff bounds body σ).mode =
        (m.subst σ.mode).subst (restrict (names cutoff)) := by
      rw [ModExpr.subst_subst]
      exact m.subst_congr (fun v hv => project_mode hf hs (ha.2 hv))
    exact congrArg₂ CompareTy.modal (ih ha.1) hm

theorem project_modeExpr {cutoff : Nat} {bounds : Bounds} {body : Ty} {σ : CompareSubstitution}
    (hf : ∀ v, v.index < cutoff → σ.mode v = .var v)
    (hs : ∀ v ∈ inputModes bounds body, RigidScoped cutoff v)
    (m : ModExpr) (hm : m.vars ⊆ inputModes bounds body) :
    m.subst (project cutoff bounds body σ).mode =
      (m.subst σ.mode).subst (restrict (names cutoff)) := by
  rw [ModExpr.subst_subst]
  exact m.subst_congr (fun v hv => project_mode hf hs (hm hv))

theorem fixed_sub {Δ : Bounds} {ms : ModVar → ModExpr} (h : Fixed Δ ms)
    {a b : CompareTy} (hab : AlgebraEntails Δ (.sub a b)) :
    AlgebraEntails Δ (.sub (a.subst CompareTy.var ms) (b.subst CompareTy.var ms)) :=
  ⟨h.algebra hab.1, h.type_defined hab.2.1, h.type_defined hab.2.2⟩

theorem project_constraint {cutoff : Nat} {bounds Δ : Bounds} {body : Ty}
    {σ : CompareSubstitution}
    (hΔ : Δ.modVars ⊆ names cutoff)
    (hf : ∀ v, v.index < cutoff → σ.mode v = .var v)
    (hs : ∀ v ∈ inputModes bounds body, RigidScoped cutoff v)
    (c : Constraint) (hcm : c.modVars ⊆ inputModes bounds body)
    (hc : AlgebraEntails Δ (σ.constraint c)) :
    AlgebraEntails Δ ((project cutoff bounds body σ).constraint c) := by
  have hh := restrict_fixed Δ (names cutoff) hΔ
  cases c <;> simp only [Constraint.modVars, Finset.union_subset_iff] at hcm
  case equal v a =>
    rw [CompareSubstitution.algebra_equal_iff, project_type, project_ty hf hs a hcm]
    exact ⟨fixed_sub hh ((σ.algebra_equal_iff Δ v a).mp hc).1,
      fixed_sub hh ((σ.algebra_equal_iff Δ v a).mp hc).2⟩
  case sub a b =>
    simpa only [CompareSubstitution.constraint, project_ty hf hs a hcm.1,
      project_ty hf hs b hcm.2] using fixed_sub hh hc
  case mode m n =>
    simpa only [CompareSubstitution.constraint, AlgebraEntails,
      project_modeExpr hf hs m hcm.1, project_modeExpr hf hs n hcm.2] using hh.submode hc
  case defined m =>
    simpa only [CompareSubstitution.constraint, AlgebraEntails,
      project_modeExpr hf hs m hcm] using hh.defined hc
  case equiv a b =>
    simp only [CompareSubstitution.constraint, AlgebraEntails,
      project_ty hf hs a hcm.1, project_ty hf hs b hcm.2]
    exact ⟨hh.algebra hc.1, hh.algebra hc.2.1,
      hh.type_defined hc.2.2.1, hh.type_defined hc.2.2.2⟩

theorem project_bounds {cutoff : Nat} {bounds Δ : Bounds} {body : Ty}
    {σ : CompareSubstitution}
    (hΔ : Δ.modVars ⊆ names cutoff)
    (hf : ∀ v, v.index < cutoff → σ.mode v = .var v)
    (hs : ∀ v ∈ inputModes bounds body, RigidScoped cutoff v)
    (hc : AlgebraEntailsAll Δ (σ.bounds bounds)) :
    AlgebraEntailsAll Δ ((project cutoff bounds body σ).bounds bounds) := by
  simp only [AlgebraEntailsAll, CompareSubstitution.bounds, List.forall_mem_map] at hc ⊢
  intro c hc'
  exact project_constraint hΔ hf hs c (fun v hv => Finset.mem_union_left _
    ((bounds.mem_modVars_iff v).mpr ⟨c,hc',hv⟩)) (hc c hc')

theorem project_body {cutoff : Nat} {bounds Δ : Bounds} {body target : Ty}
    {σ : CompareSubstitution}
    (hΔ : Δ.modVars ⊆ names cutoff)
    (hf : ∀ v, v.index < cutoff → σ.mode v = .var v)
    (hs : ∀ v ∈ inputModes bounds body, RigidScoped cutoff v)
    (ht : target.modVars ⊆ names cutoff)
    (hc : AlgebraSubtype Δ (σ.ty body) (.ofTy target)) :
    AlgebraSubtype Δ ((project cutoff bounds body σ).ty body) (.ofTy target) := by
  rw [project_ty hf hs body (fun _ hv => Finset.mem_union_right _ hv)]
  have he : (CompareTy.ofTy target).subst CompareTy.var (restrict (names cutoff)) = .ofTy target :=
    ofTy_fixed target (fun v hv => by simp only [restrict, if_pos (ht hv)])
  simpa only [he] using (restrict_fixed Δ (names cutoff) hΔ).algebra hc

theorem project_body_defined {cutoff : Nat} {bounds Δ : Bounds} {body : Ty}
    {σ : CompareSubstitution}
    (hΔ : Δ.modVars ⊆ names cutoff)
    (hf : ∀ v, v.index < cutoff → σ.mode v = .var v)
    (hs : ∀ v ∈ inputModes bounds body, RigidScoped cutoff v)
    (hc : (σ.ty body).DefinedUnder Δ) :
    ((project cutoff bounds body σ).ty body).DefinedUnder Δ := by
  rw [project_ty hf hs body (fun _ hv => Finset.mem_union_right _ hv)]
  exact (restrict_fixed Δ (names cutoff) hΔ).type_defined hc

theorem project_wellShaped {cutoff : Nat} {bounds Δ : Bounds} {body : Ty}
    {σ : CompareSubstitution} (h : σ.WellShaped Δ) :
    (project cutoff bounds body σ).WellShaped Δ := by
  rintro entry he
  obtain ⟨⟨n,a⟩, ha, rfl⟩ := List.mem_map.mp he
  exact (a.wellShaped_subst_modes_iff _).mpr (h (n,a) ha)

theorem project_wellFormedUnder {cutoff : Nat} {bounds Δ : Bounds} {body : Ty}
    {σ : CompareSubstitution} (hΔ : Δ.modVars ⊆ names cutoff) (h : σ.WellFormedUnder Δ) :
    (project cutoff bounds body σ).WellFormedUnder Δ := by
  have hf := restrict_fixed Δ (names cutoff) hΔ
  constructor
  · intro v
    rw [project_type]
    exact hf.type_defined (h.types v)
  · apply (CompareSubstitution.wellFormedUnder_of_images
      (σ := {modes := (project cutoff bounds body σ).modes}) (by simp) ?_).modes
    intro entry he
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp he
    exact hf.defined (h.modes (.flex n))

theorem project_domainsAbove {cutoff nt : Nat} {bounds : Bounds} {body : Ty}
    {σ : CompareSubstitution} (h : σ.DomainsAbove nt cutoff) :
    (project cutoff bounds body σ).DomainsAbove nt cutoff := by
  constructor
  · rintro entry he
    obtain ⟨⟨n,a⟩, ha, rfl⟩ := List.mem_map.mp he
    exact h.1 (n,a) ha
  · rintro entry he
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp he
    exact (mem_keys.mp hn).1

theorem project_type_shape (cutoff : Nat) (bounds : Bounds) (body : Ty)
    (σ : CompareSubstitution) (v : TypeVar) :
    ((project cutoff bounds body σ).type v).shape = (σ.type v).shape := by
  rw [project_type, CompareTy.shape_subst_modes]

/-- Every image mode is an input name fixed by this very action. -/
def FixedImages (cutoff : Nat) (σ : CompareSubstitution) : Prop :=
  (∀ v, ComparisonInterpolation.Supports (fun _ => True) (fun w => w.index < cutoff) (σ.type v)) ∧
  (∀ entry ∈ σ.modes, ∀ v ∈ entry.2.vars, v.index < cutoff)

theorem project_fixedImages (cutoff : Nat) (bounds : Bounds) (body : Ty)
    (σ : CompareSubstitution) : FixedImages cutoff (project cutoff bounds body σ) := by
  constructor
  · intro v
    rw [project_type]
    simpa only [mem_names] using restrict_type_support (names cutoff) (σ.type v)
  · intro entry he
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp he
    intro v hv
    exact (mem_names v cutoff).mp (restrict_support (names cutoff) _ v hv)

theorem rigidScoped_of_index {cutoff : Nat} {v : ModVar} (h : v.index < cutoff) :
    RigidScoped cutoff v := by
  cases v with
  | flex => trivial
  | rigid => exact h

theorem fresh_type_modes (s : Scheme) (nt nm cutoff : Nat) (v : TypeVar) :
    ∀ w ∈ ((s.freshSubstitution nt nm).type v).modVars, RigidScoped cutoff w := by
  obtain ⟨w,hw⟩ := s.freshSubstitution_type_variable nt nm false v
  simp only [hw, TypeExpr.modVars, Finset.notMem_empty, false_implies, implies_true]

theorem fresh_mode_scoped (s : Scheme) (nt nm cutoff : Nat) (v : ModVar)
    (hv : RigidScoped cutoff v) :
    ∀ w ∈ ((s.freshSubstitution nt nm).mode v).vars, RigidScoped cutoff w := by
  apply Substitution.mode_support ?_ v hv
  intro entry he w hw
  simp only [Scheme.freshSubstitution, List.mem_map, Prod.exists] at he
  obtain ⟨name,i,_,rfl,rfl⟩ := he
  simp only [Bool.false_eq_true, if_false, ModExpr.vars, Finset.mem_singleton] at hw
  subst w
  trivial

theorem bounds_mode_support {Q : ModVar → Prop} (bounds : Bounds) (σ : Substitution)
    (ht : ∀ v, ∀ w ∈ (σ.type v).modVars, Q w)
    (hm : ∀ v, Q v → ∀ w ∈ (σ.mode v).vars, Q w)
    (hc : ∀ v ∈ bounds.modVars, Q v) :
    ∀ w ∈ (σ.bounds bounds).modVars, Q w := by
  intro w hw
  obtain ⟨c,hc',hw⟩ := ((σ.bounds bounds).mem_modVars_iff w).mp hw
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc'
  exact d.mode_support_subst σ ht hm (fun v hv => hc v
    ((bounds.mem_modVars_iff v).mpr ⟨d,hd,hv⟩)) w hw

/-- Freshening introduces only flexible source names. All rigid source names
remain below the fresh source namespace. -/
theorem prepared_rigidScoped (ambient : Bounds) (source target : Scheme) :
    let p := SchemePreparation.prepare ambient source target
    ∀ v ∈ inputModes p.sourceBounds p.sourceType, RigidScoped p.firstMode v := by
  let p := SchemePreparation.prepare ambient source target
  change ∀ v ∈ inputModes p.sourceBounds p.sourceType, RigidScoped p.firstMode v
  have original (v : ModVar) (hv : v ∈ source.bounds.modVars ∪ source.body.modVars) :
      RigidScoped p.firstMode v := by
    apply rigidScoped_of_index
    apply SchemePreparation.original_mode_lt_first
    simp only [SchemePreparation.originalModeIds, List.mem_append,
      TypeExpr.mem_modeVariables, Bounds.mem_modeVariables]
    rcases Finset.mem_union.mp hv with hv | hv <;> tauto
  have ht := fresh_type_modes source p.firstType p.firstMode p.firstMode
  have hm := fresh_mode_scoped source p.firstType p.firstMode p.firstMode
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact bounds_mode_support source.bounds p.sourceRenaming ht hm
      (fun v hv => original v (Finset.mem_union_left _ hv)) v hv
  · exact TypeExpr.mode_support_subst source.body p.sourceRenaming (fun v _ => ht v)
      (fun v hv => hm v (original v (Finset.mem_union_right _ hv))) v hv

theorem prepared_assumptions (ambient : Bounds) (source target : Scheme) :
    (SchemePreparation.prepare ambient source target).assumptions.modVars ⊆
      names (SchemePreparation.prepare ambient source target).firstMode := by
  intro v hv
  exact (mem_names v _).mpr (((Bounds.bounded_iff _ _ _).mp
    (SchemePreparation.prepare_assumptions_bounded_first ambient source target)).2 v hv)

theorem prepared_target (ambient : Bounds) (source target : Scheme) :
    (SchemePreparation.prepare ambient source target).targetType.modVars ⊆
      names (SchemePreparation.prepare ambient source target).firstMode := by
  intro v hv
  exact (mem_names v _).mpr (((TypeExpr.bounded_iff _ _ _).mp
    (SchemePreparation.prepare_targetType_bounded_first ambient source target)).2 v hv)

/-- Projection acts on all images simultaneously, preserving admissibility
under the same assumptions and making every retained image mode fixed. -/
theorem prepared_project {ambient : Bounds} {source target : Scheme} {σ : CompareSubstitution}
    (h : PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ) :
    let p := SchemePreparation.prepare ambient source target
    let result := project p.firstMode p.sourceBounds p.sourceType σ
    PreparedWitnessUnder p result ∧ FixedImages p.firstMode result := by
  let p := SchemePreparation.prepare ambient source target
  have hΔ := prepared_assumptions ambient source target
  have hs := prepared_rigidScoped ambient source target
  have hf := h.1.1.mode_fixed
  refine ⟨⟨⟨project_domainsAbove h.1.1, project_wellShaped h.1.2.1,
    project_bounds hΔ hf hs h.1.2.2.1,
    project_body hΔ hf hs (prepared_target ambient source target) h.1.2.2.2⟩,
    project_wellFormedUnder hΔ h.2.1, project_body_defined hΔ hf hs h.2.2⟩,
    project_fixedImages _ _ _ _⟩

/-- Every admissible original comparison has an admissible prepared witness
whose image annotations use only the fixed input namespace. -/
theorem algebra_prepared_fixed {ambient : Bounds} {source target : Scheme}
    (h : AlgebraSubsumesUnder ambient source target) :
    let p := SchemePreparation.prepare ambient source target
    ∃ σ, PreparedWitnessUnder p σ ∧ FixedImages p.firstMode σ := by
  obtain ⟨σ,hσ⟩ := ComparisonPreparation.prepare_algebra_under_complete h
  exact ⟨_, prepared_project hσ⟩

theorem template_rigidScoped {p : SchemePreparation.Prepared}
    (solved : ComparisonShapeSolver.Solved)
    (hs : ∀ v ∈ inputModes p.sourceBounds p.sourceType, RigidScoped p.firstMode v) :
    let templates := ComparisonSkeleton.prepare p solved
    ∀ v ∈ inputModes (templates.substitution.bounds p.sourceBounds)
      (templates.substitution.ty p.sourceType), RigidScoped p.firstMode v := by
  let templates := ComparisonSkeleton.prepare p solved
  change ∀ v ∈ inputModes (templates.substitution.bounds p.sourceBounds)
      (templates.substitution.ty p.sourceType), RigidScoped p.firstMode v
  have ht : ∀ v, ∀ w ∈ (templates.substitution.type v).modVars, RigidScoped p.firstMode w := by
    apply Substitution.type_modeSupport
    exact ComparisonSkeleton.allocate_modeSupport p solved _ _ _ (fun _ _ => trivial)
  have hm (v : ModVar) (hv : RigidScoped p.firstMode v) :
      ∀ w ∈ (templates.substitution.mode v).vars, RigidScoped p.firstMode w := by
    rw [ComparisonSkeleton.prepare_mode]
    simpa only [ModExpr.vars, Finset.mem_singleton, forall_eq] using hv
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact bounds_mode_support p.sourceBounds templates.substitution ht hm
      (fun v hv => hs v (Finset.mem_union_left _ hv)) v hv
  · exact TypeExpr.mode_support_subst p.sourceType templates.substitution
      (fun v _ => ht v) (fun v hv => hm v (hs v (Finset.mem_union_right _ hv))) v hv

theorem project_mode_support {cutoff : Nat} {bounds : Bounds} {body : Ty}
    {σ : CompareSubstitution}
    (hf : ∀ v, v.index < cutoff → σ.mode v = .var v)
    (hs : ∀ v ∈ inputModes bounds body, RigidScoped cutoff v)
    {v : ModVar} (hv : v ∈ inputModes bounds body) :
    ∀ w ∈ ((project cutoff bounds body σ).mode v).vars, w.index < cutoff := by
  rw [project_mode hf hs hv]
  exact fun w hw => (mem_names w cutoff).mp (restrict_support (names cutoff) _ w hw)

/-- The actual shape/template factorization admits one common coordinate
assignment whose images mention only fixed input modes. The projection preserves
each allocated leaf's class and all source obligations under the original guards. -/
theorem prepared_template_fixed {source target : Scheme}
    {fuel : Nat} {solved : ComparisonShapeSolver.Solved} {σ : CompareSubstitution}
    (hshape : ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare [] source target) =
      .success (.solved solved))
    (hw : PreparedWitnessUnder (SchemePreparation.prepare [] source target) σ)
    (hR : Residual target.bounds) :
    let p := SchemePreparation.prepare [] source target
    let templates := ComparisonSkeleton.prepare p solved
    ∃ core : CompareSubstitution,
      core.DomainsAbove p.nextType p.firstMode ∧
      core.WellShaped p.assumptions ∧ core.WellFormedUnder p.assumptions ∧
      AlgebraEntailsAll p.assumptions (core.bounds (templates.substitution.bounds p.sourceBounds)) ∧
      (core.ty (templates.substitution.ty p.sourceType)).DefinedUnder p.assumptions ∧
      AlgebraSubtype p.assumptions (core.ty (templates.substitution.ty p.sourceType)) (.ofTy p.targetType) ∧
      FixedImages p.firstMode core ∧
      (∀ leaf ∈ templates.leaves, ComparisonShape.Equivalent p.assumptions
        (core.type (.flex leaf.name)).shape (.var leaf.shapeClass)) ∧
      (∀ v ∈ inputModes (templates.substitution.bounds p.sourceBounds)
          (templates.substitution.ty p.sourceType),
        ∀ w ∈ (core.mode v).vars, w.index < p.firstMode) := by
  let p := SchemePreparation.prepare [] source target
  let templates := ComparisonSkeleton.prepare p solved
  obtain ⟨trees, hsh, hWF, hb, hd, hbody, _, _⟩ :=
    ComparisonSkeleton.prepared_template_under hshape hw hR
  let old := ComparisonSkeleton.preparedForest p solved trees σ
  have hdom : old.DomainsAbove p.nextType p.firstMode :=
    ComparisonSkeleton.preparedForest_domains p solved trees σ (Nat.le_add_right _ _) hw.1.1
  have hf := hdom.mode_fixed
  have hs := template_rigidScoped solved (prepared_rigidScoped [] source target)
  have hΔ := prepared_assumptions [] source target
  let core := project p.firstMode (templates.substitution.bounds p.sourceBounds)
    (templates.substitution.ty p.sourceType) old
  refine ⟨core, project_domainsAbove hdom, project_wellShaped hsh,
    project_wellFormedUnder hΔ hWF, project_bounds hΔ hf hs hb,
    project_body_defined hΔ hf hs hd,
    project_body hΔ hf hs (prepared_target [] source target) hbody,
    project_fixedImages _ _ _ _, ?_, ?_⟩
  · intro leaf hl
    rw [project_type_shape]
    exact ComparisonSkeleton.preparedForest_leaf p solved trees σ hl
  · exact fun v hv => project_mode_support hf hs hv

theorem project_type_support {cutoff : Nat} {bounds : Bounds} {body : Ty}
    {σ : CompareSubstitution} {P : TypeVar → Prop} {v : TypeVar}
    (h : ComparisonInterpolation.Supports P (fun _ => True) (σ.type v)) :
    ComparisonInterpolation.Supports P (fun w => w.index < cutoff)
      ((project cutoff bounds body σ).type v) := by
  rw [project_type]
  apply h.subst (types := CompareTy.var) (modes := restrict (names cutoff))
    (fun _ hv => hv)
  intro v _ w hw
  by_cases hv : v ∈ names cutoff
  · simp only [restrict, if_pos hv, ModExpr.vars, Finset.mem_singleton] at hw
    subst w
    exact (mem_names v cutoff).mp hv
  · simp only [restrict, if_neg hv, ModExpr.epsilon, ModExpr.vars, Finset.notMem_empty] at hw

theorem fixedImages_type_idempotent {cutoff : Nat} {σ : CompareSubstitution}
    (hs : FixedImages cutoff σ) (hf : ∀ v, v.index < cutoff → σ.mode v = .var v)
    (v : TypeVar) : (σ.type v).subst CompareTy.var σ.mode = σ.type v := by
  rw [(hs.1 v).subst_congr (types₂ := CompareTy.var) (modes₂ := ModExpr.var)
    (fun _ _ => rfl) hf]
  exact CompareTy.subst_id _

theorem project_type_idempotent (cutoff : Nat) (bounds : Bounds) (body : Ty)
    (σ : CompareSubstitution) (v : TypeVar) :
    let result := project cutoff bounds body σ
    (result.type v).subst CompareTy.var result.mode = result.type v :=
  fixedImages_type_idempotent (project_fixedImages cutoff bounds body σ)
    (fun _ hv => project_mode_fixed σ hv) v

theorem prepared_template_fixed_opaque {source target : Scheme}
    {fuel : Nat} {solved : ComparisonShapeSolver.Solved} {σ : CompareSubstitution}
    (hshape : ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare [] source target) =
      .success (.solved solved))
    (hw : PreparedWitnessUnder (SchemePreparation.prepare [] source target) σ)
    (hR : Residual target.bounds) :
    let p := SchemePreparation.prepare [] source target
    let templates := ComparisonSkeleton.prepare p solved
    ∃ core : CompareSubstitution,
      core.DomainsAbove p.nextType p.firstMode ∧
      core.WellShaped p.assumptions ∧ core.WellFormedUnder p.assumptions ∧
      AlgebraEntailsAll p.assumptions (core.bounds (templates.substitution.bounds p.sourceBounds)) ∧
      (core.ty (templates.substitution.ty p.sourceType)).DefinedUnder p.assumptions ∧
      AlgebraSubtype p.assumptions (core.ty (templates.substitution.ty p.sourceType)) (.ofTy p.targetType) ∧
      FixedImages p.firstMode core ∧
      (∀ leaf ∈ templates.leaves, ComparisonShape.Equivalent p.assumptions
        (core.type (.flex leaf.name)).shape (.var leaf.shapeClass)) ∧
      (∀ v ∈ inputModes (templates.substitution.bounds p.sourceBounds)
          (templates.substitution.ty p.sourceType),
        ∀ w ∈ (core.mode v).vars, w.index < p.firstMode) ∧
      ComparisonReduction.OpaqueAction core := by
  let p := SchemePreparation.prepare [] source target
  let templates := ComparisonSkeleton.prepare p solved
  obtain ⟨trees, hsh, hWF, hb, hd, hbody, _, _⟩ :=
    ComparisonSkeleton.prepared_template_under hshape hw hR
  let old := ComparisonSkeleton.preparedForest p solved trees σ
  have hdom : old.DomainsAbove p.nextType p.firstMode :=
    ComparisonSkeleton.preparedForest_domains p solved trees σ (Nat.le_add_right _ _) hw.1.1
  have hf := hdom.mode_fixed
  have hs := template_rigidScoped solved (prepared_rigidScoped [] source target)
  have hΔ := prepared_assumptions [] source target
  let core := project p.firstMode (templates.substitution.bounds p.sourceBounds)
    (templates.substitution.ty p.sourceType) old
  refine ⟨core, project_domainsAbove hdom, project_wellShaped hsh,
    project_wellFormedUnder hΔ hWF, project_bounds hΔ hf hs hb,
    project_body_defined hΔ hf hs hd,
    project_body hΔ hf hs (prepared_target [] source target) hbody,
    project_fixedImages _ _ _ _, ?_, ?_, ?_⟩
  · intro leaf hl
    rw [project_type_shape]
    exact ComparisonSkeleton.preparedForest_leaf p solved trees σ hl
  · exact fun v hv => project_mode_support hf hs hv

  · intro v
    rw [project_type_shape]
    exact ComparisonSkeleton.preparedForest_opaque
      (SchemePreparation.prepare_assumptions_residual hR) p solved trees σ v

end ModalityInference.ComparisonFixedModeWitness
