import ModalityInference.Proofs.ComparisonWitnessSupport
import ModalityInference.Proofs.ComparisonPreparationComplete

/-! Simultaneous restriction of a prepared comparison witness to names in its
input. Shared images, guarded bounds, and the bare body comparison are retained. -/

namespace ModalityInference.ComparisonWitnessRestriction

def restrictTy (types : Finset TypeVar) (modes : Finset ModVar) (a : CompareTy) : CompareTy :=
  (a.subst CompareTy.var (ComparisonModeRestriction.restrict modes)).subst
    (ComparisonTypeRestriction.restrict types) ModExpr.var

def restrict (types : Finset TypeVar) (modes : Finset ModVar)
    (action : CompareSubstitution) : CompareSubstitution :=
  { types := action.types.map fun (n, a) => (n, restrictTy types modes a)
    modes := action.modes.map fun (n, m) => (n, m.subst (ComparisonModeRestriction.restrict modes)) }

theorem restrict_type (types : Finset TypeVar) (modes : Finset ModVar)
    (action : CompareSubstitution) {v : TypeVar} (hv : v ∈ types) :
    (restrict types modes action).type v = restrictTy types modes (action.type v) := by
  cases v <;> simp only [restrict, CompareSubstitution.type, lookup_map_values]
  case flex n =>
    cases action.types.lookup n <;> simp [restrictTy, CompareTy.subst,
      ComparisonTypeRestriction.restrict, hv]
  case rigid n => simp [restrictTy, CompareTy.subst, ComparisonTypeRestriction.restrict, hv]

theorem restrict_mode (types : Finset TypeVar) (modes : Finset ModVar)
    (action : CompareSubstitution) {v : ModVar} (hv : v ∈ modes) :
    (restrict types modes action).mode v =
      (action.mode v).subst (ComparisonModeRestriction.restrict modes) := by
  cases v <;> simp only [restrict, CompareSubstitution.mode, lookup_map_values]
  case flex n =>
    cases action.modes.lookup n <;> simp [ModExpr.subst, ComparisonModeRestriction.restrict, hv]
  case rigid n => simp [ModExpr.subst, ComparisonModeRestriction.restrict, hv]

theorem restrict_modeExpr (types : Finset TypeVar) (modes : Finset ModVar)
    (action : CompareSubstitution) (m : ModExpr) (hm : m.vars ⊆ modes) :
    m.subst (restrict types modes action).mode =
      (m.subst action.mode).subst (ComparisonModeRestriction.restrict modes) := by
  rw [ModExpr.subst_subst]
  exact m.subst_congr fun v hv => restrict_mode types modes action (hm hv)

theorem restrict_ty (types : Finset TypeVar) (modes : Finset ModVar)
    (action : CompareSubstitution) (a : Ty)
    (ht : a.typeVars ⊆ types) (hm : a.modVars ⊆ modes) :
    (restrict types modes action).ty a = restrictTy types modes (action.ty a) := by
  induction a with
  | var v => exact restrict_type types modes action (ht (by simp [TypeExpr.typeVars]))
  | unit | credit => rfl
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    simp only [TypeExpr.typeVars, TypeExpr.modVars, Finset.union_subset_iff] at ht hm
    simpa only [CompareSubstitution.ty, CompareTy.ofTy, CompareTy.subst, restrictTy,
      CompareTy.prod.injEq, CompareTy.sum.injEq, CompareTy.fn.injEq] using
      And.intro (iha ht.1 hm.1) (ihb ht.2 hm.2)
  | modal a m ih =>
    simp only [TypeExpr.typeVars, TypeExpr.modVars, Finset.union_subset_iff] at ht hm
    simpa only [CompareSubstitution.ty, CompareTy.ofTy, CompareTy.subst, restrictTy,
      ModExpr.subst_id, CompareTy.modal.injEq] using
      And.intro (ih ht hm.1) (restrict_modeExpr types modes action m hm.2)

theorem restrictTy_algebra {Δ : Bounds} {types : Finset TypeVar} {modes : Finset ModVar}
    (ht : Δ.typeVars ⊆ types) (hm : Δ.modVars ⊆ modes) {a b : CompareTy}
    (hab : AlgebraSubtype Δ a b) :
    AlgebraSubtype Δ (restrictTy types modes a) (restrictTy types modes b) :=
  (ComparisonTypeRestriction.restrict_fixed Δ types ht).algebra
    ((ComparisonModeRestriction.restrict_fixed Δ modes hm).algebra hab)

theorem restrictTy_defined {Δ : Bounds} {types : Finset TypeVar} {modes : Finset ModVar}
    (ht : Δ.typeVars ⊆ types) (hm : Δ.modVars ⊆ modes) {a : CompareTy}
    (ha : a.DefinedUnder Δ) : (restrictTy types modes a).DefinedUnder Δ :=
  (ComparisonTypeRestriction.restrict_fixed Δ types ht).type_defined
    ((ComparisonModeRestriction.restrict_fixed Δ modes hm).type_defined ha)

theorem restrictTy_wellShaped {Δ : Bounds} {types : Finset TypeVar} {modes : Finset ModVar}
    (ht : Δ.typeVars ⊆ types) {a : CompareTy} (ha : a.WellShaped Δ) :
    (restrictTy types modes a).WellShaped Δ :=
  (ComparisonTypeRestriction.restrict_fixed Δ types ht).wellShaped
    ((a.wellShaped_subst_modes_iff _).mpr ha)

theorem restrictTy_support (types : Finset TypeVar) (modes : Finset ModVar) (a : CompareTy) :
    ComparisonInterpolation.Supports (fun v => v ∈ types) (fun v => v ∈ modes)
      (restrictTy types modes a) :=
  ComparisonTypeRestriction.restrict_support types
    (ComparisonModeRestriction.restrict_type_support modes a)

theorem restrictTy_sub {Δ : Bounds} {types : Finset TypeVar} {modes : Finset ModVar}
    (ht : Δ.typeVars ⊆ types) (hm : Δ.modVars ⊆ modes) {a b : CompareTy}
    (h : AlgebraEntails Δ (.sub a b)) :
    AlgebraEntails Δ (.sub (restrictTy types modes a) (restrictTy types modes b)) :=
  ⟨restrictTy_algebra ht hm h.1, restrictTy_defined ht hm h.2.1,
    restrictTy_defined ht hm h.2.2⟩

theorem restrict_constraint {Δ : Bounds} {types : Finset TypeVar} {modes : Finset ModVar}
    (ht : Δ.typeVars ⊆ types) (hm : Δ.modVars ⊆ modes)
    (action : CompareSubstitution) (c : Constraint)
    (hct : c.typeVars ⊆ types) (hcm : c.modVars ⊆ modes)
    (hc : AlgebraEntails Δ (action.constraint c)) :
    AlgebraEntails Δ ((restrict types modes action).constraint c) := by
  cases c <;> simp only [Constraint.typeVars, Constraint.modVars,
    Finset.union_subset_iff, Finset.insert_subset_iff] at hct hcm
  case equal v a =>
    rw [CompareSubstitution.algebra_equal_iff,
      restrict_type types modes action hct.1, restrict_ty types modes action a hct.2 hcm]
    exact ⟨restrictTy_sub ht hm ((action.algebra_equal_iff Δ v a).mp hc).1,
      restrictTy_sub ht hm ((action.algebra_equal_iff Δ v a).mp hc).2⟩
  case sub a b =>
    simpa only [CompareSubstitution.constraint,
      restrict_ty types modes action a hct.1 hcm.1,
      restrict_ty types modes action b hct.2 hcm.2] using restrictTy_sub ht hm hc
  case mode m n =>
    simpa only [CompareSubstitution.constraint, AlgebraEntails,
      restrict_modeExpr types modes action m hcm.1,
      restrict_modeExpr types modes action n hcm.2] using
      (ComparisonModeRestriction.restrict_fixed Δ modes hm).submode hc
  case defined m =>
    simpa only [CompareSubstitution.constraint, AlgebraEntails,
      restrict_modeExpr types modes action m hcm] using
      (ComparisonModeRestriction.restrict_fixed Δ modes hm).defined hc
  case equiv a b =>
    simp only [CompareSubstitution.constraint, AlgebraEntails,
      restrict_ty types modes action a hct.1 hcm.1,
      restrict_ty types modes action b hct.2 hcm.2]
    exact ⟨restrictTy_algebra ht hm hc.1, restrictTy_algebra ht hm hc.2.1,
      restrictTy_defined ht hm hc.2.2.1, restrictTy_defined ht hm hc.2.2.2⟩

theorem restrict_bounds {Δ : Bounds} {types : Finset TypeVar} {modes : Finset ModVar}
    (ht : Δ.typeVars ⊆ types) (hm : Δ.modVars ⊆ modes)
    (action : CompareSubstitution) (cs : Bounds)
    (hct : cs.typeVars ⊆ types) (hcm : cs.modVars ⊆ modes)
    (hc : AlgebraEntailsAll Δ (action.bounds cs)) :
    AlgebraEntailsAll Δ ((restrict types modes action).bounds cs) := by
  simp only [AlgebraEntailsAll, CompareSubstitution.bounds, List.forall_mem_map] at hc ⊢
  exact fun c h => restrict_constraint ht hm action c
    (fun v hv => hct ((cs.mem_typeVars_iff v).mpr ⟨c, h, hv⟩))
    (fun v hv => hcm ((cs.mem_modVars_iff v).mpr ⟨c, h, hv⟩)) (hc c h)

theorem restrict_wellShaped {Δ : Bounds} {types : Finset TypeVar} {modes : Finset ModVar}
    (ht : Δ.typeVars ⊆ types) {action : CompareSubstitution} (h : action.WellShaped Δ) :
    (restrict types modes action).WellShaped Δ := by
  rintro entry he
  obtain ⟨⟨n, a⟩, ha, rfl⟩ := List.mem_map.mp he
  exact restrictTy_wellShaped ht (h (n, a) ha)

theorem restrict_domainsAbove {types : Finset TypeVar} {modes : Finset ModVar}
    {action : CompareSubstitution} {nt nm : Nat} (h : action.DomainsAbove nt nm) :
    (restrict types modes action).DomainsAbove nt nm := by
  constructor <;> rintro entry he
  all_goals obtain ⟨⟨n, a⟩, ha, rfl⟩ := List.mem_map.mp he
  · exact h.1 (n, a) ha
  · exact h.2 (n, a) ha

theorem restrictTy_public {types : Finset TypeVar} {modes : Finset ModVar}
    (a : Ty) (ht : a.typeVars ⊆ types) (hm : a.modVars ⊆ modes) :
    restrictTy types modes (.ofTy a) = .ofTy a := by
  rw [restrictTy, ComparisonModeRestriction.ofTy_fixed a]
  · exact ComparisonTypeRestriction.ofTy_fixed a
      (fun v hv => by simp [ComparisonTypeRestriction.restrict, ht hv])
  · exact fun v hv => by simp [ComparisonModeRestriction.restrict, hm hv]

def inputTypes (p : SchemePreparation.Prepared) : Finset TypeVar :=
  p.assumptions.typeVars ∪ p.sourceBounds.typeVars ∪ p.sourceType.typeVars ∪ p.targetType.typeVars

def inputModes (p : SchemePreparation.Prepared) : Finset ModVar :=
  p.assumptions.modVars ∪ p.sourceBounds.modVars ∪ p.sourceType.modVars ∪ p.targetType.modVars

theorem prepared_restrict {p : SchemePreparation.Prepared} {action : CompareSubstitution}
    (h : ComparisonPreparation.PreparedWitness p action) :
    ComparisonPreparation.PreparedWitness p (restrict (inputTypes p) (inputModes p) action) := by
  have ht : p.assumptions.typeVars ⊆ inputTypes p := by
    intro v hv; simp [inputTypes, hv]
  have hm : p.assumptions.modVars ⊆ inputModes p := by
    intro v hv; simp [inputModes, hv]
  refine ⟨restrict_domainsAbove h.1, restrict_wellShaped ht h.2.1, ?_, ?_⟩
  · exact restrict_bounds ht hm action p.sourceBounds
      (fun v hv => by simp [inputTypes, hv]) (fun v hv => by simp [inputModes, hv]) h.2.2.1
  · rw [restrict_ty (inputTypes p) (inputModes p) action p.sourceType
      (fun v hv => by simp [inputTypes, hv]) (fun v hv => by simp [inputModes, hv])]
    simpa only [restrictTy_public (types := inputTypes p) (modes := inputModes p) p.targetType
      (fun v hv => by simp [inputTypes, hv]) (fun v hv => by simp [inputModes, hv])] using
      restrictTy_algebra ht hm h.2.2.2

theorem restrict_keys (types : Finset TypeVar) (modes : Finset ModVar)
    (action : CompareSubstitution) :
    (restrict types modes action).types.map Prod.fst = action.types.map Prod.fst ∧
    (restrict types modes action).modes.map Prod.fst = action.modes.map Prod.fst := by
  simp [restrict, List.map_map, Function.comp_def]

theorem restrict_support (types : Finset TypeVar) (modes : Finset ModVar)
    (action : CompareSubstitution) :
    (∀ entry ∈ (restrict types modes action).types,
      ComparisonInterpolation.Supports (fun v => v ∈ types) (fun v => v ∈ modes) entry.2) ∧
    (∀ entry ∈ (restrict types modes action).modes, entry.2.vars ⊆ modes) := by
  constructor <;> rintro entry he
  all_goals obtain ⟨⟨n, a⟩, ha, rfl⟩ := List.mem_map.mp he
  · exact restrictTy_support types modes a
  · exact ComparisonModeRestriction.restrict_support modes a

def Supported (p : SchemePreparation.Prepared) (action : CompareSubstitution) : Prop :=
  (∀ entry ∈ action.types, ComparisonInterpolation.Supports
    (fun v => v ∈ inputTypes p) (fun v => v ∈ inputModes p) entry.2) ∧
  (∀ entry ∈ action.modes, entry.2.vars ⊆ inputModes p)

/-- Restriction is simultaneous across the whole witness and preserves its
exact key lists, so repeated occurrences and fixed identifiers keep their scope. -/
theorem prepared_supported {p : SchemePreparation.Prepared} {action : CompareSubstitution}
    (h : ComparisonPreparation.PreparedWitness p action) :
    ∃ result, ComparisonPreparation.PreparedWitness p result ∧
      result.types.map Prod.fst = action.types.map Prod.fst ∧
      result.modes.map Prod.fst = action.modes.map Prod.fst ∧ Supported p result :=
  ⟨_, prepared_restrict h, (restrict_keys _ _ action).1, (restrict_keys _ _ action).2,
    restrict_support _ _ action⟩

theorem algebra_supported {source target : Scheme} (h : AlgebraSubsumes [] source target) :
    ∃ action, ComparisonPreparation.PreparedWitness
      (SchemePreparation.prepare [] source target) action ∧
      Supported (SchemePreparation.prepare [] source target) action := by
  obtain ⟨action, ha⟩ := ComparisonPreparation.prepare_algebra_complete h
  exact ⟨_, prepared_restrict ha, restrict_support _ _ action⟩

end ModalityInference.ComparisonWitnessRestriction
