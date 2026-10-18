import ModalityInference.ComparisonTypeModeClosure
import ModalityInference.Proofs.ComparisonFixedModeWitness
import ModalityInference.Proofs.ComparisonStructuralPrepared

/-! Closing reconstructed type images under the shared modality action
preserves all original comparison obligations under the same assumptions. -/
namespace ModalityInference.CompareSubstitution

def ModesIdempotent (σ : CompareSubstitution) : Prop :=
  ∀v, (σ.mode v).subst σ.mode = σ.mode v

@[simp] theorem closeTypeModes_mode (σ : CompareSubstitution) (v : ModVar) :
    σ.closeTypeModes.mode v = σ.mode v := rfl

theorem closeTypeModes_type (σ : CompareSubstitution) (v : TypeVar) :
    σ.closeTypeModes.type v = (σ.type v).subst CompareTy.var σ.mode := by
  cases v <;> simp only [closeTypeModes, CompareSubstitution.type, lookup_map_values]
  case rigid => rfl
  case flex n => cases σ.types.lookup n <;> rfl

theorem ModesIdempotent.expression {σ : CompareSubstitution} (h : σ.ModesIdempotent)
    (m : ModExpr) : (m.subst σ.mode).subst σ.mode = m.subst σ.mode := by
  rw [ModExpr.subst_subst]
  exact m.subst_congr (fun v _ => h v)

theorem closeTypeModes_ty {σ : CompareSubstitution} (h : σ.ModesIdempotent) (a : Ty) :
    σ.closeTypeModes.ty a = (σ.ty a).subst CompareTy.var σ.mode := by
  induction a with
  | var v => exact closeTypeModes_type σ v
  | unit | credit => rfl
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    simp only [ty, CompareTy.ofTy, CompareTy.subst] at *
    exact congrArg₂ _ iha ihb
  | modal a m ih =>
    simpa only [ty, CompareTy.ofTy, CompareTy.subst, closeTypeModes_mode,
      h.expression] using congrArg (fun t => CompareTy.modal t (m.subst σ.mode)) ih

theorem closeTypeModes_constraint {Δ : Bounds} {σ : CompareSubstitution}
    (hf : ComparisonModeRestriction.Fixed Δ σ.mode) (hi : σ.ModesIdempotent)
    (c : Constraint) (hc : AlgebraEntails Δ (σ.constraint c)) :
    AlgebraEntails Δ (σ.closeTypeModes.constraint c) := by
  cases c with
  | sub a b =>
    simpa only [CompareSubstitution.constraint, closeTypeModes_ty hi] using
      ComparisonFixedModeWitness.fixed_sub hf hc
  | equal v a =>
    rw [CompareSubstitution.algebra_equal_iff] at hc ⊢
    simpa only [closeTypeModes_type, closeTypeModes_ty hi] using
      And.intro (ComparisonFixedModeWitness.fixed_sub hf hc.1)
        (ComparisonFixedModeWitness.fixed_sub hf hc.2)
  | equiv a b =>
    simp only [CompareSubstitution.constraint, AlgebraEntails, closeTypeModes_ty hi]
    exact ⟨hf.algebra hc.1, hf.algebra hc.2.1,
      hf.type_defined hc.2.2.1, hf.type_defined hc.2.2.2⟩
  | mode m n | defined m => exact hc

theorem closeTypeModes_bounds {Δ : Bounds} {σ : CompareSubstitution}
    (hf : ComparisonModeRestriction.Fixed Δ σ.mode) (hi : σ.ModesIdempotent)
    (cs : Bounds) (hc : AlgebraEntailsAll Δ (σ.bounds cs)) :
    AlgebraEntailsAll Δ (σ.closeTypeModes.bounds cs) := by
  intro out hout
  obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hout
  exact closeTypeModes_constraint hf hi c (hc _ (List.mem_map.mpr ⟨c, hcm, rfl⟩))

theorem closeTypeModes_wellShaped {Δ : Bounds} {σ : CompareSubstitution}
    (h : σ.WellShaped Δ) : σ.closeTypeModes.WellShaped Δ := by
  intro entry he
  obtain ⟨⟨n,a⟩, ha, rfl⟩ := List.mem_map.mp he
  exact (a.wellShaped_subst_modes_iff _).mpr (h (n,a) ha)

theorem closeTypeModes_wellFormed {Δ : Bounds} {σ : CompareSubstitution}
    (hf : ComparisonModeRestriction.Fixed Δ σ.mode) (h : σ.WellFormedUnder Δ) :
    σ.closeTypeModes.WellFormedUnder Δ := by
  refine ⟨?_, h.modes⟩
  intro v
  rw [closeTypeModes_type]
  exact hf.type_defined (h.types v)

theorem closeTypeModes_domains {nt nm : Nat} {σ : CompareSubstitution}
    (h : σ.DomainsAbove nt nm) : σ.closeTypeModes.DomainsAbove nt nm := by
  refine ⟨?_, h.2⟩
  intro entry he
  obtain ⟨⟨n,a⟩, ha, rfl⟩ := List.mem_map.mp he
  exact h.1 (n,a) ha

theorem modesIdempotent_of_fixed_range {cutoff : Nat} {σ : CompareSubstitution}
    (hf : ∀v, v.index < cutoff → σ.mode v = .var v)
    (hi : ∀entry∈σ.modes, ∀v∈entry.2.vars, v.index < cutoff) : σ.ModesIdempotent := by
  intro v
  cases v with
  | rigid n => rfl
  | flex n =>
    cases he : σ.modes.lookup n with
    | none => simp [mode, he, ModExpr.subst]
    | some m =>
      obtain ⟨left, right, hx, _⟩ := List.lookup_eq_some_iff.mp he
      have hm := hi (n,m) (by simp [hx])
      simp only [mode, he, Option.getD_some]
      exact (m.subst_congr (fun v hv => hf v (hm v hv))).trans (ModExpr.subst_id m)

theorem ModesIdempotent.of_modes_eq {σ τ : CompareSubstitution}
    (h : σ.ModesIdempotent) (he : τ.modes = σ.modes) : τ.ModesIdempotent := by
  have hm : τ.mode = σ.mode := by funext v; cases v <;> simp [mode, he]
  intro v
  simpa only [hm] using h v

theorem closeTypeModes_keys (σ : CompareSubstitution) :
    σ.closeTypeModes.types.map Prod.fst = σ.types.map Prod.fst := by
  simp [closeTypeModes, List.map_map, Function.comp_def]

end ModalityInference.CompareSubstitution

namespace ModalityInference.ComparisonWitnessRestriction

theorem Supported.mode {p : SchemePreparation.Prepared} {σ : CompareSubstitution}
    (h : Supported p σ) {v : ModVar} (hv : v∈inputModes p) :
    (σ.mode v).vars ⊆ inputModes p := by
  cases v with
  | rigid n => simpa only [CompareSubstitution.mode, ModExpr.vars,
      Finset.singleton_subset_iff] using hv
  | flex n =>
    cases he : σ.modes.lookup n with
    | none => simpa only [CompareSubstitution.mode, he, Option.getD_none,
        ModExpr.vars, Finset.singleton_subset_iff] using hv
    | some m =>
      obtain ⟨left, right, hx, _⟩ := List.lookup_eq_some_iff.mp he
      simpa only [CompareSubstitution.mode, he, Option.getD_some] using
        h.2 (n,m) (by simp [hx])

theorem Supported.closeTypeModes {p : SchemePreparation.Prepared} {σ : CompareSubstitution}
    (h : Supported p σ) : Supported p σ.closeTypeModes := by
  refine ⟨?_, h.2⟩
  intro entry he
  obtain ⟨⟨n,a⟩, ha, rfl⟩ := List.mem_map.mp he
  exact (h.1 (n,a) ha).subst (types := CompareTy.var) (modes := σ.mode)
    (fun _ hv => hv) (fun _ hv => h.mode hv)

end ModalityInference.ComparisonWitnessRestriction

namespace ModalityInference.ComparisonPreparation

open ComparisonFixedModeWitness

theorem PreparedWitnessUnder.mode_fixed_context {ambient : Bounds} {source target : Scheme}
    {σ : CompareSubstitution}
    (h : PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ) :
    ComparisonModeRestriction.Fixed
      (SchemePreparation.prepare ambient source target).assumptions σ.mode := by
  refine ⟨fun η hη v => h.2.1.modes v η hη, ?_⟩
  intro v hv
  exact h.1.1.mode_fixed v ((mem_names v _).mp (prepared_assumptions ambient source target hv))

theorem PreparedWitnessUnder.closeTypeModes {ambient : Bounds} {source target : Scheme}
    {σ : CompareSubstitution}
    (h : PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ)
    (hi : σ.ModesIdempotent) :
    PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ.closeTypeModes := by
  let p := SchemePreparation.prepare ambient source target
  have hf := h.mode_fixed_context
  have ht : (CompareTy.ofTy p.targetType).subst CompareTy.var σ.mode = .ofTy p.targetType :=
    ComparisonModeRestriction.ofTy_fixed p.targetType (fun v hv =>
      h.1.1.mode_fixed v ((mem_names v _).mp (prepared_target ambient source target hv)))
  dsimp only [p] at ht
  refine ⟨⟨CompareSubstitution.closeTypeModes_domains h.1.1,
    CompareSubstitution.closeTypeModes_wellShaped h.1.2.1,
    CompareSubstitution.closeTypeModes_bounds hf hi _ h.1.2.2.1, ?_⟩,
    CompareSubstitution.closeTypeModes_wellFormed hf h.2.1, ?_⟩
  · simpa only [CompareSubstitution.closeTypeModes_ty hi, ht] using hf.algebra h.1.2.2.2
  · rw [CompareSubstitution.closeTypeModes_ty hi]
    exact hf.type_defined h.2.2

end ModalityInference.ComparisonPreparation

namespace ModalityInference.ComparisonFixedModeWitness

open ComparisonPreparation ComparisonInterpolation

theorem project_modesIdempotent (cutoff : Nat) (bounds : Bounds) (body : Ty)
    (σ : CompareSubstitution) : (project cutoff bounds body σ).ModesIdempotent :=
  CompareSubstitution.modesIdempotent_of_fixed_range
    (fun _ hv => project_mode_fixed σ hv) (project_fixedImages cutoff bounds body σ).2

theorem restrict_variable_support {Q : ModVar → Prop} (names : Finset ModVar)
    {v : ModVar} (hv : Q v) : ∀w∈(ComparisonModeRestriction.restrict names v).vars, Q w := by
  intro w hw
  by_cases hn : v∈names
  · simp only [ComparisonModeRestriction.restrict, if_pos hn, ModExpr.vars,
      Finset.mem_singleton] at hw
    exact hw ▸ hv
  · simp [ComparisonModeRestriction.restrict, hn, ModExpr.epsilon, ModExpr.vars] at hw

theorem project_supported {p : SchemePreparation.Prepared} {σ : CompareSubstitution}
    (h : ComparisonWitnessRestriction.Supported p σ) :
    ComparisonWitnessRestriction.Supported p (project p.firstMode p.sourceBounds p.sourceType σ) := by
  have hv : ∀v∈ComparisonWitnessRestriction.inputModes p,
      ∀w∈(σ.mode v).vars, w∈ComparisonWitnessRestriction.inputModes p := by
    intro v hv
    cases v with
    | rigid n => simpa only [CompareSubstitution.mode, ModExpr.vars, Finset.mem_singleton,
        forall_eq] using hv
    | flex n =>
      cases he : σ.modes.lookup n with
      | none => simpa only [CompareSubstitution.mode, he, Option.getD_none, ModExpr.vars,
          Finset.mem_singleton, forall_eq] using hv
      | some m =>
        obtain ⟨left, right, hx, _⟩ := List.lookup_eq_some_iff.mp he
        simpa only [CompareSubstitution.mode, he, Option.getD_some] using h.2 (n,m) (by simp [hx])
  constructor
  · intro entry he
    obtain ⟨⟨n,a⟩, ha, rfl⟩ := List.mem_map.mp he
    exact (h.1 (n,a) ha).subst (types := CompareTy.var)
      (modes := ComparisonModeRestriction.restrict (names p.firstMode))
      (fun _ hv => hv) (fun _ hv => restrict_variable_support _ hv)
  · intro entry he
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp he
    have hnin : ModVar.flex n∈ComparisonWitnessRestriction.inputModes p := by
      have := (mem_keys.mp hn).2
      simp only [inputModes, ComparisonWitnessRestriction.inputModes, Finset.mem_union] at *
      tauto
    apply ModExpr.support_subst
    exact fun v hv' => restrict_variable_support _ (hv _ hnin v hv')

theorem prepared_supported_fixed {ambient : Bounds} {source target : Scheme}
    {σ : CompareSubstitution}
    (h : PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ) :
    let p := SchemePreparation.prepare ambient source target
    ∃τ, PreparedWitnessUnder p τ ∧ ComparisonWitnessRestriction.Supported p τ ∧
      FixedImages p.firstMode τ ∧ τ.ModesIdempotent := by
  obtain ⟨σ', hw, _, _, hsp⟩ := ComparisonWitnessRestriction.prepared_supported_under h
  exact ⟨_, (prepared_project hw).1, project_supported hsp, (prepared_project hw).2,
    project_modesIdempotent _ _ _ _⟩

end ModalityInference.ComparisonFixedModeWitness
