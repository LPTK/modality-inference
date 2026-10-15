import ModalityInference.Proofs.ComparisonDefinedTotality
import ModalityInference.Proofs.ComparisonPropagationSetup

/-! Explicit instance guards retain every quantified type and modality in the
ordinary shape-template path. The optional partial-image preparations leave
these guarded binders unchanged. -/

namespace ModalityInference

theorem Scheme.fresh_type_at (s : Scheme) (hn : s.typeParams.Nodup) (nt nm : Nat)
    (i : Nat) (hi : i < s.typeParams.length) :
    (s.freshSubstitution nt nm).type (.flex s.typeParams[i]) = .var (.flex (nt + i)) := by
  cases he : (s.freshSubstitution nt nm).types.lookup s.typeParams[i] with
  | none =>
    exact False.elim ((lookup_fresh_none (by simpa [Scheme.freshSubstitution] using he))
      (List.getElem_mem hi))
  | some a =>
    obtain ⟨j, hj, rfl⟩ := lookup_fresh_some (xs := s.typeParams)
      (f := fun j => (.var (.flex (nt + j)) : Ty))
      (by simpa [Scheme.freshSubstitution] using he)
    have hj' := List.getElem?_eq_some_iff.mp hj
    have hji : j = i := hn.getElem_inj_iff.mp hj'.2
    subst j
    simp only [Substitution.type, he, Option.getD_some]

theorem Scheme.fresh_mode_at (s : Scheme) (hn : s.modParams.Nodup) (nt nm : Nat)
    (i : Nat) (hi : i < s.modParams.length) :
    (s.freshSubstitution nt nm).mode (.flex s.modParams[i]) = .var (.flex (nm + i)) := by
  cases he : (s.freshSubstitution nt nm).modes.lookup s.modParams[i] with
  | none =>
    exact False.elim ((lookup_fresh_none (by simpa [Scheme.freshSubstitution] using he))
      (List.getElem_mem hi))
  | some a =>
    obtain ⟨j, hj, rfl⟩ := lookup_fresh_some (xs := s.modParams)
      (f := fun j => (.var (.flex (nm + j)) : ModExpr))
      (by simpa [Scheme.freshSubstitution] using he)
    have hj' := List.getElem?_eq_some_iff.mp hj
    have hji : j = i := hn.getElem_inj_iff.mp hj'.2
    subst j
    simp only [Substitution.mode, he, Option.getD_some]

namespace SchemePreparation

theorem prepare_type_guard_at (ambient : Bounds) (source target : Scheme)
    (hn : source.typeParams.Nodup) (i : Nat) (hi : i < source.typeParams.length) :
    let p := prepare ambient source.requireDefinedInstances target
    Constraint.sub (.var (.flex (p.firstType + i))) (.var (.flex (p.firstType + i))) ∈ p.sourceBounds := by
  let p := prepare ambient source.requireDefinedInstances target
  have hg : Constraint.sub (.var (.flex source.typeParams[i])) (.var (.flex source.typeParams[i])) ∈
      source.requireDefinedInstances.bounds := by
    exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨_, List.getElem_mem hi, rfl⟩)))
  have he := source.requireDefinedInstances.fresh_type_at hn p.firstType p.firstMode i hi
  change p.sourceRenaming.type (.flex source.typeParams[i]) = .var (.flex (p.firstType + i)) at he
  change _ ∈ p.sourceRenaming.bounds source.requireDefinedInstances.bounds
  refine List.mem_map.mpr ⟨_, hg, ?_⟩
  simp only [Substitution.constraint, Constraint.subst, TypeExpr.subst]
  rw [he]

theorem prepare_mode_guard_at (ambient : Bounds) (source target : Scheme)
    (hn : source.modParams.Nodup) (i : Nat) (hi : i < source.modParams.length) :
    let p := prepare ambient source.requireDefinedInstances target
    Constraint.defined (.var (.flex (p.firstMode + i))) ∈ p.sourceBounds := by
  let p := prepare ambient source.requireDefinedInstances target
  have hg : Constraint.defined (.var (.flex source.modParams[i])) ∈
      source.requireDefinedInstances.bounds := by
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_map.mpr ⟨_, List.getElem_mem hi, rfl⟩))
  have he := source.requireDefinedInstances.fresh_mode_at hn p.firstType p.firstMode i hi
  change p.sourceRenaming.mode (.flex source.modParams[i]) = .var (.flex (p.firstMode + i)) at he
  change _ ∈ p.sourceRenaming.bounds source.requireDefinedInstances.bounds
  refine List.mem_map.mpr ⟨_, hg, ?_⟩
  simp only [Substitution.constraint, Constraint.subst, ModExpr.subst]
  rw [he]

theorem prepare_type_guard (ambient : Bounds) (source target : Scheme)
    (hn : source.typeParams.Nodup) (n : Nat)
    (hlo : (prepare ambient source.requireDefinedInstances target).firstType ≤ n)
    (hhi : n < (prepare ambient source.requireDefinedInstances target).nextType) :
    Constraint.sub (.var (.flex n)) (.var (.flex n)) ∈
      (prepare ambient source.requireDefinedInstances target).sourceBounds := by
  let p := prepare ambient source.requireDefinedInstances target
  change p.firstType ≤ n at hlo
  change n < p.nextType at hhi
  have hlen : p.nextType = p.firstType + source.typeParams.length := rfl
  have hi : n - p.firstType < source.typeParams.length := by omega
  have he : p.firstType + (n - p.firstType) = n := by omega
  have hg := prepare_type_guard_at ambient source target hn (n - p.firstType) hi
  change Constraint.sub (.var (.flex (p.firstType + (n - p.firstType))))
    (.var (.flex (p.firstType + (n - p.firstType)))) ∈ p.sourceBounds at hg
  simpa only [he] using hg

theorem prepare_mode_guard (ambient : Bounds) (source target : Scheme)
    (hn : source.modParams.Nodup) (n : Nat)
    (hlo : (prepare ambient source.requireDefinedInstances target).firstMode ≤ n)
    (hhi : n < (prepare ambient source.requireDefinedInstances target).nextMode) :
    Constraint.defined (.var (.flex n)) ∈
      (prepare ambient source.requireDefinedInstances target).sourceBounds := by
  let p := prepare ambient source.requireDefinedInstances target
  change p.firstMode ≤ n at hlo
  change n < p.nextMode at hhi
  have hlen : p.nextMode = p.firstMode + source.modParams.length := rfl
  have hi : n - p.firstMode < source.modParams.length := by omega
  have he : p.firstMode + (n - p.firstMode) = n := by omega
  have hg := prepare_mode_guard_at ambient source target hn (n - p.firstMode) hi
  change Constraint.defined (.var (.flex (p.firstMode + (n - p.firstMode)))) ∈ p.sourceBounds at hg
  simpa only [he] using hg

/-- The prepared source explicitly constrains every quantified image. -/
def BinderGuards (p : Prepared) : Prop :=
  (∀ n, p.firstType ≤ n → n < p.nextType →
    Constraint.sub (.var (.flex n)) (.var (.flex n)) ∈ p.sourceBounds) ∧
  (∀ n, p.firstMode ≤ n → n < p.nextMode →
    Constraint.defined (.var (.flex n)) ∈ p.sourceBounds)

theorem prepare_binderGuards (ambient : Bounds) (source target : Scheme)
    (ht : source.typeParams.Nodup) (hm : source.modParams.Nodup) :
    BinderGuards (prepare ambient source.requireDefinedInstances target) :=
  ⟨prepare_type_guard ambient source target ht, prepare_mode_guard ambient source target hm⟩

end SchemePreparation

namespace ComparisonChecker
open SchemePreparation

theorem bareEligible_nil {p : Prepared} (hg : BinderGuards p) :
    ComparisonPartial.eligible p = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro n hn
  obtain ⟨hr, hb, _⟩ := ComparisonPartial.mem_eligible.mp hn
  have hr := List.mem_range'_1.mp hr
  exact hb _ (hg.1 n hr.1 (by omega)) (by simp [Constraint.typeVars, TypeExpr.typeVars])

theorem modeEligible_nil {p : Prepared} (hg : BinderGuards p) :
    ComparisonPartialModes.eligible p = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro n hn
  obtain ⟨hr, hb⟩ := ComparisonPartialModes.mem_eligible.mp hn
  have hr := List.mem_range'_1.mp hr
  exact hb _ (hg.2 n hr.1 (by omega)) (by simp [Constraint.modVars, ModExpr.vars])

theorem absorption_owners_nil {p : Prepared} (hg : BinderGuards p) (total : ModExpr → Bool) :
    (ComparisonAbsorption.plan p total).owners = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro pair hp
  have hs := (ComparisonAbsorption.scopeCheck_spec _ _).mp
    (ComparisonAbsorption.plan_spec p total).1 pair hp
  exact hs.2.2.1 _ (hg.1 pair.1 hs.1.1 hs.1.2)
    (by simp [Constraint.typeVars, TypeExpr.typeVars])

theorem absorption_body_eq {p : Prepared} (hg : BinderGuards p) (total : ModExpr → Bool) :
    (ComparisonAbsorption.plan p total).body = p.sourceType := by
  have hbody := (ComparisonAbsorption.plan_spec p total).2
  rw [absorption_owners_nil hg, ComparisonAbsorption.rewrite_empty] at hbody
  exact (Option.some.inj hbody).symm

theorem annotations_trivial {p : Prepared} (hg : BinderGuards p) (total : ModExpr → Bool) :
    (ComparisonAnnotations.prepare p total).images = [] ∧
    (ComparisonAnnotations.prepare p total).bounds = [] ∧
    (ComparisonAnnotations.prepare p total).nextMode = p.nextMode := by
  simp only [ComparisonAnnotations.prepare, modeEligible_nil hg,
    List.filter_nil, ComparisonPartialModes.adapt, List.zipIdx_nil,
    List.filterMap_nil, List.map_nil, List.flatMap_nil, List.length_nil, Nat.add_zero,
    and_self]

end ComparisonChecker
end ModalityInference
