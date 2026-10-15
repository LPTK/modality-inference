import ModalityInference.Proofs.ComparisonChecker
import ModalityInference.Proofs.ComparisonAnnotations
import ModalityInference.Proofs.ComparisonSkeleton
import ModalityInference.Proofs.ComparisonReduction
import ModalityInference.Proofs.SchemeModeSynthesis
import ModalityInference.Proofs.ComparisonContext
import ModalityInference.Proofs.ComparisonCapsuleContext

/-! Fresh-domain invariants for the assembled comparison witness. -/
namespace ModalityInference

def CompareSubstitution.DomainsAbove (σ : CompareSubstitution) (firstType firstMode : Nat) : Prop :=
  (∀ entry ∈ σ.types, firstType ≤ entry.1) ∧ ∀ entry ∈ σ.modes, firstMode ≤ entry.1

theorem CompareSubstitution.DomainsAbove.type_fixed {σ : CompareSubstitution} {nt nm : Nat}
    (h : σ.DomainsAbove nt nm) (v : TypeVar) (hv : v.index < nt) : σ.type v = .var v := by
  cases v with
  | rigid => rfl
  | flex n =>
    have hl : σ.types.lookup n = none := List.lookup_eq_none_iff.mpr (by
      intro entry he
      have hn := h.1 entry he
      apply bne_iff_ne.mpr
      intro heq
      simp only [TypeVar.index] at hv
      omega)
    simp [CompareSubstitution.type, hl]

theorem CompareSubstitution.DomainsAbove.mode_fixed {σ : CompareSubstitution} {nt nm : Nat}
    (h : σ.DomainsAbove nt nm) (v : ModVar) (hv : v.index < nm) : σ.mode v = .var v := by
  cases v with
  | rigid => rfl
  | flex n =>
    apply Substitution.mode_fresh ({ modes := σ.modes } : Substitution)
    intro hn
    obtain ⟨entry, he, heq⟩ := List.mem_map.mp hn
    have hb := h.2 entry he
    simp only [ModVar.index] at hv
    omega

namespace ComparisonExactContext

theorem finish_domainsAbove {before : Substitution} {after : CompareSubstitution} {nt nm : Nat}
    (hb : (CompareSubstitution.ofSubstitution before).DomainsAbove nt nm)
    (ha : after.DomainsAbove nt nm) : (finish before after).DomainsAbove nt nm := by
  constructor <;> intro entry he
  · simp only [finish, List.mem_append, List.mem_map, List.mem_filter] at he
    rcases he with ⟨pair, hp, rfl⟩ | ⟨he, _⟩
    · exact hb.1 (pair.1, CompareTy.ofTy pair.2) (List.mem_map.mpr ⟨pair, hp, rfl⟩)
    · exact ha.1 entry he
  · simp only [finish, Substitution.compose, List.mem_append, List.mem_map, List.mem_filter] at he
    rcases he with ⟨pair, hp, rfl⟩ | ⟨he, _⟩
    · exact hb.2 pair hp
    · exact ha.2 entry he

theorem Scoped.domainsAbove {p : Prepared} {before : Substitution} (h : Scoped p before) :
    (CompareSubstitution.ofSubstitution before).DomainsAbove p.firstType p.firstMode := by
  constructor
  · intro entry he
    obtain ⟨⟨name, image⟩, hi, rfl⟩ := List.mem_map.mp he
    have hk := (h.1 name image hi).1
    simp only [ComparisonInstance.typeAllowed, Bool.and_eq_true, decide_eq_true_eq] at hk
    exact hk.1
  · intro entry he
    have hk := (h.2 entry.1 entry.2 he).1
    simp only [ComparisonInstance.modeAllowed, Bool.and_eq_true, decide_eq_true_eq] at hk
    exact hk.1

end ComparisonExactContext

theorem Substitution.compose_domainsAbove {before after : Substitution} {nt nm : Nat}
    (hb : (CompareSubstitution.ofSubstitution before).DomainsAbove nt nm)
    (ha : (CompareSubstitution.ofSubstitution after).DomainsAbove nt nm) :
    (CompareSubstitution.ofSubstitution (after.compose before)).DomainsAbove nt nm := by
  constructor <;> intro entry he
  · obtain ⟨pair, hp, rfl⟩ := List.mem_map.mp he
    simp only [Substitution.compose, List.mem_append, List.mem_map, List.mem_filter] at hp
    rcases hp with ⟨old, ho, rfl⟩ | ⟨hp, _⟩
    · exact hb.1 (old.1, CompareTy.ofTy old.2) (List.mem_map.mpr ⟨old, ho, rfl⟩)
    · exact ha.1 _ (List.mem_map.mpr ⟨pair, hp, rfl⟩)
  · simp only [CompareSubstitution.ofSubstitution, Substitution.compose,
      List.mem_append, List.mem_map, List.mem_filter] at he
    rcases he with ⟨old, ho, rfl⟩ | ⟨he, _⟩
    · exact hb.2 old ho
    · exact ha.2 entry he

theorem ComparisonContext.Scoped.domainsAbove {p : ComparisonContext.Prepared}
    {before : Substitution} (h : ComparisonContext.Scoped p before) :
    (CompareSubstitution.ofSubstitution before).DomainsAbove p.firstType p.firstMode := by
  apply ComparisonExactContext.Scoped.domainsAbove
  exact ⟨by simp [h.1], h.2⟩

namespace ComparisonReduction

theorem prepare_partial_domain {fuel p templates bare known shared result}
    (h : prepare fuel p templates bare known shared = .success result) :
    result.partialTypes.map Prod.fst = bare := by
  simp only [prepare, bind, RunResult.bind] at h
  split at h
  · rw [run_partialTypes h]
    simp [ComparisonPartial.reduceBare, List.map_map, Function.comp_def]
  · contradiction
  · contradiction

end ComparisonReduction

theorem ComparisonInstance.run_domainsAbove {fuel p result}
    (h : ComparisonInstance.run fuel p = some result) :
    (CompareSubstitution.ofSubstitution result.action).DomainsAbove p.firstType p.firstMode := by
  have hd := ComparisonInstance.candidate_domain (ComparisonInstance.run_spec h).1
  constructor <;> intro entry he
  · obtain ⟨⟨name, image⟩, hp, rfl⟩ := List.mem_map.mp he
    change p.firstType ≤ name
    have hn := List.mem_map_of_mem (f := Prod.fst) hp
    rw [hd.1] at hn
    simp only [List.mem_range'] at hn
    omega
  · have hn := List.mem_map_of_mem (f := Prod.fst) he
    change entry.1 ∈ result.action.modes.map Prod.fst at hn
    rw [hd.2] at hn
    simp only [List.mem_range'] at hn
    omega

namespace ComparisonChecker

private theorem bare_domain_lower {p : SchemePreparation.Prepared}
    {total : ModExpr → Bool} {shared : Bool} {name : Nat}
    (h : name ∈ if shared then ComparisonBody.eligible p total else ComparisonPartial.eligible p) :
    p.firstType ≤ name := by
  split at h
  all_goals have hn := (List.mem_filter.mp h).1
  all_goals simp only [List.mem_range'] at hn
  all_goals omega

theorem absorption_domain_lower {p : SchemePreparation.Prepared}
    {total : ModExpr → Bool} {entry : Nat × ModExpr}
    (h : entry ∈ (ComparisonAbsorption.plan p total).action.modes) :
    p.firstMode ≤ entry.1 := by
  simp only [ComparisonAbsorption.Result.action, List.mem_map] at h
  obtain ⟨name, hn, rfl⟩ := h
  simp only [ComparisonAbsorption.Result.modes, ComparisonAbsorption.modes,
    List.mem_dedup, List.mem_map] at hn
  obtain ⟨pair, hp, rfl⟩ := hn
  exact ((ComparisonAbsorption.scopeCheck_spec _ _).mp
    (ComparisonAbsorption.plan_spec p total).1 pair hp).2.1.1

theorem annotations_domain_lower {p : SchemePreparation.Prepared}
    {total : ModExpr → Bool} {entry : Nat × ModExpr}
    (h : entry ∈ (ComparisonAnnotations.prepare p total).images) :
    p.firstMode ≤ entry.1 := by
  have hn := (ComparisonPartialModes.mem_eligible.mp
    (ComparisonAnnotations.prepare_domain (List.mem_map.mpr ⟨entry, h, rfl⟩))).1
  simp only [List.mem_range'] at hn
  omega

theorem propagate_domains {fuel p shapes shared before e}
    (hb : (CompareSubstitution.ofSubstitution before).DomainsAbove p.firstType p.firstMode)
    (h : propagate fuel p shapes shared before = .success e) :
    ∃ action, e.substitution = ComparisonPreparation.reconstruct p action ∧
      e.obligations = action.bounds p.sourceBounds ∧
      e.body = (action.ty p.sourceType, CompareTy.ofTy p.targetType) ∧
      action.DomainsAbove p.firstType p.firstMode := by
  simp only [propagate, bind, pure, RunResult.bind] at h
  repeat' first | contradiction | cases h | split at h
  all_goals refine ⟨_, rfl, rfl, rfl, ?_⟩
  all_goals apply ComparisonExactContext.finish_domainsAbove hb
  all_goals rename_i _ known hknown _ reduced hred _ types htypes _ modes hmodes _ report hreport hv
  all_goals have hpd := ComparisonReduction.prepare_partial_domain hred
  all_goals have hmd := (SchemeModeSynthesis.run_domain hmodes).2.1
  constructor
  · intro entry he
    simp only [List.mem_map, List.mem_append] at he
    obtain ⟨pair, hp, rfl⟩ := he
    rcases hp with hp | ⟨old, hp, rfl⟩
    · have hn := List.mem_map_of_mem (f := Prod.fst) hp
      rw [hpd] at hn
      have hx := bare_domain_lower (shared := shared) (List.mem_filter.mp hn).1
      exact hx
    · have hn := List.mem_map_of_mem (f := Prod.fst) hp
      rw [ComparisonSkeleton.allocate_domain] at hn
      have hr := (List.mem_filter.mp hn).1
      simp only [List.mem_range'] at hr
      omega

  · intro entry he
    simp only [List.mem_append, List.mem_map] at he
    rcases he with (hp | ⟨old, hp, rfl⟩) | hp
    · have hn := absorption_domain_lower hp
      exact hn
    · have hn := annotations_domain_lower hp
      exact hn
    · have hn := List.mem_map_of_mem (f := Prod.fst) hp
      rw [hmd] at hn
      have hr := (List.mem_filter.mp hn).1
      simp only [List.mem_range'] at hr
      omega

theorem variants_domains {fuel p shapes before e}
    (hb : (CompareSubstitution.ofSubstitution before).DomainsAbove p.firstType p.firstMode)
    (h : variants fuel p shapes before = .success e) :
    ∃ action, e.substitution = ComparisonPreparation.reconstruct p action ∧
      e.obligations = action.bounds p.sourceBounds ∧
      e.body = (action.ty p.sourceType, CompareTy.ofTy p.targetType) ∧
      action.DomainsAbove p.firstType p.firstMode := by
  cases hp : propagate fuel p shapes false before <;> simp only [variants, hp] at h
  case success => cases h; exact propagate_domains hb hp
  case exhausted => contradiction
  case rejected reason =>
    cases hq : propagate fuel p shapes true before <;> simp only [hq] at h
    case success => cases h; exact propagate_domains hb hq
    all_goals contradiction

theorem refineContexts_domains {fuel p shapes before e}
    (hb : (CompareSubstitution.ofSubstitution before).DomainsAbove p.firstType p.firstMode)
    (h : refineContexts fuel p shapes before = .success e) :
    ∃ action, e.substitution = ComparisonPreparation.reconstruct p action ∧
      e.obligations = action.bounds p.sourceBounds ∧
      e.body = (action.ty p.sourceType, CompareTy.ofTy p.targetType) ∧
      action.DomainsAbove p.firstType p.firstMode := by
  cases hv : variants fuel p shapes before <;> simp only [refineContexts, hv] at h
  case success => cases h; exact variants_domains hb hv
  case exhausted => contradiction
  case rejected =>
    simp only [bind, RunResult.bind] at h
    repeat' first
      | contradiction
      | exact variants_domains hb h
      | (refine variants_domains (Substitution.compose_domainsAbove hb ?_) h
         first
         | (have hs := ComparisonContext.prepare_scoped (by assumption); exact hs.domainsAbove)
         | (have hs := ComparisonExactContext.prepare_scoped (by assumption); exact hs.domainsAbove))
      | split at h

theorem core_domains {fuel source target e}
    (h : core fuel source target = .success e) :
    let p := SchemePreparation.prepare [] source target
    ∃ action, e.substitution = ComparisonPreparation.reconstruct p action ∧
      e.obligations = action.bounds p.sourceBounds ∧
      e.body = (action.ty p.sourceType, CompareTy.ofTy p.targetType) ∧
      action.DomainsAbove p.firstType p.firstMode := by
  simp only [core, bind, pure, RunResult.bind] at h
  repeat' first
    | contradiction
    | (refine refineContexts_domains ?_ h
       first
       | exact (ComparisonExactContext.neutral_scoped _).domainsAbove
       | simp [CompareSubstitution.DomainsAbove, CompareSubstitution.ofSubstitution])
    | split at h
  cases h
  refine ⟨_, rfl, rfl, rfl, ?_⟩
  rename_i result hi
  exact ComparisonInstance.run_domainsAbove (ComparisonInstance.attempt_some_iff.mp hi)

theorem partial_action_domains {fuel p result}
    (h : ComparisonPartialPropagation.attempt fuel p = .success (some result)) :
    result.action.DomainsAbove p.firstType p.firstMode := by
  rw [(ComparisonPartialPropagation.attempt_spec h).action_eq]
  constructor
  · rintro entry he
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp he
    obtain ⟨i, _, rfl⟩ := List.mem_range'.mp hn
    simp
  · simp [ComparisonPartialPropagation.action]

theorem capsuleCore_domains {fuel source target e}
    (h : capsuleCore fuel source target = .success e) :
    let p := SchemePreparation.prepare [] source target
    ∃ action, e.substitution = ComparisonPreparation.reconstruct p action ∧
      e.obligations = action.bounds p.sourceBounds ∧
      e.body = (action.ty p.sourceType, CompareTy.ofTy p.targetType) ∧
      action.DomainsAbove p.firstType p.firstMode := by
  simp only [capsuleCore, bind, RunResult.bind] at h
  repeat' first | contradiction | split at h
  exact variants_domains
    (ComparisonCapsuleContext.prepare_scoped (by assumption)).1.domainsAbove h

theorem run_domains {fuel source target e}
    (h : run fuel source target = .success e) :
    let p := SchemePreparation.prepare [] source target
    ∃ action, e.substitution = ComparisonPreparation.reconstruct p action ∧
      e.obligations = action.bounds p.sourceBounds ∧
      e.body = (action.ty p.sourceType, CompareTy.ofTy p.targetType) ∧
      action.DomainsAbove p.firstType p.firstMode := by
  cases hc : core fuel source target <;> simp only [run, hc] at h
  case success => cases h; exact core_domains hc
  case exhausted => contradiction
  case rejected reason =>
    cases hp : ComparisonPartialPropagation.attempt fuel
        (SchemePreparation.prepare [] source target) <;>
      simp only [hp, bind, pure, RunResult.bind] at h
    case success result =>
      cases result with
      | none =>
        cases hs : capsuleCore fuel source target <;> simp only [hs] at h
        case success => cases h; exact capsuleCore_domains hs
        all_goals contradiction
      | some result => cases h; exact ⟨result.action, rfl, rfl, rfl, partial_action_domains hp⟩
    all_goals contradiction

end ComparisonChecker

end ModalityInference
