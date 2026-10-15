import ModalityInference.Proofs.ComparisonPreparation
import ModalityInference.Proofs.ComparisonAlgebra

/-! Reconstruction of prepared comparison obligations in the guarded algebra. -/
namespace ModalityInference

theorem CompareSubstitution.WellShaped.type {Δ : Bounds} {σ : CompareSubstitution}
    (h : σ.WellShaped Δ) (v : TypeVar) : (σ.type v).WellShaped Δ := by
  cases v
  all_goals simp only [CompareSubstitution.type, CompareTy.WellShaped]
  case flex n =>
    cases he : σ.types.lookup n <;> simp only [Option.getD]
    · trivial
    · obtain ⟨left, right, hx, _⟩ := List.lookup_eq_some_iff.mp he
      exact h (n, _) (by simp [hx])

theorem CompareSubstitution.WellShaped.ty {Δ : Bounds} {σ : CompareSubstitution}
    (h : σ.WellShaped Δ) (a : Ty) : (σ.ty a).WellShaped Δ := by
  induction a <;> simp_all [CompareSubstitution.ty, CompareTy.ofTy, CompareTy.subst,
    CompareTy.WellShaped, h.type]

namespace ComparisonPreparation

theorem reconstruct_wellShaped {p : Prepared} {action : CompareSubstitution} {Δ : Bounds}
    (h : action.WellShaped Δ) : (reconstruct p action).WellShaped Δ := by
  simp only [CompareSubstitution.WellShaped, reconstruct, List.forall_mem_map]
  exact fun entry _ => h.ty entry.2

private theorem equal_entails (σ : CompareSubstitution) (Δ : Bounds) (v : TypeVar) (a : Ty) :
    AlgebraEntails Δ (σ.constraint (.equal v a)) ↔
      AlgebraEntails Δ (.sub (σ.type v) (σ.ty a)) ∧
      AlgebraEntails Δ (.sub (σ.ty a) (σ.type v)) := by
  cases v
  case rigid =>
    simp [CompareSubstitution.constraint, CompareSubstitution.type, AlgebraEntails,
      CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels, and_left_comm, and_comm]
  case flex n =>
    cases he : σ.types.lookup n <;>
      simp [CompareSubstitution.constraint, CompareSubstitution.type, he, AlgebraEntails,
        CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels, and_left_comm, and_comm]

theorem reconstruct_algebra_constraint (p : Prepared) (action : CompareSubstitution)
    (c : Constraint) (Δ : Bounds)
    (ht : ∀ v ∈ c.typeVars, action.type v = .var v)
    (hm : ∀ v ∈ c.modVars, action.mode v = .var v) :
    AlgebraEntails Δ ((reconstruct p action).constraint c) ↔
      AlgebraEntails Δ (action.constraint (p.sourceRenaming.constraint c)) := by
  cases c <;> simp only [Constraint.typeVars, Constraint.modVars, Finset.mem_union,
    Finset.mem_insert, or_imp, forall_and, forall_eq] at ht hm
  case sub a b | equiv a b =>
    simp only [CompareSubstitution.constraint, Substitution.constraint, Constraint.subst,
      reconstruct_ty p action a ht.1 hm.1, reconstruct_ty p action b ht.2 hm.2,
      Substitution.ty]
  case mode a b =>
    simp only [CompareSubstitution.constraint, Substitution.constraint, Constraint.subst,
      reconstruct_modeExpr p action a hm.1, reconstruct_modeExpr p action b hm.2]
  case defined m =>
    simp only [CompareSubstitution.constraint, Substitution.constraint, Constraint.subst,
      reconstruct_modeExpr p action m hm]
  case equal v t =>
    rw [equal_entails, reconstruct_type p action v ht.1,
      reconstruct_ty p action t ht.2 hm]
    cases v <;> simp only [Substitution.constraint, Substitution.type]
    case rigid n => exact (equal_entails action Δ (.rigid n) (p.sourceRenaming.ty t)).symm
    case flex n =>
      cases he : p.sourceRenaming.types.lookup n <;> simp only [Option.getD]
      case none => exact (equal_entails action Δ (.flex n) (p.sourceRenaming.ty t)).symm
      case some => simp [CompareSubstitution.constraint, AlgebraEntails,
        and_left_comm, and_comm]

theorem reconstruct_algebra_bounds (p : Prepared) (action : CompareSubstitution) (cs Δ : Bounds)
    (ht : ∀ v ∈ cs.typeVars, action.type v = .var v)
    (hm : ∀ v ∈ cs.modVars, action.mode v = .var v) :
    AlgebraEntailsAll Δ ((reconstruct p action).bounds cs) ↔
      AlgebraEntailsAll Δ (action.bounds (p.sourceRenaming.bounds cs)) := by
  simp only [AlgebraEntailsAll, CompareSubstitution.bounds, Substitution.bounds,
    List.forall_mem_map]
  exact forall_congr' fun c => forall_congr' fun hc =>
    reconstruct_algebra_constraint p action c Δ
      (fun v hv => ht v ((cs.mem_typeVars_iff v).mpr ⟨c, hc, hv⟩))
      (fun v hv => hm v ((cs.mem_modVars_iff v).mpr ⟨c, hc, hv⟩))

/-- A well-shaped solution of every prepared obligation reconstructs a witness
for the original schemes, with precisely the source quantifiers as its domain. -/
theorem reconstruct_algebra_sound (ambient : Bounds) (source target : Scheme)
    (action : CompareSubstitution)
    (ht : ∀ v ∈ source.body.typeVars ∪ source.bounds.typeVars, action.type v = .var v)
    (hm : ∀ v ∈ source.body.modVars ∪ source.bounds.modVars, action.mode v = .var v)
    (hs : action.WellShaped (prepare ambient source target).assumptions)
    (hb : AlgebraEntailsAll (prepare ambient source target).assumptions
      (action.bounds (prepare ambient source target).sourceBounds))
    (hbody : AlgebraSubtype (prepare ambient source target).assumptions
      (action.ty (prepare ambient source target).sourceType)
      (CompareTy.ofTy (prepare ambient source target).targetType)) :
    AlgebraSubsumes ambient source target := by
  refine ⟨reconstruct (prepare ambient source target) action,
    reconstruct_instantiates ambient source target action, reconstruct_wellShaped hs, ?_, ?_⟩
  · exact (reconstruct_algebra_bounds (prepare ambient source target) action source.bounds
      (prepare ambient source target).assumptions
      (fun v hv => ht v (Finset.mem_union_right _ hv))
      (fun v hv => hm v (Finset.mem_union_right _ hv))).mpr hb
  · simpa only [reconstruct_ty (prepare ambient source target) action source.body
      (fun v hv => ht v (Finset.mem_union_left _ hv))
      (fun v hv => hm v (Finset.mem_union_left _ hv))] using hbody

end ComparisonPreparation

end ModalityInference
