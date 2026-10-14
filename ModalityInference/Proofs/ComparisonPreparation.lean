import ModalityInference.ComparisonPreparation
import ModalityInference.Proofs.ComparisonTypes
import ModalityInference.Proofs.SchemePreparation
import ModalityInference.Proofs.SkolemSubstitution

namespace ModalityInference.ComparisonPreparation

private theorem equal_entails (σ : CompareSubstitution) (Δ : Bounds) (v : TypeVar) (a : Ty) :
    CompareEntails Δ (σ.constraint (.equal v a)) ↔
      CompareEntails Δ (.sub (σ.type v) (σ.ty a)) ∧
      CompareEntails Δ (.sub (σ.ty a) (σ.type v)) := by
  cases v
  case rigid =>
    simp [CompareSubstitution.constraint, CompareSubstitution.type, CompareEntails,
      CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels, and_left_comm, and_comm]
  case flex n =>
    cases he : σ.types.lookup n <;>
      simp [CompareSubstitution.constraint, CompareSubstitution.type, he, CompareEntails,
        CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels, and_left_comm, and_comm]

theorem reconstruct_type (p : Prepared) (action : CompareSubstitution) (v : TypeVar)
    (hv : action.type v = .var v) :
    (reconstruct p action).type v = action.ty (p.sourceRenaming.type v) := by
  cases v
  case rigid => rfl
  case flex n =>
    simp only [reconstruct, CompareSubstitution.type, Substitution.type, lookup_map_values]
    cases p.sourceRenaming.types.lookup n <;>
      simp [CompareSubstitution.ty, CompareTy.ofTy, CompareTy.subst, hv]

theorem reconstruct_mode (p : Prepared) (action : CompareSubstitution) (v : ModVar)
    (hv : action.mode v = .var v) :
    (reconstruct p action).mode v = (p.sourceRenaming.mode v).subst action.mode := by
  cases v
  case rigid => rfl
  case flex n =>
    simp only [reconstruct, CompareSubstitution.mode, Substitution.mode, lookup_map_values]
    cases p.sourceRenaming.modes.lookup n <;> simp [ModExpr.subst, hv]

theorem reconstruct_modeExpr (p : Prepared) (action : CompareSubstitution) (m : ModExpr)
    (hm : ∀ v ∈ m.vars, action.mode v = .var v) :
    m.subst (reconstruct p action).mode = (m.subst p.sourceRenaming.mode).subst action.mode := by
  rw [ModExpr.subst_subst]
  exact m.subst_congr fun v hv => reconstruct_mode p action v (hm v hv)

theorem reconstruct_ty (p : Prepared) (action : CompareSubstitution) (t : Ty)
    (ht : ∀ v ∈ t.typeVars, action.type v = .var v)
    (hm : ∀ v ∈ t.modVars, action.mode v = .var v) :
    (reconstruct p action).ty t = action.ty (p.sourceRenaming.ty t) := by
  induction t <;> simp_all [CompareSubstitution.ty, CompareTy.ofTy, CompareTy.subst,
    Substitution.ty, TypeExpr.subst, TypeExpr.typeVars, TypeExpr.modVars, or_imp, forall_and]
  case var v => exact reconstruct_type p action v ht
  case modal a m ih => exact reconstruct_modeExpr p action m hm.2

theorem reconstruct_constraint (p : Prepared) (action : CompareSubstitution)
    (c : Constraint) (Δ : Bounds)
    (ht : ∀ v ∈ c.typeVars, action.type v = .var v)
    (hm : ∀ v ∈ c.modVars, action.mode v = .var v) :
    CompareEntails Δ ((reconstruct p action).constraint c) ↔
      CompareEntails Δ (action.constraint (p.sourceRenaming.constraint c)) := by
  cases c <;> simp only [Constraint.typeVars, Constraint.modVars, Finset.mem_union,
    Finset.mem_insert, or_imp, forall_and, forall_eq] at ht hm
  case equal v t =>
    rw [equal_entails, reconstruct_type p action v ht.1,
      reconstruct_ty p action t ht.2 hm]
    cases v <;> simp only [Substitution.constraint, Substitution.type]
    case rigid n => exact (equal_entails action Δ (.rigid n) (p.sourceRenaming.ty t)).symm
    case flex n =>
      cases he : p.sourceRenaming.types.lookup n <;> simp only [Option.getD]
      case none => exact (equal_entails action Δ (.flex n) (p.sourceRenaming.ty t)).symm
      case some => simp [CompareSubstitution.constraint, CompareEntails,
        and_left_comm, and_comm]
  case sub a b | equiv a b =>
    simp only [CompareSubstitution.constraint, Substitution.constraint, Constraint.subst,
      reconstruct_ty p action a ht.1 hm.1, reconstruct_ty p action b ht.2 hm.2]
    rfl
  case mode a b =>
    simp only [CompareSubstitution.constraint, Substitution.constraint, Constraint.subst,
      reconstruct_modeExpr p action a hm.1, reconstruct_modeExpr p action b hm.2]
  case defined m =>
    simp only [CompareSubstitution.constraint, Substitution.constraint, Constraint.subst,
      reconstruct_modeExpr p action m hm]

theorem reconstruct_bounds (p : Prepared) (action : CompareSubstitution) (cs Δ : Bounds)
    (ht : ∀ v ∈ cs.typeVars, action.type v = .var v)
    (hm : ∀ v ∈ cs.modVars, action.mode v = .var v) :
    CompareEntailsAll Δ ((reconstruct p action).bounds cs) ↔
      CompareEntailsAll Δ (action.bounds (p.sourceRenaming.bounds cs)) := by
  simp only [CompareEntailsAll, CompareSubstitution.bounds, Substitution.bounds,
    List.forall_mem_map]
  exact forall_congr' fun c => forall_congr' fun hc =>
    reconstruct_constraint p action c Δ
      (fun v hv => ht v ((cs.mem_typeVars_iff v).mpr ⟨c, hc, hv⟩))
      (fun v hv => hm v ((cs.mem_modVars_iff v).mpr ⟨c, hc, hv⟩))

theorem reconstruct_instantiates (ambient : Bounds) (source target : Scheme)
    (action : CompareSubstitution) :
    CompareInstantiates source (reconstruct (prepare ambient source target) action) := by
  simp only [CompareInstantiates, reconstruct, List.map_map, Function.comp_def]
  exact source.freshSubstitution_instantiates _ _ false

/-- A solution of the fresh obligations reconstructs exactly the source's
quantifiers, preserving its guarded bounds and separate body comparison. -/
theorem reconstruct_sound (ambient : Bounds) (source target : Scheme) (action : CompareSubstitution)
    (ht : ∀ v ∈ source.body.typeVars ∪ source.bounds.typeVars, action.type v = .var v)
    (hm : ∀ v ∈ source.body.modVars ∪ source.bounds.modVars, action.mode v = .var v)
    (hb : CompareEntailsAll (prepare ambient source target).assumptions
      (action.bounds (prepare ambient source target).sourceBounds))
    (hbody : CompareSubtype (prepare ambient source target).assumptions
      (action.ty (prepare ambient source target).sourceType)
      (CompareTy.ofTy (prepare ambient source target).targetType)) :
    CompareSubsumes ambient source target := by
  refine ⟨reconstruct (prepare ambient source target) action,
    reconstruct_instantiates ambient source target action, ?_, ?_⟩
  · exact (reconstruct_bounds (prepare ambient source target) action source.bounds
      (prepare ambient source target).assumptions
      (fun v hv => ht v (Finset.mem_union_right _ hv))
      (fun v hv => hm v (Finset.mem_union_right _ hv))).mpr hb
  · simpa only [reconstruct_ty (prepare ambient source target) action source.body
      (fun v hv => ht v (Finset.mem_union_left _ hv))
      (fun v hv => hm v (Finset.mem_union_left _ hv))] using hbody

end ModalityInference.ComparisonPreparation
