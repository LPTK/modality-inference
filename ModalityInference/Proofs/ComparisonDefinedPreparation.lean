import ModalityInference.Proofs.ComparisonDefinedInstances
import ModalityInference.Proofs.ComparisonPreparationComplete

/-! Freshening preserves the defined image and body conditions of admissible
comparison instances. -/
namespace ModalityInference.ComparisonPreparation

def PreparedWitnessUnder (p : Prepared) (action : CompareSubstitution) : Prop :=
  PreparedWitness p action ∧ action.WellFormedUnder p.assumptions ∧
    (action.ty p.sourceType).DefinedUnder p.assumptions

theorem liftWitness_wellFormedUnder {p : Prepared} {source : Scheme}
    {σ : CompareSubstitution} {Δ : Bounds} (h : σ.WellFormedUnder Δ) :
    (liftWitness p source σ).WellFormedUnder Δ := by
  apply CompareSubstitution.wellFormedUnder_of_images
  · simp only [liftWitness, List.forall_mem_map]
    exact fun _ _ => h.types _
  · simp only [liftWitness, List.forall_mem_map]
    exact fun _ _ => h.modes _

theorem reconstruct_wellFormedUnder {ambient : Bounds} {source target : Scheme}
    {action : CompareSubstitution} {Δ : Bounds} (h : action.WellFormedUnder Δ) :
    (reconstruct (prepare ambient source target) action).WellFormedUnder Δ := by
  apply CompareSubstitution.wellFormedUnder_of_images
  · simp only [reconstruct, SchemePreparation.prepare, Scheme.freshSubstitution,
      List.forall_mem_map, Bool.false_eq_true, if_false,
      CompareSubstitution.ty, CompareTy.ofTy, CompareTy.subst]
    exact fun _ _ => h.types _
  · simp only [reconstruct, SchemePreparation.prepare, Scheme.freshSubstitution,
      List.forall_mem_map, Bool.false_eq_true, if_false, ModExpr.subst]
    exact fun _ _ => h.modes _

private theorem input_type_lt {ambient : Bounds} {source target : Scheme} {v : TypeVar}
    (hv : v ∈ source.body.typeVars ∪ source.bounds.typeVars) :
    v.index < (prepare ambient source target).firstType := by
  apply SchemePreparation.original_type_lt_first
  simp only [SchemePreparation.originalTypeIds, List.mem_append,
    TypeExpr.mem_typeVariables, Bounds.mem_typeVariables]
  rcases Finset.mem_union.mp hv with hv | hv <;> tauto

private theorem input_mode_lt {ambient : Bounds} {source target : Scheme} {v : ModVar}
    (hv : v ∈ source.body.modVars ∪ source.bounds.modVars) :
    v.index < (prepare ambient source target).firstMode := by
  apply SchemePreparation.original_mode_lt_first
  simp only [SchemePreparation.originalModeIds, List.mem_append,
    TypeExpr.mem_modeVariables, Bounds.mem_modeVariables]
  rcases Finset.mem_union.mp hv with hv | hv <;> tauto

theorem prepare_algebra_under_complete {ambient : Bounds} {source target : Scheme}
    (h : AlgebraSubsumesUnder ambient source target) :
    ∃ action, PreparedWitnessUnder (prepare ambient source target) action := by
  obtain ⟨σ, hi, hs, hw, hd, hb, ht⟩ := h
  let p := prepare ambient source target
  have he := liftWitness_ty (ambient := ambient) (target := target) hi source.body
    (fun _ hv => input_type_lt (Finset.mem_union_left _ hv))
    (fun _ hv => input_mode_lt (Finset.mem_union_left _ hv))
  refine ⟨liftWitness p source σ,
    ⟨liftWitness_domainsAbove _ _ _, liftWitness_wellShaped hs, ?_, ?_⟩,
    liftWitness_wellFormedUnder hw, ?_⟩
  · exact (liftWitness_bounds hi source.bounds p.assumptions
      (fun _ hv => input_type_lt (Finset.mem_union_right _ hv))
      (fun _ hv => input_mode_lt (Finset.mem_union_right _ hv))).mpr hb
  · exact he.symm ▸ ht
  · exact he.symm ▸ hd

theorem PreparedWitnessUnder.subsumes {ambient : Bounds} {source target : Scheme}
    {action : CompareSubstitution}
    (h : PreparedWitnessUnder (prepare ambient source target) action) :
    AlgebraSubsumesUnder ambient source target := by
  let p := prepare ambient source target
  have ht : ∀ v ∈ source.body.typeVars ∪ source.bounds.typeVars,
      action.type v = .var v := fun v hv => h.1.1.type_fixed v (input_type_lt hv)
  have hm : ∀ v ∈ source.body.modVars ∪ source.bounds.modVars,
      action.mode v = .var v := fun v hv => h.1.1.mode_fixed v (input_mode_lt hv)
  have he := reconstruct_ty p action source.body
    (fun v hv => ht v (Finset.mem_union_left _ hv))
    (fun v hv => hm v (Finset.mem_union_left _ hv))
  refine ⟨reconstruct p action, reconstruct_instantiates ambient source target action,
    reconstruct_wellShaped h.1.2.1, reconstruct_wellFormedUnder h.2.1, ?_, ?_, ?_⟩
  · exact he.symm ▸ h.2.2
  · exact (reconstruct_algebra_bounds p action source.bounds p.assumptions
      (fun v hv => ht v (Finset.mem_union_right _ hv))
      (fun v hv => hm v (Finset.mem_union_right _ hv))).mpr h.1.2.2.1
  · exact he.symm ▸ h.1.2.2.2

theorem prepare_algebra_under_iff (ambient : Bounds) (source target : Scheme) :
    AlgebraSubsumesUnder ambient source target ↔
      ∃ action, PreparedWitnessUnder (prepare ambient source target) action :=
  ⟨prepare_algebra_under_complete, fun ⟨_, h⟩ => h.subsumes⟩

end ModalityInference.ComparisonPreparation
