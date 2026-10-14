import ModalityInference.SchemePreparation
import ModalityInference.Proofs.SchemeFreshening

namespace ModalityInference.SchemePreparation

theorem prepare_assumptions (ambient : Bounds) (source target : Scheme) :
    (prepare ambient source target).assumptions = ambient ++
      (target.instantiate (source.subsumptionIndices ambient target).1
        (source.subsumptionIndices ambient target).2 true).1.assumptions := rfl

theorem prepare_target (ambient : Bounds) (source target : Scheme) :
    (prepare ambient source target).targetType =
      (target.instantiate (source.subsumptionIndices ambient target).1
        (source.subsumptionIndices ambient target).2 true).2 := rfl

theorem reconstruct_eq_mapImages (p : Prepared) (action : Substitution) :
    reconstruct p action = action.mapImages p.sourceRenaming := rfl

theorem reconstruct_instantiates (ambient : Bounds) (source target : Scheme)
    (action : Substitution) : Instantiates source (reconstruct (prepare ambient source target) action) :=
  (source.freshSubstitution_instantiates _ _ false).mapImages action

theorem reconstruct_ty (p : Prepared) (action : Substitution) (t : Ty)
    (ht : ∀ v ∈ t.typeVars, action.type v = .var v)
    (hm : ∀ v ∈ t.modVars, action.mode v = .var v) :
    (reconstruct p action).ty t = action.ty (p.sourceRenaming.ty t) := by
  rw [reconstruct_eq_mapImages, Substitution.ty_compose]
  exact t.subst_congr
    (fun v hv => (action.mapImages_type p.sourceRenaming v (ht v hv)).trans
      (Substitution.type_compose v p.sourceRenaming action).symm)
    (fun v hv => (action.mapImages_mode p.sourceRenaming v (hm v hv)).trans
      (Substitution.mode_compose v p.sourceRenaming action).symm)

theorem reconstruct_bounds (p : Prepared) (action : Substitution) (cs Δ : Bounds)
    (ht : ∀ v ∈ cs.typeVars, action.type v = .var v)
    (hm : ∀ v ∈ cs.modVars, action.mode v = .var v) :
    EntailsAll Δ ((reconstruct p action).bounds cs) ↔
      EntailsAll Δ (action.bounds (p.sourceRenaming.bounds cs)) := by
  simp only [reconstruct_eq_mapImages, EntailsAll, Substitution.bounds,
    List.forall_mem_map, Substitution.constraint_compose]
  exact forall_congr' fun c => forall_congr' fun hc =>
    Substitution.constraint_entails_congr_on c Δ
      (fun v hv =>
        (action.mapImages_type p.sourceRenaming v
          (ht v ((cs.mem_typeVars_iff v).mpr ⟨c, hc, hv⟩))).trans
          (Substitution.type_compose v p.sourceRenaming action).symm)
      (fun v hv =>
        (action.mapImages_mode p.sourceRenaming v
          (hm v ((cs.mem_modVars_iff v).mpr ⟨c, hc, hv⟩))).trans
          (Substitution.mode_compose v p.sourceRenaming action).symm)

/-- A solution of the fresh source obligations gives an instantiation with
exactly the original quantified domain. Body subtyping remains a separate goal
from guarded constraint entailment. -/
theorem reconstruct_sound (ambient : Bounds) (source target : Scheme) (action : Substitution)
    (ht : ∀ v ∈ source.body.typeVars ∪ source.bounds.typeVars, action.type v = .var v)
    (hm : ∀ v ∈ source.body.modVars ∪ source.bounds.modVars, action.mode v = .var v)
    (hb : EntailsAll (prepare ambient source target).assumptions
      (action.bounds (prepare ambient source target).sourceBounds))
    (hbody : Subtype (prepare ambient source target).assumptions
      (action.ty (prepare ambient source target).sourceType)
      (prepare ambient source target).targetType) : Subsumes ambient source target := by
  refine ⟨reconstruct (prepare ambient source target) action,
    reconstruct_instantiates ambient source target action, ?_, ?_⟩
  · exact (reconstruct_bounds (prepare ambient source target) action source.bounds
      (prepare ambient source target).assumptions
      (fun v hv => ht v (Finset.mem_union_right _ hv))
      (fun v hv => hm v (Finset.mem_union_right _ hv))).mpr hb
  · simpa only [reconstruct_ty (prepare ambient source target) action source.body
      (fun v hv => ht v (Finset.mem_union_left _ hv))
      (fun v hv => hm v (Finset.mem_union_left _ hv))] using hbody

end ModalityInference.SchemePreparation
