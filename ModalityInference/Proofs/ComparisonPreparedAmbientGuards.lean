import ModalityInference.Proofs.ComparisonPreparedDriver

/-! A successful scalar certificate establishes the written guards of ambient
type edges without strengthening or replacing the ambient assumptions. -/
namespace ModalityInference.ComparisonPreparedScalar

theorem required_typeBoundsDefined {p : SchemePreparation.Prepared} {action : Substitution}
    (hfixed : ∀v∈p.assumptions.modVars,action.mode v=.var v)
    (hguards : EntailsAll p.assumptions
      ((required p).map (Constraint.subst TypeExpr.var action.mode))) :
    p.assumptions.TypeBoundsDefined := by
  intro a b hab
  have hg := endpoint_guards hguards
    ((ComparisonSignedObservation.mem_endpoints (p := p) (pair := (a,b))).mpr (Or.inl hab))
  have hf (t : Ty) (ht : t=a ∨ t=b) : ∀v∈t.modVars,action.mode v=.var v := by
    intro v hv
    apply hfixed v
    apply (p.assumptions.mem_modVars_iff v).mpr
    refine ⟨_,hab,?_⟩
    rcases ht with rfl|rfl <;> simp [Constraint.modVars,hv]
  let σ : CompareSubstitution := {modes:=action.modes}
  have hm : σ.mode=action.mode := by funext v;cases v <;> rfl
  have ht : σ.type=CompareTy.var := by funext v;cases v <;> rfl
  have hd (t : Ty) (hmem : t=a ∨ t=b) : t.DefinedUnder p.assumptions := by
    have hh := ComparisonSignedClosedAlignment.defined_of_annotations (σ := σ)
      (fun v => by rw [ht];intro η hη c hc;cases hc) t
      (by simpa only [hm] using hg t (by simpa using hmem))
    rw [CompareSubstitution.ty,ht,hm,ComparisonModeRestriction.ofTy_fixed t (hf t hmem)] at hh
    exact (CompareTy.definedUnder_ofTy t p.assumptions).mp hh
  exact ⟨hd a (Or.inl rfl),hd b (Or.inr rfl)⟩

end ModalityInference.ComparisonPreparedScalar
