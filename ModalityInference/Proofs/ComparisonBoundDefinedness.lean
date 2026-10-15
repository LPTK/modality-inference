import ModalityInference.Proofs.ComparisonWitnessProperties
import ModalityInference.Proofs.InstanceDefinedness
import ModalityInference.Proofs.ComparisonPropagationComposition

/-!
# Defined images of parameters in comparison bounds

An internal substitution that satisfies guarded source bounds maps every parameter
occurring in those bounds to a defined type or modality. Partial images can
therefore occur only for parameters absent from the bounds.
-/

namespace ModalityInference

theorem CompareTy.definedUnder_prod_iff {Δ : Bounds} {a b : CompareTy} :
    (.prod a b : CompareTy).DefinedUnder Δ ↔ a.DefinedUnder Δ ∧ b.DefinedUnder Δ := by
  simp only [CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels,
    List.mem_append, or_imp, forall_and]

theorem CompareTy.definedUnder_sum_iff {Δ : Bounds} {a b : CompareTy} :
    (.sum a b : CompareTy).DefinedUnder Δ ↔ a.DefinedUnder Δ ∧ b.DefinedUnder Δ := by
  simp only [CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels,
    List.mem_append, or_imp, forall_and]

theorem CompareTy.definedUnder_fn_iff {Δ : Bounds} {a b : CompareTy} :
    (.fn a b : CompareTy).DefinedUnder Δ ↔ a.DefinedUnder Δ ∧ b.DefinedUnder Δ := by
  simp only [CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels,
    List.mem_append, or_imp, forall_and]

theorem CompareTy.defined_ofTy_subst_types {a : Ty} {ts : TypeVar → CompareTy}
    {ms : ModVar → ModExpr} {Δ : Bounds}
    (h : ((ofTy a).subst ts ms).DefinedUnder Δ) :
    ∀ v ∈ a.typeVars, (ts v).DefinedUnder Δ := by
  induction a <;> simp_all only [TypeExpr.typeVars, CompareTy.ofTy, CompareTy.subst,
    CompareTy.definedUnder_prod_iff, CompareTy.definedUnder_sum_iff,
    CompareTy.definedUnder_fn_iff, CompareTy.definedUnder_modal_iff,
    Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty,
    or_imp, false_implies, implies_true, and_self]

theorem CompareTy.defined_ofTy_subst_modes {a : Ty} {ts : TypeVar → CompareTy}
    {ms : ModVar → ModExpr} {Δ : Bounds}
    (h : ((ofTy a).subst ts ms).DefinedUnder Δ) :
    ∀ v ∈ a.modVars, Entails Δ (.defined (ms v)) := by
  induction a <;> simp_all only [TypeExpr.modVars, CompareTy.ofTy, CompareTy.subst,
    CompareTy.definedUnder_prod_iff, CompareTy.definedUnder_sum_iff,
    CompareTy.definedUnder_fn_iff, CompareTy.definedUnder_modal_iff,
    Finset.mem_union, Finset.notMem_empty, or_imp, false_implies, implies_true, and_self, true_and]
  exact fun v hv η hη => (h.2 η hη).subst_var hv

theorem AlgebraEntails.constraint_types_defined {Δ : Bounds} {σ : CompareSubstitution}
    {c : Constraint} (h : AlgebraEntails Δ (σ.constraint c)) :
    ∀ v ∈ c.typeVars, (σ.type v).DefinedUnder Δ := by
  cases c with
  | sub a b =>
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact CompareTy.defined_ofTy_subst_types h.2.1 v hv
    · exact CompareTy.defined_ofTy_subst_types h.2.2 v hv
  | equiv a b =>
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact CompareTy.defined_ofTy_subst_types h.2.2.1 v hv
    · exact CompareTy.defined_ofTy_subst_types h.2.2.2 v hv
  | equal v a =>
    have hh := (CompareSubstitution.algebra_equal_iff σ Δ v a).mp h
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hh.1.2.1
    · exact CompareTy.defined_ofTy_subst_types hh.1.2.2 w hw
  | mode | defined => simp [Constraint.typeVars]

theorem AlgebraEntails.constraint_modes_defined {Δ : Bounds} {σ : CompareSubstitution}
    {c : Constraint} (h : AlgebraEntails Δ (σ.constraint c)) :
    ∀ v ∈ c.modVars, Entails Δ (.defined (σ.mode v)) := by
  cases c with
  | sub a b =>
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact CompareTy.defined_ofTy_subst_modes h.2.1 v hv
    · exact CompareTy.defined_ofTy_subst_modes h.2.2 v hv
  | equiv a b =>
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact CompareTy.defined_ofTy_subst_modes h.2.2.1 v hv
    · exact CompareTy.defined_ofTy_subst_modes h.2.2.2 v hv
  | equal v a =>
    have hh := (CompareSubstitution.algebra_equal_iff σ Δ v a).mp h
    exact CompareTy.defined_ofTy_subst_modes hh.1.2.2
  | mode a b =>
    intro v hv η hη
    rcases Finset.mem_union.mp hv with hv | hv
    · exact (h.defined.1 η hη).subst_var hv
    · exact (h.defined.2 η hη).subst_var hv
  | defined m => exact fun v hv η hη => (h η hη).subst_var hv

/-- Satisfying substituted bounds entails definedness of every image used by
those bounds. -/
theorem AlgebraEntailsAll.bounds_support_defined {Δ bounds : Bounds} {σ : CompareSubstitution}
    (h : AlgebraEntailsAll Δ (σ.bounds bounds)) :
    (∀ v ∈ bounds.typeVars, (σ.type v).DefinedUnder Δ) ∧
    (∀ v ∈ bounds.modVars, Entails Δ (.defined (σ.mode v))) := by
  constructor
  · intro v hv
    obtain ⟨c, hc, hv⟩ := (bounds.mem_typeVars_iff v).mp hv
    exact AlgebraEntails.constraint_types_defined
      (h _ (List.mem_map.mpr ⟨c, hc, rfl⟩)) v hv
  · intro v hv
    obtain ⟨c, hc, hv⟩ := (bounds.mem_modVars_iff v).mp hv
    exact AlgebraEntails.constraint_modes_defined
      (h _ (List.mem_map.mpr ⟨c, hc, rfl⟩)) v hv

end ModalityInference
