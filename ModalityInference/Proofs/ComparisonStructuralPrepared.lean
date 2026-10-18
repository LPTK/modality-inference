import ModalityInference.Proofs.ComparisonStructuralBasis
import ModalityInference.Proofs.ComparisonWitnessRestriction
import ModalityInference.Proofs.ComparisonDefinedPreparation
import ModalityInference.Proofs.ComparisonDefinedPropagationWitness

/-! Prepared witnesses retain their definedness when restricted to input names.
Successful declared-shape solving then supplies finite structural normal forms
at each image's resolved shape. -/
namespace ModalityInference.ComparisonWitnessRestriction

theorem restrict_wellFormedUnder {Δ : Bounds} {types : Finset TypeVar}
    {modes : Finset ModVar} {action : CompareSubstitution}
    (ht : Δ.typeVars ⊆ types) (hm : Δ.modVars ⊆ modes)
    (h : action.WellFormedUnder Δ) : (restrict types modes action).WellFormedUnder Δ := by
  constructor
  · rintro (n | n)
    · simp only [CompareSubstitution.type, restrict, lookup_map_values]
      cases he : action.types.lookup n with
      | none =>
          simp [CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels]
      | some a =>
          have hd := h.types (.flex n)
          simp only [CompareSubstitution.type, he, Option.getD_some] at hd
          simpa only [he, Option.map_some, Option.getD_some] using restrictTy_defined ht hm hd
    · simp [CompareSubstitution.type, CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels]
  · rintro (n | n)
    · simp only [CompareSubstitution.mode, restrict, lookup_map_values]
      cases he : action.modes.lookup n with
      | none => simp [Entails, ModExpr.WellFormed, ModExpr.eval]
      | some m =>
          have hd := h.modes (.flex n)
          simp only [CompareSubstitution.mode, he, Option.getD_some] at hd
          simpa only [he, Option.map_some, Option.getD_some] using
            (ComparisonModeRestriction.restrict_fixed Δ modes hm).defined hd
    · simp [CompareSubstitution.mode, Entails, ModExpr.WellFormed, ModExpr.eval]

theorem prepared_restrict_under {p : SchemePreparation.Prepared} {action : CompareSubstitution}
    (h : ComparisonPreparation.PreparedWitnessUnder p action) :
    ComparisonPreparation.PreparedWitnessUnder p (restrict (inputTypes p) (inputModes p) action) := by
  have ht : p.assumptions.typeVars ⊆ inputTypes p := by
    intro v hv; simp [inputTypes, hv]
  have hm : p.assumptions.modVars ⊆ inputModes p := by
    intro v hv; simp [inputModes, hv]
  refine ⟨prepared_restrict h.1, restrict_wellFormedUnder ht hm h.2.1, ?_⟩
  rw [restrict_ty (inputTypes p) (inputModes p) action p.sourceType
    (fun v hv => by simp [inputTypes, hv]) (fun v hv => by simp [inputModes, hv])]
  exact restrictTy_defined ht hm h.2.2

theorem prepared_supported_under {p : SchemePreparation.Prepared} {action : CompareSubstitution}
    (h : ComparisonPreparation.PreparedWitnessUnder p action) :
    ∃ result, ComparisonPreparation.PreparedWitnessUnder p result ∧
      result.types.map Prod.fst = action.types.map Prod.fst ∧
      result.modes.map Prod.fst = action.modes.map Prod.fst ∧ Supported p result :=
  ⟨_, prepared_restrict_under h, (restrict_keys _ _ action).1, (restrict_keys _ _ action).2,
    restrict_support _ _ action⟩

theorem Supported.type {p : SchemePreparation.Prepared} {action : CompareSubstitution}
    (h : Supported p action) {v : TypeVar} (hv : v ∈ inputTypes p) :
    ComparisonInterpolation.Supports (· ∈ inputTypes p) (· ∈ inputModes p) (action.type v) := by
  cases v with
  | flex n =>
      cases he : action.types.lookup n with
      | none => simpa only [CompareSubstitution.type, he, Option.getD_none] using hv
      | some a =>
          obtain ⟨left, right, hx, _⟩ := List.lookup_eq_some_iff.mp he
          simpa only [CompareSubstitution.type, he, Option.getD_some] using
            h.1 (n, a) (by simp [hx])
  | rigid n => exact hv

end ModalityInference.ComparisonWitnessRestriction

namespace ModalityInference.ComparisonStructuralBasis

open ComparisonWitnessRestriction

/-- The actual declared-shape unifier supplies the finite model and all shape
equivalences needed to normalize each supported, defined image. The index of
this normal form is the resolved image shape. -/
theorem prepared_image_normal {p : SchemePreparation.Prepared} {action : CompareSubstitution}
    {fuel : Nat} {shapes : ComparisonShapeSolver.Solved}
    (hs : ComparisonShapeSolver.prepare fuel p = .success (.solved shapes))
    (h : ComparisonPreparation.PreparedWitnessUnder p action) (hsp : Supported p action)
    {v : TypeVar} (hv : v ∈ inputTypes p) :
    Normal p.assumptions (inputTypes p).toList (inputModes p).toList shapes.fixedShapes
      ((action.type v).shape.subst shapes.fixedShapes) (action.type v) := by
  have hf := (ComparisonShapeSolver.prepare_solved_iff.mp hs).1
  apply normal_of_supported _ _ shapes.fixedShapes (ComparisonShapeSolver.unify_sound hf)
  · intro w ρ hρ
    exact (ComparisonShapeSolver.unify_factor hf hρ w).symm
  · exact action.type_wellShaped h.1.2.1 v
  · exact h.2.1.types v
  · exact (hsp.type hv).mono (fun _ h => Finset.mem_toList.mpr h)
      (fun _ h => Finset.mem_toList.mpr h)

/-- Simultaneous input-name restriction retains the admissible prepared
witness and its exact key lists. Every observed type image then has a finite
constructor-and-control normal form under the unchanged declared context. -/
theorem prepared_normal_forms {p : SchemePreparation.Prepared} {action : CompareSubstitution}
    {fuel : Nat} {shapes : ComparisonShapeSolver.Solved}
    (hs : ComparisonShapeSolver.prepare fuel p = .success (.solved shapes))
    (h : ComparisonPreparation.PreparedWitnessUnder p action) :
    ∃ result, ComparisonPreparation.PreparedWitnessUnder p result ∧
      result.types.map Prod.fst = action.types.map Prod.fst ∧
      result.modes.map Prod.fst = action.modes.map Prod.fst ∧ Supported p result ∧
      ∀ v ∈ inputTypes p,
        Normal p.assumptions (inputTypes p).toList (inputModes p).toList shapes.fixedShapes
          ((result.type v).shape.subst shapes.fixedShapes) (result.type v) := by
  obtain ⟨result, hr, ht, hm, hsp⟩ := prepared_supported_under h
  exact ⟨result, hr, ht, hm, hsp, fun _ hv => prepared_image_normal hs hr hsp hv⟩

/-- An admissible scheme comparison whose declared shape equations have a
finite model reaches successful shape preparation and a simultaneously
supported, defined witness. Each image admits the corresponding finite
structural normal form, including under structured ambient assumptions. -/
theorem algebra_normal_forms {ambient : Bounds} {source target : Scheme}
    (h : AlgebraSubsumesUnder ambient source target)
    (hdecl : ∃ ρ, ComparisonShape.Models
      (SchemePreparation.prepare ambient source.requireDefinedInstances target).assumptions ρ) :
    let p := SchemePreparation.prepare ambient source.requireDefinedInstances target
    ∃ n shapes action,
      (∀ fuel ≥ n, ComparisonShapeSolver.prepare fuel p = .success (.solved shapes)) ∧
      ComparisonPreparation.PreparedWitnessUnder p action ∧ Supported p action ∧
      ∀ v ∈ inputTypes p,
        Normal p.assumptions (inputTypes p).toList (inputModes p).toList shapes.fixedShapes
          ((action.type v).shape.subst shapes.fixedShapes) (action.type v) := by
  obtain ⟨action, ha⟩ := ComparisonPreparation.prepare_algebra_under_complete h.requireDefinedInstances
  obtain ⟨n, shapes, hs⟩ := ComparisonSkeleton.prepared_witness_shape_complete ha.1 hdecl
  obtain ⟨result, hr, _, _, hsp, hnormal⟩ := prepared_normal_forms (hs n le_rfl) ha
  exact ⟨n, shapes, result, hs, hr, hsp, hnormal⟩

end ModalityInference.ComparisonStructuralBasis
