import ModalityInference.ComparisonSelectedMatches
import ModalityInference.Proofs.ComparisonShapeSelectorMatches
import ModalityInference.Proofs.ComparisonSelectedBranchWitness

/-! The same prepared witness satisfies the executable anchor constraints.
Fixed input names and the whole target body retain their declared shapes. -/

namespace ModalityInference.ComparisonSelectedBases

open ComparisonShapeSelectors ComparisonShapeRetraction ComparisonShapeSolver
open ComparisonPreparation ComparisonWitnessRestriction

theorem BranchPolynomials.image_shape {fuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world : Nat → Bool} {action : CompareSubstitution}
    (hs : ComparisonShapeSolver.prepare fuel p=.success (.solved solved))
    (h : BranchPolynomials first p solved world action) {v : TypeVar} (hv : v∈inputNames p) :
    (action.type v).shape.subst solved.fixedShapes =
      ((solved.resolveAll v).subst ((layout first p solved).decode world)).subst solved.fixedShapes := by
  obtain ⟨branch, hb, _, _, hg, _, _, _, hrep, he⟩ := h.2 v hv
  have hshape := (prepared_sound h.1 hv hb hg).1
  have hi := (he.1.shape_equivalent.symm.trans hrep.2.2) solved.fixedShapes
    (unify_sound (prepare_solved_iff.mp hs).1)
  simpa only [hshape, fixedShapes_idempotent hs] using hi

theorem BranchPolynomials.ty_shape {fuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world : Nat → Bool} {action : CompareSubstitution}
    (hs : ComparisonShapeSolver.prepare fuel p=.success (.solved solved))
    (h : BranchPolynomials first p solved world action)
    (t : Ty) (ht : ∀v∈t.typeVars, v∈inputNames p) :
    (action.ty t).shape.subst solved.fixedShapes =
      (((ComparisonShape.ofTy t).subst solved.resolveAll).subst
        ((layout first p solved).decode world)).subst solved.fixedShapes := by
  rw [action.ty_shape, subst_comp]
  simp only [subst_comp]
  apply subst_congr
  intro v hv
  simpa only [subst_comp] using h.image_shape hs (ht v ((mem_vars_ofTy t v).mp hv))


private theorem source_input (p : SchemePreparation.Prepared) {v : TypeVar}
    (hv : v∈p.sourceType.typeVars) : v∈inputNames p := by
  apply (mem_inputNames p v).mpr
  simp only [ComparisonWitnessRestriction.inputTypes, Finset.mem_union]
  exact Or.inl (Or.inr hv)

theorem template_scope {first : Nat} {p : SchemePreparation.Prepared} {solved : ComparisonShapeSolver.Solved}
    {t : Ty} (ht : ∀v∈t.typeVars, v∈inputNames p) {w : TypeVar}
    (hw : w∈((ComparisonShape.ofTy t).subst solved.resolveAll).vars) :
    w∈(layout first p solved).parameters := by
  obtain ⟨v, hv, hw⟩ := (mem_vars_subst _ _ _).mp hw
  exact layout_scope (ht v ((mem_vars_ofTy t v).mp hv)) hw

theorem anchorEquations_scope (first : Nat) (p : SchemePreparation.Prepared) (solved : ComparisonShapeSolver.Solved) :
    ∀pair∈anchorEquations p solved, ∀v∈pair.1.vars, v∈(layout first p solved).parameters := by
  intro pair hp v hv
  simp only [anchorEquations, List.mem_append, List.mem_map, List.mem_filter, List.mem_singleton] at hp
  rcases hp with ⟨w, ⟨hw, _⟩, rfl⟩ | rfl
  · exact layout_scope hw hv
  · exact template_scope (fun _ => source_input p) hv

theorem BranchPolynomials.anchor_equations {fuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world : Nat → Bool} {action : CompareSubstitution}
    (hs : ComparisonShapeSolver.prepare fuel p=.success (.solved solved))
    (h : BranchPolynomials first p solved world action) (hw : PreparedWitnessUnder p action) :
    ∀pair∈anchorEquations p solved,
      (pair.1.subst ((layout first p solved).decode world)).subst solved.fixedShapes=pair.2 := by
  intro pair hp
  simp only [anchorEquations, List.mem_append, List.mem_map, List.mem_filter, List.mem_singleton] at hp
  rcases hp with ⟨v, ⟨hv, hlt⟩, rfl⟩ | rfl
  · change ((solved.resolveAll v).subst ((layout first p solved).decode world)).subst solved.fixedShapes = _
    rw [← h.image_shape hs hv, hw.1.1.type_fixed v (of_decide_eq_true hlt)]
    rfl
  · have he := hw.1.2.2.2.shape_equivalent solved.fixedShapes
      (unify_sound (prepare_solved_iff.mp hs).1)
    simpa only [h.ty_shape hs p.sourceType (fun _ => source_input p), CompareTy.shape_ofTy] using he

theorem BranchPolynomials.anchorTheory {fuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world : Nat → Bool} {action : CompareSubstitution}
    (hs : ComparisonShapeSolver.prepare fuel p=.success (.solved solved))
    (h : BranchPolynomials first p solved world action) (hw : PreparedWitnessUnder p action) :
    (anchorTheory first p solved).eval world=true := by
  exact ((layout first p solved).matchTheory_correct solved.fixedShapes
    (anchorEquations p solved) world (anchorEquations_scope first p solved)).mpr
      ⟨h.1, h.anchor_equations hs hw⟩

theorem anchorTheory_atoms (first : Nat) (p : SchemePreparation.Prepared) (solved : ComparisonShapeSolver.Solved) :
    ∀n∈(anchorTheory first p solved).atoms, first≤n ∧ n<(layout first p solved).next :=
  (layout first p solved).matchTheory_atoms solved.fixedShapes (anchorEquations p solved)
    (anchorEquations_scope first p solved)


/-- Anchor constraints follow from the original fixed-domain and body
judgments of the same admissible finite-basis witness. -/
theorem algebra_anchored_polynomials {ambient : Bounds} {source target : Scheme}
    (first : Nat) (h : AlgebraSubsumesUnder ambient source target)
    (hdecl : ∃φ, ComparisonShape.Models
      (SchemePreparation.prepare ambient source.requireDefinedInstances target).assumptions φ) :
    let p := SchemePreparation.prepare ambient source.requireDefinedInstances target
    ∃n solved τ ρ,
      (∀fuel≥n, ComparisonShapeSolver.prepare fuel p = .success (.solved solved)) ∧
      PreparedWitnessUnder p τ ∧ Supported p τ ∧
      (∀v, ρ v∈shapeChoices p solved) ∧
      (anchorTheory first p solved).eval ((layout first p solved).encode ρ)=true ∧
      BranchPolynomials first p solved ((layout first p solved).encode ρ) τ := by
  obtain ⟨n, solved, τ, ρ, hs, hw, hsp, hc, hp⟩ := algebra_branch_polynomials first h hdecl
  exact ⟨n, solved, τ, ρ, hs, hw, hsp, hc, hp.anchorTheory (hs n le_rfl) hw, hp⟩

end ModalityInference.ComparisonSelectedBases
