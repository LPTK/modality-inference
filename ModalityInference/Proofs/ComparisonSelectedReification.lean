import ModalityInference.ComparisonSelectedReification
import ModalityInference.Proofs.ComparisonClosedBranchWitness

/-! Selected-branch reconstruction is total on every covered witness and
retains shape compatibility and definedness under the original assumptions. -/
namespace ModalityInference.ComparisonSelectedBases

open ComparisonAlgebra ComparisonControls ComparisonPropagation ComparisonStructuralLattice
open ComparisonPreparation ComparisonWitnessRestriction

theorem enabled_spec {world : Nat → Bool} {bs : List Branch} {b : Branch}
    (h : enabled world bs = some b) : b∈bs ∧ b.guard.eval world=true := by
  induction bs with
  | nil => cases h
  | cons a bs ih =>
    simp only [enabled] at h
    split at h
    next ha => cases Option.some.inj h; exact ⟨List.mem_cons_self, ha⟩
    next => exact ⟨List.mem_cons_of_mem _ (ih h).1, (ih h).2⟩

theorem enabled_complete {world : Nat → Bool} {bs : List Branch}
    (h : ∃b∈bs, b.guard.eval world=true) : ∃b, enabled world bs=some b := by
  induction bs with
  | nil => simp at h
  | cons a bs ih =>
    by_cases ha : a.guard.eval world=true
    · exact ⟨a, by simp [enabled, ha]⟩
    · obtain ⟨b, hb, hg⟩ := h
      have hb' : b∈bs := (List.mem_cons.mp hb).resolve_left (fun he => ha (he ▸ hg))
      obtain ⟨c, hc⟩ := ih ⟨b,hb',hg⟩
      exact ⟨c, by simp [enabled, ha, hc]⟩

theorem reifyImage_spec {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world : Nat → Bool}
    {v : TypeVar} {clauses : CNF} {t : CompareTy}
    (h : reifyImage first p solved world v clauses=some t) :
    ∃b∈prepared first p solved v, b.guard.eval world=true ∧
      reify b.basis.types clauses=some t := by
  cases he : enabled world (prepared first p solved v) with
  | none => simp [reifyImage, he] at h
  | some b => exact ⟨b, (enabled_spec he).1, (enabled_spec he).2,
      by simpa [reifyImage, he] using h⟩

theorem BranchPolynomials.reifyImage {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world : Nat → Bool} {action : CompareSubstitution}
    (h : BranchPolynomials first p solved world action) {v : TypeVar} (hv : v∈inputNames p) :
    ∃clauses t, reifyImage first p solved world v clauses=some t ∧
      Representable p.assumptions
        (((solved.resolveAll v).subst ((layout first p solved).decode world)).subst solved.fixedShapes) t ∧
      Equiv p.assumptions t (action.type v) := by
  obtain ⟨b, hb, clauses, t, hg, _, _, ht, hr, he⟩ := h.2 v hv
  obtain ⟨c, hc⟩ := enabled_complete ⟨b,hb,hg⟩
  have hs := bases_enabled_unique h.1 (fun _ => layout_scope hv)
    (enabled_spec hc).1 hb (enabled_spec hc).2 hg
  refine ⟨clauses,t,?_,?_,he⟩
  · simp [ComparisonSelectedBases.reifyImage, hc, hs.2, ht]
  · simpa only [(prepared_sound h.1 hv hb hg).1] using hr

theorem reifyImage_representable {fuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world : Nat → Bool}
    (hs : ComparisonShapeSolver.prepare fuel p=.success (.solved solved))
    (hw : (layout first p solved).theory.eval world=true)
    {v : TypeVar} (hv : v∈inputNames p) {clauses : CNF} {t : CompareTy}
    (h : reifyImage first p solved world v clauses=some t) :
    Representable p.assumptions
      (((solved.resolveAll v).subst ((layout first p solved).decode world)).subst solved.fixedShapes) t := by
  obtain ⟨b, hb, hg, ht⟩ := reifyImage_spec h
  obtain ⟨he, hbas⟩ := prepared_sound hw hv hb hg
  rw [← he]
  apply reify_property ht (Representable p.assumptions b.shape)
  · rw [(ComparisonStructuralBasis.basis_spec hbas).2.2]
    apply ComparisonStructuralBasis.extend_representable
    apply ComparisonStructuralBasis.heads_representable
    intro v ρ hρ
    exact (ComparisonShapeSolver.unify_factor
      (ComparisonShapeSolver.prepare_solved_iff.mp hs).1 hρ v).symm
  · exact fun _ _ => representable_typeOp true
  · exact fun _ _ => representable_typeOp false

theorem reifyImage_support {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world : Nat → Bool}
    {v : TypeVar} {clauses : CNF} {t : CompareTy}
    (h : reifyImage first p solved world v clauses=some t) :
    ComparisonInterpolation.Supports (·∈inputNames p) (·∈inputModes p) t := by
  obtain ⟨b,hb,_,ht⟩ := reifyImage_spec h
  obtain ⟨_,_,_,_,hbas⟩ := bases_origin hb
  exact reify_property ht _ (ComparisonStructuralBasis.basis_support hbas)
    (fun _ _ ha hb => ⟨ha,hb⟩) (fun _ _ ha hb => ⟨ha,hb⟩)

theorem BranchPolynomials.reifyClosedImage {ambient : Bounds} {source target : Scheme}
    {first : Nat} {solved : ComparisonShapeSolver.Solved} {world : Nat → Bool}
    {action : CompareSubstitution}
    (h : BranchPolynomials first (SchemePreparation.prepare ambient source target) solved world action)
    (hw : PreparedWitnessUnder (SchemePreparation.prepare ambient source target) action)
    {v : TypeVar} (hv : v∈inputNames (SchemePreparation.prepare ambient source target)) :
    ∃clauses t, reifyClosedImage first (SchemePreparation.prepare ambient source target)
      solved world action.mode v clauses=some t ∧
      t.DefinedUnder (SchemePreparation.prepare ambient source target).assumptions ∧
      Equiv (SchemePreparation.prepare ambient source target).assumptions
        t (action.closeTypeModes.type v) := by
  obtain ⟨clauses,t,ht,hr,he⟩ := h.reifyImage hv
  have hf := hw.mode_fixed_context
  refine ⟨clauses, t.subst CompareTy.var action.mode, ?_, hf.type_defined hr.2.1, ?_⟩
  · simp [ComparisonSelectedBases.reifyClosedImage, ht]
  · rw [CompareSubstitution.closeTypeModes_type]
    exact ⟨hf.algebra he.1, hf.algebra he.2⟩

end ModalityInference.ComparisonSelectedBases
