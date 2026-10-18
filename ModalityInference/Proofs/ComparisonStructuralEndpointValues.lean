import ModalityInference.Proofs.ComparisonStructuralNormalizationValues
import ModalityInference.Proofs.ComparisonStructuralEndpoints

/-! Candidate observers recover the original whole declared bounds from the
actual normalized endpoint list. This direction uses syntactic normalization
preservation and never assumes the root bounds already hold. -/

namespace ModalityInference.ComparisonStructuralEndpoints
open ComparisonAlgebra ComparisonControls ComparisonShapedObserverGluing ComparisonShapeSolver

theorem normalizeList_member {fuel : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {originals : List (CompareTy × CompareTy)}
    {pairs : List Pair} (h : normalizeList fuel p solved originals=.success pairs)
    {original : CompareTy × CompareTy} (ho : original∈originals) :
    ∃pair∈pairs,normalizePair fuel p solved original=.success pair := by
  have hs := normalizeList_spec h
  clear h
  induction hs with
  | nil => cases ho
  | cons hp hrest ih =>
    rcases List.mem_cons.mp ho with rfl|ho
    · exact ⟨_,List.mem_cons_self,hp⟩
    · obtain ⟨pair,hp,he⟩ := ih ho
      exact ⟨pair,List.mem_cons_of_mem _ hp,he⟩

theorem normalizePair_values {shapeFuel fuel : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    {shape : ComparisonShape} (d : Data p.assumptions shape) (hr : Resolved p.assumptions shape)
    {c : Coordinate} {η : ModVar → Mode} (hη : c=.unaffected ∨ ModeModels p.assumptions η)
    (hc : ∀m x,d.transition.apply m x=coordinateValue c x (m.complete η))
    {original : CompareTy × CompareTy} {pair : Pair}
    (hl : Representable p.assumptions shape original.1)
    (hright : Representable p.assumptions shape original.2)
    (hsl : SupportedTy p original.1) (hsr : SupportedTy p original.2)
    (h : normalizePair fuel p solved original=.success pair) :
    d.value pair.left=d.value original.1 ∧ d.value pair.right=d.value original.2 := by
  obtain ⟨left,right,hleft,hright',rfl⟩ := normalizePair_spec h
  have hu := (prepare_solved_iff.mp hs).1
  have hmodels := unify_sound hu
  have heq : ∀v,ComparisonShape.Equivalent p.assumptions (.var v) (solved.fixedShapes v) :=
    fun v φ hφ=>(unify_factor hu hφ v).symm
  exact ⟨ComparisonStructuralNormalization.run_value d hr hη hc hmodels heq hl hsl hleft,
    ComparisonStructuralNormalization.run_value d hr hη hc hmodels heq hright hsr hright'⟩

theorem declared_boundsHold {shapeFuel fuel : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    {shape : ComparisonShape} (d : Data p.assumptions shape) (hr : Resolved p.assumptions shape)
    (hf : shape.subst solved.fixedShapes=shape)
    {c : Coordinate} {η : ModVar → Mode} (hη : c=.unaffected ∨ ModeModels p.assumptions η)
    (hc : ∀m x,d.transition.apply m x=coordinateValue c x (m.complete η))
    (hΔ : p.assumptions.TypeBoundsDefined)
    {originals : List (CompareTy × CompareTy)} {pairs : List Pair}
    (h : normalizeList fuel p solved originals=.success pairs)
    (hdeclared : ∀pair∈declared p,pair∈originals)
    (hnode : ∀pair∈atShape pairs shape,d.value pair.1≤d.value pair.2) : BoundsHold d := by
  intro a b hab hshape
  have horiginal : (CompareTy.ofTy a,CompareTy.ofTy b)∈declared p :=
    List.mem_filterMap.mpr ⟨.sub a b,hab,rfl⟩
  have hg := declared_guarded p hΔ _ horiginal
  obtain ⟨pair,hpair,hp⟩ := normalizeList_member h (hdeclared _ horiginal)
  have hleft : Representable p.assumptions shape (.ofTy a) :=
    ⟨hg.subtype.wellShaped_left,hg.left_defined,by simpa using hshape⟩
  have hright : Representable p.assumptions shape (.ofTy b) :=
    ⟨hg.subtype.wellShaped_right,hg.right_defined,hg.subtype.shape_equivalent.symm.trans hleft.2.2⟩
  obtain ⟨hl,hright'⟩ := normalizePair_values hs d hr hη hc hleft hright
    hg.left_supported hg.right_supported hp
  have he : pair.shape=shape := by
    obtain ⟨left,right,_,_,he⟩ := normalizePair_spec hp
    rw [he]
    exact (hleft.2.2 solved.fixedShapes (unify_sound (prepare_solved_iff.mp hs).1)).trans hf
  have hm : (pair.left,pair.right)∈atShape pairs shape :=
    List.mem_filterMap.mpr ⟨pair,hpair,by simp [he]⟩
  simpa only [hl,hright'] using hnode _ hm

theorem run_boundsHold {shapeFuel fuel : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    {shape : ComparisonShape} (d : Data p.assumptions shape) (hr : Resolved p.assumptions shape)
    (hf : shape.subst solved.fixedShapes=shape)
    {c : Coordinate} {η : ModVar → Mode} (hη : c=.unaffected ∨ ModeModels p.assumptions η)
    (hc : ∀m x,d.transition.apply m x=coordinateValue c x (m.complete η))
    (hΔ : p.assumptions.TypeBoundsDefined)
    {action : CompareSubstitution} {pairs : List Pair}
    (h : run fuel p solved action=.success pairs)
    (hnode : ∀pair∈atShape pairs shape,d.value pair.1≤d.value pair.2) : BoundsHold d :=
  declared_boundsHold hs d hr hf hη hc hΔ h (fun _ hp=>List.mem_append_left _ hp) hnode

theorem prepared_run_boundsHold {shapeFuel fuel : Nat} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved}
    (hs : ComparisonShapeSolver.prepare shapeFuel (SchemePreparation.prepare [] source target)=
      .success (.solved solved))
    {shape : ComparisonShape} (d : Data (SchemePreparation.prepare [] source target).assumptions shape)
    (hr : Resolved (SchemePreparation.prepare [] source target).assumptions shape)
    (hf : shape.subst solved.fixedShapes=shape)
    {c : Coordinate} {η : ModVar → Mode}
    (hη : c=.unaffected ∨ ModeModels (SchemePreparation.prepare [] source target).assumptions η)
    (hc : ∀m x,d.transition.apply m x=coordinateValue c x (m.complete η))
    {action : CompareSubstitution} {pairs : List Pair}
    (h : run fuel (SchemePreparation.prepare [] source target) solved action=.success pairs)
    (hnode : ∀pair∈atShape pairs shape,d.value pair.1≤d.value pair.2) : BoundsHold d :=
  run_boundsHold hs d hr hf hη hc (SchemePreparation.prepared_typeBoundsDefined source target) h hnode

end ModalityInference.ComparisonStructuralEndpoints
