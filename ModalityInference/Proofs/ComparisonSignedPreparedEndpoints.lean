import ModalityInference.ComparisonSignedPreparation
import ModalityInference.Proofs.ComparisonSignedEndpointAlignment
import ModalityInference.Proofs.ComparisonStructuralEndpoints
import ModalityInference.Proofs.ComparisonInputAction
import ModalityInference.Proofs.ComparisonSelectedBranchWitness

/-! Prepared comparison witnesses align every whole public endpoint with its
actual structural layout. Original guards supply all annotation definedness,
and one canonical polynomial is shared by all occurrences of each type binder. -/
namespace ModalityInference.ComparisonSignedObservation
open ComparisonSignedEndpoints ComparisonStructuralLayout ComparisonControls ComparisonAlgebra
  ComparisonStructuralBasis ComparisonInterpolation ComparisonPreparation ComparisonWitnessRestriction

@[simp] theorem mem_declaredEndpoints {p : SchemePreparation.Prepared} {pair : Ty × Ty} :
    pair∈declaredEndpoints p ↔ Constraint.sub pair.1 pair.2∈p.assumptions := by
  constructor
  · intro h
    obtain ⟨c,hc,he⟩ := List.mem_filterMap.mp h
    cases c <;> simp only at he
    case sub a b =>
      cases Option.some.inj he
      exact hc
    all_goals cases he
  · intro h
    exact List.mem_filterMap.mpr ⟨.sub pair.1 pair.2,h,rfl⟩

theorem mem_endpoints {p : SchemePreparation.Prepared} {pair : Ty × Ty} :
    pair∈endpoints p ↔ Constraint.sub pair.1 pair.2∈p.assumptions ∨
      (∃c∈p.sourceBounds,pair∈ComparisonStructuralEndpoints.constraintPairs c) ∨
      pair=(p.sourceType,p.targetType) := by
  simp only [endpoints,sourceEndpoints,List.mem_append,mem_declaredEndpoints,
    List.mem_flatMap,List.mem_singleton]

theorem endpoints_input {p : SchemePreparation.Prepared} {pair : Ty × Ty}
    (h : pair∈endpoints p) :
    pair.1.typeVars ⊆ inputTypes p ∧ pair.2.typeVars ⊆ inputTypes p ∧
      pair.1.modVars ⊆ inputModes p ∧ pair.2.modVars ⊆ inputModes p := by
  rcases mem_endpoints.mp h with h|⟨c,hc,hpair⟩|rfl
  · have ht (v) (hv : v∈pair.1.typeVars ∪ pair.2.typeVars) : v∈p.assumptions.typeVars :=
      (p.assumptions.mem_typeVars_iff v).mpr ⟨_,h,hv⟩
    have hm (v) (hv : v∈pair.1.modVars ∪ pair.2.modVars) : v∈p.assumptions.modVars :=
      (p.assumptions.mem_modVars_iff v).mpr ⟨_,h,hv⟩
    refine ⟨?_,?_,?_,?_⟩
    · exact fun v hv => by have hh:=ht v (Finset.mem_union_left _ hv);simp [inputTypes,hh]
    · exact fun v hv => by have hh:=ht v (Finset.mem_union_right _ hv);simp [inputTypes,hh]
    · exact fun v hv => by have hh:=hm v (Finset.mem_union_left _ hv);simp [inputModes,hh]
    · exact fun v hv => by have hh:=hm v (Finset.mem_union_right _ hv);simp [inputModes,hh]
  · have hs:=ComparisonStructuralEndpoints.constraintPairs_support c pair hpair
    have ht (v) (hv:v∈c.typeVars) : v∈p.sourceBounds.typeVars :=
      (p.sourceBounds.mem_typeVars_iff v).mpr ⟨c,hc,hv⟩
    have hm (v) (hv:v∈c.modVars) : v∈p.sourceBounds.modVars :=
      (p.sourceBounds.mem_modVars_iff v).mpr ⟨c,hc,hv⟩
    refine ⟨?_,?_,?_,?_⟩
    · exact fun v hv => by have hh:=ht v (hs.1 hv);simp [inputTypes,hh]
    · exact fun v hv => by have hh:=ht v (hs.2.1 hv);simp [inputTypes,hh]
    · exact fun v hv => by have hh:=hm v (hs.2.2.1 hv);simp [inputModes,hh]
    · exact fun v hv => by have hh:=hm v (hs.2.2.2 hv);simp [inputModes,hh]
  · exact ⟨fun _ hv => by simp [inputTypes,hv],fun _ hv => by simp [inputTypes,hv],
      fun _ hv => by simp [inputModes,hv],fun _ hv => by simp [inputModes,hv]⟩

theorem ty_fixed_bounded {σ : CompareSubstitution} {nt nm : Nat}
    (h : σ.DomainsAbove nt nm) (a : Ty) (ha : a.Bounded nt nm) : σ.ty a=.ofTy a := by
  have hb:=(TypeExpr.bounded_iff _ _ _).mp ha
  exact σ.ty_fixed a (fun v hv => h.type_fixed v (hb.1 v hv))
    (fun v hv => h.mode_fixed v (hb.2 v hv))

theorem inputAction_fixed (p : SchemePreparation.Prepared) (σ : CompareSubstitution)
    (v : TypeVar) (hv : ∀n∈ComparisonSelectedBases.inputTypeKeys p,v≠.flex n) :
    (ComparisonSelectedBases.inputAction p σ).type v=.var v := by
  cases v with
  | rigid => rfl
  | flex n =>
    have hn : n∉ComparisonSelectedBases.inputTypeKeys p := fun hn => hv n hn rfl
    have hlookup : (ComparisonSelectedBases.inputAction p σ).types.lookup n=none := by
      apply List.lookup_eq_none_iff.mpr
      intro entry he
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp he
      exact bne_iff_ne.mpr (fun heq => hn (heq ▸ hk))
    simp only [CompareSubstitution.type,hlookup,Option.getD_none]


theorem prepared_interpreted_mem {ambient : Bounds} {source target : Scheme}
    {σ : CompareSubstitution}
    (hw : PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ)
    {pair : Ty × Ty} (hp : pair∈endpoints (SchemePreparation.prepare ambient source target)) :
    (σ.ty pair.1,σ.ty pair.2)∈ComparisonStructuralEndpoints.all
      (SchemePreparation.prepare ambient source target) σ := by
  let p:=SchemePreparation.prepare ambient source target
  rcases mem_endpoints.mp hp with hd|⟨c,hc,hpair⟩|rfl
  · have hs:=(Bounds.bounded_iff _ _ _).mp
      (SchemePreparation.prepare_assumptions_bounded_first ambient source target)
    have fixed (a : Ty) (ha : a=pair.1 ∨ a=pair.2) : σ.ty a=.ofTy a := by
      apply σ.ty_fixed a
      · intro v hv
        apply hw.1.1.type_fixed v
        apply hs.1 v
        apply (p.assumptions.mem_typeVars_iff v).mpr
        refine ⟨_,hd,?_⟩
        rcases ha with rfl|rfl
        · exact Finset.mem_union_left _ hv
        · exact Finset.mem_union_right _ hv
      · intro v hv
        apply hw.1.1.mode_fixed v
        apply hs.2 v
        apply (p.assumptions.mem_modVars_iff v).mpr
        refine ⟨_,hd,?_⟩
        rcases ha with rfl|rfl
        · exact Finset.mem_union_left _ hv
        · exact Finset.mem_union_right _ hv
    rw [fixed _ (Or.inl rfl),fixed _ (Or.inr rfl)]
    exact List.mem_append_left _ (List.mem_filterMap.mpr ⟨_,hd,rfl⟩)
  · exact List.mem_append_right _ (List.mem_append_left _
      (List.mem_map.mpr ⟨pair,List.mem_flatMap.mpr ⟨c,hc,hpair⟩,rfl⟩))
  · rw [ty_fixed_bounded hw.1.1 _ (SchemePreparation.prepare_targetType_bounded_first ambient source target)]
    exact List.mem_append_right _ (List.mem_append_right _ List.mem_cons_self)

theorem prepared_guarded {source target : Scheme} {σ : CompareSubstitution}
    (hw : PreparedWitnessUnder (SchemePreparation.prepare [] source target) σ)
    (hsp : Supported (SchemePreparation.prepare [] source target) σ)
    {pair : Ty × Ty} (hp : pair∈endpoints (SchemePreparation.prepare [] source target)) :
    ComparisonStructuralEndpoints.GuardedPair (SchemePreparation.prepare [] source target)
      (σ.ty pair.1,σ.ty pair.2) :=
  ComparisonStructuralEndpoints.prepared_all_guarded hw hsp _ (prepared_interpreted_mem hw hp)


theorem prepared_alignment {shapeFuel : Nat} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {σ : CompareSubstitution}
    (hshape : ComparisonShapeSolver.prepare shapeFuel (SchemePreparation.prepare [] source target)=
      .success (.solved solved))
    (hw : PreparedWitnessUnder (SchemePreparation.prepare [] source target) σ)
    (hsp : Supported (SchemePreparation.prepare [] source target) σ)
    {pair : Ty × Ty} (hp : pair∈endpoints (SchemePreparation.prepare [] source target)) :
    let p:=SchemePreparation.prepare [] source target
    let action:=ComparisonSelectedBases.inputAction p σ
    ∃layout labels,
      build (ComparisonSelectedBases.inputNames p) (ComparisonSelectedBases.inputModes p)
        solved.fixedShapes ((action.ty pair.1).shape.subst solved.fixedShapes)=some layout ∧
      layout.shape=(action.ty pair.1).shape.subst solved.fixedShapes ∧
      Based (ComparisonSelectedBases.inputNames p) (ComparisonSelectedBases.inputModes p)
        solved.fixedShapes layout ∧
      Endpoint p.assumptions labels (ComparisonSelectedBases.inputTypeKeys p) action layout pair.1 ∧
      Endpoint p.assumptions labels (ComparisonSelectedBases.inputTypeKeys p) action layout pair.2 ∧
      (∀m∈ComparisonStructuralAlignment.tests (ComparisonSelectedBases.inputModes p),
        ∃g∈labels,g.expression=m) ∧
      (∀b : Basis,b.modes=ComparisonSelectedBases.inputModes p →
        ∀q∈b.modalPairs,∃g∈labels,g.expression=q.2) ∧
      (∀g∈labels,∀v∈g.expression.freeVariables,v∈ComparisonSelectedBases.inputModes p) := by
  let p:=SchemePreparation.prepare [] source target
  let action:=ComparisonSelectedBases.inputAction p σ
  have haw:=ComparisonSelectedBases.inputAction_prepared hw
  have has:=ComparisonSelectedBases.inputAction_supported hsp
  have hg:=prepared_guarded haw has hp
  have hmodel:=ComparisonShapeSolver.unify_sound (ComparisonShapeSolver.prepare_solved_iff.mp hshape).1
  have heq : ∀v,ComparisonShape.Equivalent p.assumptions (.var v) (solved.fixedShapes v) :=
    fun v φ hφ => (ComparisonShapeSolver.unify_factor
      (ComparisonShapeSolver.prepare_solved_iff.mp hshape).1 hφ v).symm
  obtain ⟨b,hb,_⟩:=normal_of_supported (ComparisonSelectedBases.inputNames p)
    (ComparisonSelectedBases.inputModes p) solved.fixedShapes hmodel heq
    (haw.1.2.1.ty pair.1) hg.left_defined hg.left_supported
  obtain ⟨layout,hbuild,hls,_,hbased⟩:=build_complete
    (ComparisonSelectedBases.inputNames p) (ComparisonSelectedBases.inputModes p) solved.fixedShapes _ hb
  have he:=build_endpoints hmodel heq (inputAction_fixed p σ)
    (haw.1.2.1.ty pair.1) hg.left_defined hg.left_supported
    (haw.1.2.1.ty pair.2) hg.right_defined hg.right_supported hg.subtype.shape_equivalent hbuild
  exact ⟨layout,observingLabels (ComparisonSelectedBases.inputModes p) hg.left_defined hg.right_defined,
    hbuild,hls,hbased,he.1,he.2,observingLabels_tests _ _,
    fun b hbm => observingLabels_basis _ _ b hbm,
    observingLabels_support _ _ hg.left_supported hg.right_supported⟩


theorem branch_compiled_images {shapeFuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {σ : CompareSubstitution} {world : Nat → Bool}
    (hshape : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (hw : PreparedWitnessUnder p σ)
    (hbranches : ComparisonSelectedBases.BranchPolynomials first p solved world σ) :
    ∃polynomials : Nat → CNF,∀n∈ComparisonSelectedBases.inputTypeKeys p,∃b,
      basis (ComparisonSelectedBases.inputNames p) (ComparisonSelectedBases.inputModes p)
        solved.fixedShapes (((ComparisonSelectedBases.inputAction p σ).type (.flex n)).shape.subst solved.fixedShapes)=some b ∧
      ComparisonLatticeCompiler.compile b ((ComparisonSelectedBases.inputAction p σ).type (.flex n))=
        some (polynomials n) := by
  let action:=ComparisonSelectedBases.inputAction p σ
  let polynomials : Nat → CNF:=fun n =>
    ((basis (ComparisonSelectedBases.inputNames p) (ComparisonSelectedBases.inputModes p)
      solved.fixedShapes ((action.type (.flex n)).shape.subst solved.fixedShapes)).bind
      (fun b => ComparisonLatticeCompiler.compile b (action.type (.flex n)))).getD []
  refine ⟨polynomials,?_⟩
  intro n hn
  have hv:=((ComparisonSelectedBases.mem_inputTypeKeys p n).mp hn).1
  have ht:=ComparisonSelectedBases.inputAction_type hw.1.1 hv
  obtain ⟨branch,hbranch,clauses,t,_,hc,_,_,hrep,he⟩:=hbranches.2 _ hv
  obtain ⟨raw,_,hs,_,hb⟩:=ComparisonSelectedBases.bases_origin hbranch
  have hmodel:=ComparisonShapeSolver.unify_sound (ComparisonShapeSolver.prepare_solved_iff.mp hshape).1
  have hsfix : branch.shape.subst solved.fixedShapes=branch.shape := by
    rw [hs]
    exact ComparisonShapeRetraction.fixedShapes_idempotent hshape _
  have hsame : (action.type (.flex n)).shape.subst solved.fixedShapes=branch.shape := by
    rw [ht]
    exact ((he.2.shape_equivalent.trans hrep.2.2) solved.fixedShapes hmodel).trans hsfix
  refine ⟨branch.basis,?_,?_⟩
  · change basis (ComparisonSelectedBases.inputNames p) (ComparisonSelectedBases.inputModes p)
      solved.fixedShapes ((action.type (.flex n)).shape.subst solved.fixedShapes)=some branch.basis
    rw [hsame]
    exact hb
  · change ComparisonLatticeCompiler.compile branch.basis (action.type (.flex n))=some (polynomials n)
    have h : ComparisonLatticeCompiler.compile branch.basis (action.type (.flex n))=some clauses := by
      change ComparisonLatticeCompiler.compile branch.basis ((ComparisonSelectedBases.inputAction p σ).type (.flex n))=some clauses
      rw [ht]
      exact hc
    simp only [polynomials,hsame,hb,Option.bind_some,h,Option.getD_some]

end ModalityInference.ComparisonSignedObservation
