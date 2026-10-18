import ModalityInference.Proofs.ComparisonSignedBranchImages
import ModalityInference.Proofs.ComparisonLayoutModePullback
import ModalityInference.Proofs.ComparisonPropagationModes
import ModalityInference.Proofs.ComparisonPreparedBounds
import ModalityInference.Proofs.ComparisonBareShapes

namespace ModalityInference.ComparisonSignedBranchImages
open ComparisonSelectedBases ComparisonAlgebra ComparisonControls ComparisonInterpolation
  ComparisonShapeSolver ComparisonShapeRetraction
open SchemePreparation ComparisonSelectedBases

theorem sourceRenaming_rigid_origin {ambient : Bounds} {source target : Scheme}
    {v : TypeVar} {n : Nat}
    (h : TypeVar.rigid n∈((prepare ambient source target).sourceRenaming.type v).typeVars) :
    v=.rigid n := by
  cases v with
  | rigid k =>
    have he : TypeVar.rigid n=TypeVar.rigid k := by
      simpa [Substitution.type,TypeExpr.typeVars] using h
    exact he.symm
  | flex k =>
    by_cases hk : k∈source.typeParams
    · obtain ⟨i,he,_,_⟩:=prepare_source_type_param ambient source target hk
      simp [he,TypeExpr.typeVars] at h
    · have he:=prepare_source_type_fixed ambient source target (.flex k) (by simpa using hk)
      simp [he,TypeExpr.typeVars] at h

theorem sourceRenaming_ty_rigid_origin {ambient : Bounds} {source target : Scheme}
    {a : Ty} {n : Nat}
    (h : TypeVar.rigid n∈((prepare ambient source target).sourceRenaming.ty a).typeVars) :
    TypeVar.rigid n∈a.typeVars := by
  obtain ⟨v,hv,he⟩:=(TypeExpr.mem_typeVars_subst _ _ _ _).mp h
  exact sourceRenaming_rigid_origin he ▸ hv

theorem prepared_rigid_input {ambient : Bounds} {source target : Scheme} {n : Nat}
    (h : TypeVar.rigid n∈inputNames (prepare ambient source target)) :
    n<(prepare ambient source target).firstType := by
  have hh:=(mem_inputNames _ _).mp h
  simp only [ComparisonWitnessRestriction.inputTypes,Finset.mem_union] at hh
  rcases hh with ((ha|hb)|hs)|ht
  · exact (Bounds.bounded_iff _ _ _).mp
      (prepare_assumptions_bounded_first ambient source target) |>.1 _ ha
  · obtain ⟨c,hc,hv⟩:=(Bounds.mem_typeVars_iff _ _).mp hb
    obtain ⟨d,hd,rfl⟩:=List.mem_map.mp hc
    obtain ⟨v,hv,he⟩:=(Constraint.mem_typeVars_substitution _ _ _).mp hv
    have heq:=sourceRenaming_rigid_origin he
    have hn : TypeVar.rigid n∈source.bounds.typeVars :=
      (Bounds.mem_typeVars_iff _ _).mpr ⟨d,hd,heq ▸ hv⟩
    exact original_type_lt_first (v:=.rigid n) (by
      simp [originalTypeIds,Bounds.mem_typeVariables,hn])
  · have hn:=sourceRenaming_ty_rigid_origin (ambient:=ambient) (source:=source) (target:=target) hs
    exact original_type_lt_first (v:=.rigid n) (by
      simp [originalTypeIds,TypeExpr.mem_typeVariables,hn])
  · exact (TypeExpr.bounded_iff _ _ _).mp
      (prepare_targetType_bounded_first ambient source target) |>.1 _ ht


 theorem select_mode {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world : Nat→Bool}
    {images : List (Nat×CompareTy)} {modes : List (Nat×ModExpr)} {result : CompareSubstitution}
    (h : select first p solved world images modes=some result) :
    result.mode=({modes:=modes}:CompareSubstitution).mode := by
  funext v
  cases v <;> simp [CompareSubstitution.mode,(select_spec h).1]

theorem select_fixed {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world : Nat→Bool}
    {images : List (Nat×CompareTy)} {modes : List (Nat×ModExpr)} {result : CompareSubstitution}
    (h : select first p solved world images modes=some result)
    (v : TypeVar) (hv : ∀n∈inputTypeKeys p,v≠.flex n) : result.type v=.var v := by
  cases v with
  | rigid => rfl
  | flex n =>
    have hn : result.types.lookup n=none := by
      apply List.lookup_eq_none_iff.mpr
      intro entry he
      have hk : entry.1∈inputTypeKeys p := (select_spec h).2.1 ▸ List.mem_map.mpr ⟨entry,he,rfl⟩
      exact bne_iff_ne.mpr (fun heq => hv entry.1 hk (congrArg TypeVar.flex heq))
    simp [CompareSubstitution.type,hn]

theorem select_domains {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world : Nat→Bool}
    {images : List (Nat×CompareTy)} {modes : List (Nat×ModExpr)} {result : CompareSubstitution}
    (h : select first p solved world images modes=some result)
    (hm : ∀entry∈modes,p.firstMode≤entry.1) : result.DomainsAbove p.firstType p.firstMode := by
  refine ⟨?_,?_⟩
  · intro entry he
    have hk : entry.1∈inputTypeKeys p := (select_spec h).2.1 ▸ List.mem_map.mpr ⟨entry,he,rfl⟩
    exact ((mem_inputTypeKeys p entry.1).mp hk).2
  · simpa only [(select_spec h).1] using hm

theorem select_representable {shapeFuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world parameters : Nat→Bool}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (hw : (layout first p solved).theory.eval world=true)
    {r : CNF} {images : List (Nat×CompareTy)}
    (hr : (input (entries first p solved)).reconstruct r parameters=some images)
    {modes : List (Nat×ModExpr)}
    (hm : ComparisonModeRestriction.Fixed p.assumptions ({modes:=modes}:CompareSubstitution).mode)
    {result : CompareSubstitution} (h : select first p solved world images modes=some result) :
    ∀entry∈result.types,Representable p.assumptions
      (((solved.resolveAll (.flex entry.1)).subst ((layout first p solved).decode world)).subst solved.fixedShapes)
      entry.2 := by
  intro entry he
  obtain ⟨raw,hraw,heq⟩ := (select_spec h).2.2 entry he
  rw [heq]
  obtain ⟨key,_,ht⟩ := pick_reifyImage hr hraw
  have hn : entry.1∈inputTypeKeys p := (select_spec h).2.1 ▸ List.mem_map.mpr ⟨entry,he,rfl⟩
  have hv := (mem_inputTypeKeys p entry.1).mp hn |>.1
  exact ComparisonObserverModePullback.representable hm (reifyImage_representable hs hw hv ht)

theorem select_wellShaped {shapeFuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world parameters : Nat→Bool}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (hw : (layout first p solved).theory.eval world=true)
    {r : CNF} {images : List (Nat×CompareTy)}
    (hr : (input (entries first p solved)).reconstruct r parameters=some images)
    {modes : List (Nat×ModExpr)}
    (hm : ComparisonModeRestriction.Fixed p.assumptions ({modes:=modes}:CompareSubstitution).mode)
    {result : CompareSubstitution} (h : select first p solved world images modes=some result) :
    result.WellShaped p.assumptions := fun entry he => (select_representable hs hw hr hm h entry he).1

theorem select_support {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world parameters : Nat→Bool}
    {r : CNF} {images : List (Nat×CompareTy)}
    (hr : (input (entries first p solved)).reconstruct r parameters=some images)
    {modes : List (Nat×ModExpr)}
    (hm : ∀v∈inputModes p,∀w∈(({modes:=modes}:CompareSubstitution).mode v).vars,w∈inputModes p)
    {result : CompareSubstitution} (h : select first p solved world images modes=some result) :
    ∀entry∈result.types,Supports (·∈inputNames p) (·∈inputModes p) entry.2 := by
  intro entry he
  obtain ⟨raw,hraw,heq⟩ := (select_spec h).2.2 entry he
  rw [heq]
  obtain ⟨key,_,ht⟩ := pick_reifyImage hr hraw
  exact (reifyImage_support ht).subst (fun _ hv=>hv) hm

theorem select_type_support {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world parameters : Nat→Bool}
    {r : CNF} {images : List (Nat×CompareTy)}
    (hr : (input (entries first p solved)).reconstruct r parameters=some images)
    {modes : List (Nat×ModExpr)}
    (hm : ∀v∈inputModes p,∀w∈(({modes:=modes}:CompareSubstitution).mode v).vars,w∈inputModes p)
    {result : CompareSubstitution} (h : select first p solved world images modes=some result)
    {v : TypeVar} (hv : v∈inputNames p) :
    Supports (·∈inputNames p) (·∈inputModes p) (result.type v) := by
  cases v with
  | rigid => exact hv
  | flex n =>
    cases hl : result.types.lookup n with
    | none => simpa only [CompareSubstitution.type,hl,Option.getD_none] using hv
    | some a =>
      have hmem : (n,a)∈result.types := by
        obtain ⟨l,r,he,_⟩:=List.lookup_eq_some_iff.mp hl
        simp [he]
      simpa only [CompareSubstitution.type,hl,Option.getD_some] using select_support hr hm h (n,a) hmem

theorem select_ty_support {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world parameters : Nat→Bool}
    {r : CNF} {images : List (Nat×CompareTy)}
    (hr : (input (entries first p solved)).reconstruct r parameters=some images)
    {modes : List (Nat×ModExpr)}
    (hm : ∀v∈inputModes p,∀w∈(({modes:=modes}:CompareSubstitution).mode v).vars,w∈inputModes p)
    {result : CompareSubstitution} (h : select first p solved world images modes=some result)
    {a : Ty} (ht : ∀v∈a.typeVars,v∈inputNames p) (hmode : ∀v∈a.modVars,v∈inputModes p) :
    Supports (·∈inputNames p) (·∈inputModes p) (result.ty a) := by
  have hbase : Supports (·∈inputNames p) (·∈inputModes p) (.ofTy a) := by
    induction a with
    | var => simpa [CompareTy.ofTy,Supports,TypeExpr.typeVars] using ht
    | unit | credit => trivial
    | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
      simp only [TypeExpr.typeVars,TypeExpr.modVars,Finset.mem_union,or_imp,forall_and] at ht hmode
      exact ⟨iha ht.1 hmode.1,ihb ht.2 hmode.2⟩
    | modal a m ih =>
      simp only [TypeExpr.typeVars,TypeExpr.modVars,Finset.mem_union,or_imp,forall_and] at ht hmode
      exact ⟨ih ht hmode.1,hmode.2⟩
  apply hbase.subst (fun _ hv=>select_type_support hr hm h hv)
  simpa only [select_mode h] using hm


theorem select_wellFormed {shapeFuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world parameters : Nat→Bool}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (hw : (layout first p solved).theory.eval world=true)
    {r : CNF} {images : List (Nat×CompareTy)}
    (hr : (input (entries first p solved)).reconstruct r parameters=some images)
    {modes : List (Nat×ModExpr)}
    (hm : ComparisonModeRestriction.Fixed p.assumptions ({modes:=modes}:CompareSubstitution).mode)
    {result : CompareSubstitution} (h : select first p solved world images modes=some result) :
    result.WellFormedUnder p.assumptions := by
  refine ⟨?_,?_⟩
  · exact (CompareSubstitution.wellFormedUnder_of_images
      (σ:={types:=result.types}) (by
        have hd:=select_defined hs hw hr hm h
        exact hd) (by simp)).types
  · rw [select_mode h]
    exact fun v η hη=>hm.total η hη v

theorem select_type_shape {shapeFuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world parameters : Nat→Bool}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (ha : (anchorTheory first p solved).eval world=true)
    (hrigid : ∀n,TypeVar.rigid n∈inputNames p→n<p.firstType)
    {r : CNF} {images : List (Nat×CompareTy)}
    (hr : (input (entries first p solved)).reconstruct r parameters=some images)
    {modes : List (Nat×ModExpr)}
    (hm : ComparisonModeRestriction.Fixed p.assumptions ({modes:=modes}:CompareSubstitution).mode)
    {result : CompareSubstitution} (h : select first p solved world images modes=some result)
    {v : TypeVar} (hv : v∈inputNames p) :
    (result.type v).shape.subst solved.fixedShapes=
      ((solved.resolveAll v).subst ((layout first p solved).decode world)).subst solved.fixedShapes := by
  have hanchor:=((layout first p solved).matchTheory_correct solved.fixedShapes
    (anchorEquations p solved) world (anchorEquations_scope first p solved)).mp ha
  have hsmall (v : TypeVar) (hv : v∈inputNames p) (hlt : v.index<p.firstType) :
      (result.type v).shape.subst solved.fixedShapes=
        ((solved.resolveAll v).subst ((layout first p solved).decode world)).subst solved.fixedShapes := by
    have hfix:=select_fixed h v (fun n hn he=>by
      have hh:=((mem_inputTypeKeys p n).mp hn).2
      subst v
      exact (Nat.not_lt_of_ge hh) hlt)
    rw [hfix]
    exact (hanchor.2 (solved.resolveAll v,solved.fixedShapes v)
      (List.mem_append_left _ (List.mem_map.mpr ⟨v,List.mem_filter.mpr ⟨hv,by simpa using hlt⟩,rfl⟩))).symm
  cases v with
  | rigid n => exact hsmall _ hv (hrigid n hv)
  | flex n =>
    by_cases hlt : n<p.firstType
    · exact hsmall _ hv hlt
    · have hk : n∈result.types.map Prod.fst :=
        (select_spec h).2.1 ▸ (mem_inputTypeKeys p n).mpr ⟨hv,Nat.le_of_not_gt hlt⟩
      cases hl : result.types.lookup n with
      | none =>
        obtain ⟨entry,he,hkey⟩:=List.mem_map.mp hk
        have hne:=List.lookup_eq_none_iff.mp hl entry he
        simp [hkey] at hne
      | some a =>
        have hmem : (n,a)∈result.types := by
          obtain ⟨l,r,he,_⟩:=List.lookup_eq_some_iff.mp hl
          simp [he]
        have hre:=select_representable hs hanchor.1 hr hm h (n,a) hmem
        have he:=hre.2.2 solved.fixedShapes
          (ComparisonShapeSolver.unify_sound (ComparisonShapeSolver.prepare_solved_iff.mp hs).1)
        simpa only [CompareSubstitution.type,hl,Option.getD_some,fixedShapes_idempotent hs] using he

theorem select_ty_shape {shapeFuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world parameters : Nat→Bool}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (ha : (anchorTheory first p solved).eval world=true)
    (hrigid : ∀n,TypeVar.rigid n∈inputNames p→n<p.firstType)
    {r : CNF} {images : List (Nat×CompareTy)}
    (hr : (input (entries first p solved)).reconstruct r parameters=some images)
    {modes : List (Nat×ModExpr)}
    (hm : ComparisonModeRestriction.Fixed p.assumptions ({modes:=modes}:CompareSubstitution).mode)
    {result : CompareSubstitution} (h : select first p solved world images modes=some result)
    (a : Ty) (ht : ∀v∈a.typeVars,v∈inputNames p) :
    (result.ty a).shape.subst solved.fixedShapes=
      (((ComparisonShape.ofTy a).subst solved.resolveAll).subst
        ((layout first p solved).decode world)).subst solved.fixedShapes := by
  rw [result.ty_shape,subst_comp]
  simp only [subst_comp]
  apply subst_congr
  intro v hv
  simpa only [subst_comp] using
    select_type_shape hs ha hrigid hr hm h (ht v ((mem_vars_ofTy a v).mp hv))


theorem constraintPairs_resolved {bounds : Bounds} {ρ : TypeVar→ComparisonShape}
    (hm : ComparisonShape.Models bounds ρ) {c : Constraint} (hc : c∈bounds)
    {pair : Ty×Ty} (hp : pair∈ComparisonStructuralEndpoints.constraintPairs c) :
    (ComparisonShape.ofTy pair.1).subst ρ=(ComparisonShape.ofTy pair.2).subst ρ := by
  have hmem (a b) (h : (a,b)∈ComparisonShape.pairs [c]) :
      a.subst ρ=b.subst ρ := by
    apply hm (a,b)
    simp only [ComparisonShape.pairs,List.flatMap_cons,List.flatMap_nil,List.append_nil] at h
    exact List.mem_flatMap.mpr ⟨c,hc,h⟩
  cases c with
  | sub a b =>
    obtain rfl:=List.mem_singleton.mp hp
    exact hmem _ _ (by simp [ComparisonShape.pairs])
  | equiv a b =>
    have he:=hmem (ComparisonShape.ofTy a) (ComparisonShape.ofTy b) (by simp [ComparisonShape.pairs])
    rcases List.mem_cons.mp hp with rfl|hp
    · exact he
    · obtain rfl:=List.mem_singleton.mp hp
      exact he.symm
  | equal v a =>
    have he:=hmem (.var v) (ComparisonShape.ofTy a) (by simp [ComparisonShape.pairs])
    rcases List.mem_cons.mp hp with rfl|hp
    · exact he
    · obtain rfl:=List.mem_singleton.mp hp
      exact he.symm
  | mode | defined => cases hp

theorem endpoints_resolved {fuel : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved}
    (hs : ComparisonShapeSolver.prepare fuel p=.success (.solved solved))
    {pair : Ty×Ty} (hp : pair∈ComparisonSignedObservation.endpoints p) :
    (ComparisonShape.ofTy pair.1).subst solved.resolveAll=
      (ComparisonShape.ofTy pair.2).subst solved.resolveAll := by
  have hmodels:=prepare_sound hs
  rcases ComparisonSignedObservation.mem_endpoints.mp hp with hc|⟨c,hc,hpair⟩|rfl
  · exact constraintPairs_resolved hmodels.1 hc List.mem_cons_self
  · apply constraintPairs_resolved (bounds:=p.sourceBounds) ?_ hc hpair
    exact fun pair hp=>hmodels.2 pair (List.mem_append_left _ hp)
  · exact hmodels.2 _ (List.mem_append_right _ List.mem_cons_self)

theorem select_endpoint_shapes {shapeFuel first : Nat} {ambient : Bounds} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {world parameters : Nat→Bool}
    (hs : ComparisonShapeSolver.prepare shapeFuel (prepare ambient source target)=.success (.solved solved))
    (ha : (anchorTheory first (prepare ambient source target) solved).eval world=true)
    {r : CNF} {images : List (Nat×CompareTy)}
    (hr : (input (entries first (prepare ambient source target) solved)).reconstruct r parameters=some images)
    {modes : List (Nat×ModExpr)}
    (hm : ComparisonModeRestriction.Fixed (prepare ambient source target).assumptions
      ({modes:=modes}:CompareSubstitution).mode)
    {result : CompareSubstitution}
    (h : select first (prepare ambient source target) solved world images modes=some result)
    {pair : Ty×Ty} (hp : pair∈ComparisonSignedObservation.endpoints (prepare ambient source target)) :
    ComparisonShape.Equivalent (prepare ambient source target).assumptions
      (result.ty pair.1).shape (result.ty pair.2).shape := by
  apply (prepare_fixed_equivalent hs _ _).mpr
  have hi:=ComparisonSignedObservation.endpoints_input hp
  have hrn : ∀n,TypeVar.rigid n∈inputNames (prepare ambient source target)→
      n<(prepare ambient source target).firstType := fun n hn=>prepared_rigid_input hn
  rw [select_ty_shape hs ha hrn hr hm h pair.1 (fun v hv=>(mem_inputNames _ _).mpr (hi.1 hv)),
    select_ty_shape hs ha hrn hr hm h pair.2 (fun v hv=>(mem_inputNames _ _).mpr (hi.2.1 hv)),
    endpoints_resolved hs hp]

end ModalityInference.ComparisonSignedBranchImages
