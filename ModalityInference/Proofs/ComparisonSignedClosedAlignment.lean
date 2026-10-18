import ModalityInference.Proofs.ComparisonSignedBranchAlignment

namespace ModalityInference.ComparisonSignedClosedAlignment
open ComparisonSelectedBases ComparisonSignedBranchImages ComparisonAlgebra ComparisonControls
  ComparisonSignedObservation ComparisonStructuralLayout ComparisonInterpolation

 def substitutedLabels {Δ : Bounds} {ms : ModVar→ModExpr}
    (h : ComparisonModeRestriction.Fixed Δ ms) (raw : List (GuardedMode Δ)) : List (GuardedMode Δ) :=
  raw.map fun m=>GuardedMode.ofDefined (m.expression.subst ms) (by
    intro η hη
    exact h.defined (show Entails Δ (.defined m.expression) from m.defined) η hη)

theorem substitutedLabels_cover {Δ : Bounds} {ms : ModVar→ModExpr}
    (h : ComparisonModeRestriction.Fixed Δ ms) (raw : List (GuardedMode Δ)) :
    ∀m∈raw,∃n∈substitutedLabels h raw,n.expression=m.expression.subst ms := by
  intro m hm
  exact ⟨_,List.mem_map.mpr ⟨m,hm,rfl⟩,rfl⟩

theorem substitutedLabels_support {Δ : Bounds} {ms : ModVar→ModExpr}
    (h : ComparisonModeRestriction.Fixed Δ ms) {raw : List (GuardedMode Δ)} {modes : List ModVar}
    (hr : ∀m∈raw,∀v∈m.expression.freeVariables,v∈modes)
    (hm : ∀v∈modes,∀w∈(ms v).vars,w∈modes) :
    ∀m∈substitutedLabels h raw,∀v∈m.expression.freeVariables,v∈modes := by
  intro m hmem v hv
  obtain ⟨n,hn,rfl⟩:=List.mem_map.mp hmem
  apply ModExpr.support_subst n.expression ms ?_ v ((n.expression.subst ms).mem_freeVariables v |>.mp hv)
  intro w hw
  exact hm w (hr n hn w ((n.expression.mem_freeVariables w).mpr hw))

theorem Endpoint.labels_mono {Δ labels extra keys σ layout a}
    (he : Endpoint Δ labels keys σ layout a) (hh : ∀m∈labels,m∈extra) :
    Endpoint Δ extra keys σ layout a := by
  induction he with
  | image hs hr => exact .image hs hr
  | fixed hu hf hm => exact .fixed hu hf hm
  | unit hm => exact .unit hm
  | credit hm => exact .credit hm
  | node _ _ ihl ihr => exact .node ihl ihr
  | modal _ hm ih =>
    obtain ⟨m,hmem,he⟩:=hm
    exact .modal ih ⟨m,hh m hmem,he⟩

theorem defined_of_annotations {Δ : Bounds} {σ : CompareSubstitution}
    (ht : ∀v,(σ.type v).DefinedUnder Δ) (a : Ty)
    (hg : ∀m∈ComparisonAnnotations.expressions a,Entails Δ (.defined (m.subst σ.mode))) :
    (σ.ty a).DefinedUnder Δ := by
  induction a with
  | var v => exact ht v
  | unit | credit => intro η hη c hc;cases hc
  | prod a b iha ihb =>
    exact CompareTy.definedUnder_prod_iff.mpr
      ⟨iha (fun m hm=>hg m (List.mem_append_left _ hm)),
       ihb (fun m hm=>hg m (List.mem_append_right _ hm))⟩
  | sum a b iha ihb =>
    exact CompareTy.definedUnder_sum_iff.mpr
      ⟨iha (fun m hm=>hg m (List.mem_append_left _ hm)),
       ihb (fun m hm=>hg m (List.mem_append_right _ hm))⟩
  | fn a b iha ihb =>
    exact CompareTy.definedUnder_fn_iff.mpr
      ⟨iha (fun m hm=>hg m (List.mem_append_left _ hm)),
       ihb (fun m hm=>hg m (List.mem_append_right _ hm))⟩
  | modal a m ih =>
    exact CompareTy.definedUnder_modal_iff.mpr
      ⟨ih (fun n hn=>hg n (List.mem_cons_of_mem _ hn)),hg m List.mem_cons_self⟩

/-- Every actual returned image and whole public endpoint receives its layout
without assuming any required type comparison. Only the independently checked
scalar definedness obligations are used. -/
theorem select_alignment {shapeFuel first : Nat} {ambient : Bounds} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {world parameters : Nat→Bool}
    (hs : ComparisonShapeSolver.prepare shapeFuel (SchemePreparation.prepare ambient source target)=.success (.solved solved))
    (ha : (anchorTheory first (SchemePreparation.prepare ambient source target) solved).eval world=true)
    {r : CNF} {images : List (Nat×CompareTy)}
    (hr : (input (entries first (SchemePreparation.prepare ambient source target) solved)).reconstruct r parameters=some images)
    {modes : List (Nat×ModExpr)}
    (hm : ComparisonModeRestriction.Fixed (SchemePreparation.prepare ambient source target).assumptions
      ({modes:=modes}:CompareSubstitution).mode)
    (hms : ∀v∈inputModes (SchemePreparation.prepare ambient source target),
      ∀w∈(({modes:=modes}:CompareSubstitution).mode v).vars,
        w∈inputModes (SchemePreparation.prepare ambient source target))
    {result : CompareSubstitution}
    (h : select first (SchemePreparation.prepare ambient source target) solved world images modes=some result)
    {pair : Ty×Ty} (hp : pair∈endpoints (SchemePreparation.prepare ambient source target))
    (hguards : ∀a∈[pair.1,pair.2],∀m∈ComparisonAnnotations.expressions a,
      Entails (SchemePreparation.prepare ambient source target).assumptions (.defined (m.subst result.mode))) :
    let p:=SchemePreparation.prepare ambient source target
    ∃layout closed,
      build (inputNames p) (inputModes p) solved.fixedShapes
        ((result.ty pair.1).shape.subst solved.fixedShapes)=some layout ∧
      layout.shape=(result.ty pair.1).shape.subst solved.fixedShapes ∧
      Based (inputNames p) (inputModes p) solved.fixedShapes layout ∧
      Endpoint p.assumptions closed (inputTypeKeys p) result layout pair.1 ∧
      Endpoint p.assumptions closed (inputTypeKeys p) result layout pair.2 ∧
      (∀m∈ComparisonStructuralAlignment.tests (inputModes p),∃n∈closed,n.expression=m) ∧
      (∀m∈ComparisonStructuralLayout.labels p.assumptions (inputModes p),
        ∃n∈closed,n.expression=m.expression.subst result.mode) ∧
      (∀m∈closed,∀v∈m.expression.freeVariables,v∈inputModes p) := by
  let p:=SchemePreparation.prepare ambient source target
  have hanchor:=((ComparisonSelectedBases.layout first p solved).matchTheory_correct solved.fixedShapes
    (anchorEquations p solved) world (anchorEquations_scope first p solved)).mp ha
  have hw:=select_wellShaped hs hanchor.1 hr hm h
  have hd:=select_wellFormed hs hanchor.1 hr hm h
  have hi:=endpoints_input hp
  have hlsp:=select_ty_support hr hms h (a:=pair.1)
    (fun v hv=>(mem_inputNames _ _).mpr (hi.1 hv))
    (fun v hv=>(mem_inputModes _ _).mpr (hi.2.2.1 hv))
  have hrsp:=select_ty_support hr hms h (a:=pair.2)
    (fun v hv=>(mem_inputNames _ _).mpr (hi.2.1 hv))
    (fun v hv=>(mem_inputModes _ _).mpr (hi.2.2.2 hv))
  have hld:=defined_of_annotations hd.types pair.1 (hguards _ List.mem_cons_self)
  have hrd:=defined_of_annotations hd.types pair.2 (hguards _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hmodel:=ComparisonShapeSolver.unify_sound (ComparisonShapeSolver.prepare_solved_iff.mp hs).1
  have hshapes : ∀v,ComparisonShape.Equivalent p.assumptions (.var v) (solved.fixedShapes v) :=
    fun v φ hφ=>(ComparisonShapeSolver.unify_factor (ComparisonShapeSolver.prepare_solved_iff.mp hs).1 hφ v).symm
  obtain ⟨basis,hbasis,_⟩:=ComparisonStructuralBasis.normal_of_supported
    (inputNames p) (inputModes p) solved.fixedShapes hmodel hshapes (hw.ty pair.1) hld hlsp
  obtain ⟨layout,hbuild,hshape,_,hbased⟩:=build_complete
    (inputNames p) (inputModes p) solved.fixedShapes _ hbasis
  have he:=select_endpoint_shapes hs ha hr hm h hp
  have hendpoints:=build_endpoints hmodel hshapes (select_fixed h)
    (hw.ty pair.1) hld hlsp (hw.ty pair.2) hrd hrsp he hbuild
  have hfixed : ComparisonModeRestriction.Fixed p.assumptions result.mode := select_mode h ▸ hm
  let base:=observingLabels (inputModes p) hld hrd
  let closed:=base++substitutedLabels hfixed (ComparisonStructuralLayout.labels p.assumptions (inputModes p))
  refine ⟨layout,closed,hbuild,hshape,hbased,
    Endpoint.labels_mono hendpoints.1 (fun _ h=>List.mem_append_left _ h),
    Endpoint.labels_mono hendpoints.2 (fun _ h=>List.mem_append_left _ h),?_,?_,?_⟩
  · intro m hm
    obtain ⟨n,hn,he⟩:=observingLabels_tests (modes:=inputModes p) hld hrd m hm
    exact ⟨n,List.mem_append_left _ hn,he⟩
  · intro m hm
    obtain ⟨n,hn,he⟩:=substitutedLabels_cover hfixed _ m hm
    exact ⟨n,List.mem_append_right _ hn,he⟩
  · intro m hm
    rcases List.mem_append.mp hm with hm|hm
    · exact observingLabels_support hld hrd hlsp hrsp m hm
    · apply substitutedLabels_support hfixed (labels_support p.assumptions (inputModes p)) ?_ m hm
      simpa only [select_mode h] using hms

end ModalityInference.ComparisonSignedClosedAlignment
