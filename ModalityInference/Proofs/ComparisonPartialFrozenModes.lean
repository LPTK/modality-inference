import ModalityInference.Proofs.ComparisonPartialFrozenImages

namespace ModalityInference.ComparisonPartialStructuredCapsule

/-- Literal scalar subexpressions, retaining every residual and compound node. -/
def modeSubexpressions (m : ModExpr) : List ModExpr :=
  m :: match m with
  | .compose a b | .join a b | .meet a b | .leftResidual a b | .rightResidual a b =>
    modeSubexpressions a ++ modeSubexpressions b
  | .close a | .closeInv a | .future a | .capture a => modeSubexpressions a
  | _ => []

 theorem mode_image_mem_subexpressions (m : ModExpr) (ms : ModVar → ModExpr)
    {v : ModVar} (hv : v ∈ m.vars) : ms v ∈ modeSubexpressions (m.subst ms) := by
  induction m with
  | var w =>
    have he : v = w := Finset.mem_singleton.mp hv
    subst v
    change ms w ∈ modeSubexpressions (ms w)
    cases ms w <;> exact List.mem_cons_self
  | const _ => exact (Finset.notMem_empty v hv).elim
  | compose a b ia ib | join a b ia ib | meet a b ia ib
  | leftResidual a b ia ib | rightResidual a b ia ib =>
    apply List.mem_cons_of_mem
    exact (Finset.mem_union.mp hv).elim
      (fun h => List.mem_append_left _ (ia h))
      (fun h => List.mem_append_right _ (ib h))
  | close a ia | closeInv a ia | future a ia | capture a ia =>
    exact List.mem_cons_of_mem _ (ia hv)

/-- Literal scalar subexpressions of every annotation in an internal type. -/
def annotationSubexpressions : CompareTy → List ModExpr
  | .prod a b | .sum a b | .fn a b | .join a b | .meet a b =>
    annotationSubexpressions a ++ annotationSubexpressions b
  | .modal a m => annotationSubexpressions a ++ modeSubexpressions m
  | _ => []

 theorem mode_image_mem_annotations (body : Ty) (ts : TypeVar → CompareTy)
    (ms : ModVar → ModExpr) {v : ModVar} (hv : v ∈ body.modVars) :
    ms v ∈ annotationSubexpressions ((CompareTy.ofTy body).subst ts ms) := by
  induction body with
  | var _ | unit | credit => exact (Finset.notMem_empty v hv).elim
  | prod a b ia ib | sum a b ia ib | fn a b ia ib =>
    exact (Finset.mem_union.mp hv).elim
      (fun h => List.mem_append_left _ (ia h))
      (fun h => List.mem_append_right _ (ib h))
  | modal a m ia =>
    exact (Finset.mem_union.mp hv).elim
      (fun h => List.mem_append_left _ (ia h))
      (fun h => List.mem_append_right _ (mode_image_mem_subexpressions m ms h))

/-- Candidate modality images depend only on the public endpoint. -/
def frozenModeCandidates (endpoint : Ty) : List ModExpr :=
  (frozenFragments (.ofTy endpoint) none).flatMap annotationSubexpressions

 theorem frozen_modes_below {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (body : Ty) (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    {endpoint : Ty} {m : ModExpr}
    (hh : FrozenHead ((CompareTy.ofTy body).subst ts ms))
    (hm : ¬Entails Δ (.defined m))
    (h : AlgebraSubtype Δ (.modal ((CompareTy.ofTy body).subst ts ms) m) (.ofTy endpoint)) :
    ∀ v ∈ body.modVars, ms v ∈ frozenModeCandidates endpoint := by
  intro v hv
  exact List.mem_flatMap.mpr ⟨_, frozen_fragment_below hΔ hh hm h,
    mode_image_mem_annotations body ts ms hv⟩

 theorem frozen_modes_above {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (body : Ty) (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    {endpoint : Ty} {m : ModExpr}
    (hh : FrozenHead ((CompareTy.ofTy body).subst ts ms))
    (hm : ¬Entails Δ (.defined m))
    (h : AlgebraSubtype Δ (.ofTy endpoint) (.modal ((CompareTy.ofTy body).subst ts ms) m)) :
    ∀ v ∈ body.modVars, ms v ∈ frozenModeCandidates endpoint := by
  intro v hv
  exact List.mem_flatMap.mpr ⟨_, frozen_fragment_above hΔ hh hm h,
    mode_image_mem_annotations body ts ms hv⟩

/-- The original modality keys are retained, including keys used in several
compound source annotations. -/
def frozenModeBindings (body : Ty) (ms : ModVar → ModExpr) : List (ModVar × ModExpr) :=
  body.modeVariables.map fun v => (v, ms v)

 theorem frozenModeBindings_keys (body : Ty) (ms : ModVar → ModExpr) :
    (frozenModeBindings body ms).map Prod.fst = body.modeVariables := by
  simp only [frozenModeBindings, List.map_map, Function.comp_def]
  exact List.map_id _

 theorem frozenModeBindings_lookup (body : Ty) (ms : ModVar → ModExpr) {v : ModVar}
    (hv : v ∈ body.modVars) : (frozenModeBindings body ms).lookup v = some (ms v) :=
  lookup_map_self _ _ ((body.mem_modeVariables v).mpr hv)

 theorem frozenModeBindings_members {body : Ty} {ms : ModVar → ModExpr}
    {entry : ModVar × ModExpr} (he : entry ∈ frozenModeBindings body ms) :
    entry.1 ∈ body.modVars ∧ entry.2 = ms entry.1 := by
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp he
  exact ⟨(body.mem_modeVariables v).mp hv, rfl⟩

 theorem frozen_mode_bindings_below {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (body : Ty) (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    {endpoint : Ty} {m : ModExpr}
    (hh : FrozenHead ((CompareTy.ofTy body).subst ts ms))
    (hm : ¬Entails Δ (.defined m))
    (h : AlgebraSubtype Δ (.modal ((CompareTy.ofTy body).subst ts ms) m) (.ofTy endpoint)) :
    ∀ entry ∈ frozenModeBindings body ms, entry.2 ∈ frozenModeCandidates endpoint := by
  intro entry he
  obtain ⟨hv, hi⟩ := frozenModeBindings_members he
  rw [hi]
  exact frozen_modes_below hΔ body ts ms hh hm h entry.1 hv

 theorem frozen_mode_bindings_above {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (body : Ty) (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    {endpoint : Ty} {m : ModExpr}
    (hh : FrozenHead ((CompareTy.ofTy body).subst ts ms))
    (hm : ¬Entails Δ (.defined m))
    (h : AlgebraSubtype Δ (.ofTy endpoint) (.modal ((CompareTy.ofTy body).subst ts ms) m)) :
    ∀ entry ∈ frozenModeBindings body ms, entry.2 ∈ frozenModeCandidates endpoint := by
  intro entry he
  obtain ⟨hv, hi⟩ := frozenModeBindings_members he
  rw [hi]
  exact frozen_modes_above hΔ body ts ms hh hm h entry.1 hv

end ModalityInference.ComparisonPartialStructuredCapsule
