import ModalityInference.Proofs.ComparisonPartialOperandGrammar
import ModalityInference.Proofs.ComparisonPartialFrozenModes

namespace ModalityInference.ComparisonPartialStructuredCapsule

open ComparisonDefinedCovers (Refines)

/-- Literal images allowed by a frozen structured context. The grammar depth
and every generating fragment depend only on the public endpoint. -/
def structuredImageCandidates (endpoint : Ty) : List CompareTy :=
  (operandGrammar (pairDepth endpoint) endpoint).flatMap subtrees

/-- Exact scalar syntax allowed by a frozen structured context, including
subexpressions of compound annotations. -/
def structuredModeCandidates (endpoint : Ty) : List ModExpr :=
  (operandGrammar (pairDepth endpoint) endpoint).flatMap annotationSubexpressions

theorem structuredImageCandidates_public (endpoint : Ty) {a : CompareTy}
    (ha : a ∈ structuredImageCandidates endpoint) : Public a := by
  obtain ⟨fragment, hf, ha⟩ := List.mem_flatMap.mp ha
  exact subtrees_public (operandGrammar_public _ _ hf) ha

/-- Every occurrence retains its original witness image; the statement does
not choose images independently for different occurrences. -/
theorem structured_images {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) (hR : Residual Δ)
    (body : Ty) (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    {endpoint : Ty} {m : ModExpr} {lower : Bool}
    (hm : ¬Entails Δ (.defined m))
    (h : Refines Δ lower (.ofTy endpoint)
      (.modal ((CompareTy.ofTy body).subst ts ms) m)) :
    ∀ v ∈ body.typeVars, ts v ∈ structuredImageCandidates endpoint := by
  intro v hv
  exact List.mem_flatMap.mpr ⟨_, internal_operandGrammar_complete hΔ hR hm h,
    image_mem_subtrees body ts ms hv⟩

theorem structured_modes {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) (hR : Residual Δ)
    (body : Ty) (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    {endpoint : Ty} {m : ModExpr} {lower : Bool}
    (hm : ¬Entails Δ (.defined m))
    (h : Refines Δ lower (.ofTy endpoint)
      (.modal ((CompareTy.ofTy body).subst ts ms) m)) :
    ∀ v ∈ body.modVars, ms v ∈ structuredModeCandidates endpoint := by
  intro v hv
  exact List.mem_flatMap.mpr ⟨_, internal_operandGrammar_complete hΔ hR hm h,
    mode_image_mem_annotations body ts ms hv⟩

theorem structured_bindings {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) (hR : Residual Δ)
    (body : Ty) (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    {endpoint : Ty} {m : ModExpr} {lower : Bool}
    (hm : ¬Entails Δ (.defined m))
    (h : Refines Δ lower (.ofTy endpoint)
      (.modal ((CompareTy.ofTy body).subst ts ms) m)) :
    ∀ entry ∈ frozenBindings body ts, entry.2 ∈ structuredImageCandidates endpoint := by
  intro entry he
  obtain ⟨hv, hi⟩ := frozenBindings_members he
  rw [hi]
  exact structured_images hΔ hR body ts ms hm h entry.1 hv

theorem structured_mode_bindings {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) (hR : Residual Δ)
    (body : Ty) (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    {endpoint : Ty} {m : ModExpr} {lower : Bool}
    (hm : ¬Entails Δ (.defined m))
    (h : Refines Δ lower (.ofTy endpoint)
      (.modal ((CompareTy.ofTy body).subst ts ms) m)) :
    ∀ entry ∈ frozenModeBindings body ms, entry.2 ∈ structuredModeCandidates endpoint := by
  intro entry he
  obtain ⟨hv, hi⟩ := frozenModeBindings_members he
  rw [hi]
  exact structured_modes hΔ hR body ts ms hm h entry.1 hv

/-- A single pair of finite binding lists covers the entire frozen context.
Lookup agrees literally with the initial shared witness in both namespaces. -/
theorem structured_assignments {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) (hR : Residual Δ)
    (body : Ty) (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    {endpoint : Ty} {m : ModExpr} {lower : Bool}
    (hm : ¬Entails Δ (.defined m))
    (h : Refines Δ lower (.ofTy endpoint)
      (.modal ((CompareTy.ofTy body).subst ts ms) m)) :
    ∃ types : List (TypeVar × CompareTy), ∃ modes : List (ModVar × ModExpr),
      types.map Prod.fst = body.typeVariables ∧
      modes.map Prod.fst = body.modeVariables ∧
      (∀ v ∈ body.typeVars, types.lookup v = some (ts v)) ∧
      (∀ v ∈ body.modVars, modes.lookup v = some (ms v)) ∧
      (∀ entry ∈ types, entry.2 ∈ structuredImageCandidates endpoint) ∧
      (∀ entry ∈ modes, entry.2 ∈ structuredModeCandidates endpoint) := by
  exact ⟨frozenBindings body ts, frozenModeBindings body ms,
    frozenBindings_keys body ts, frozenModeBindings_keys body ms,
    fun _ hv => frozenBindings_lookup body ts hv,
    fun _ hv => frozenModeBindings_lookup body ms hv,
    structured_bindings hΔ hR body ts ms hm h,
    structured_mode_bindings hΔ hR body ts ms hm h⟩

end ModalityInference.ComparisonPartialStructuredCapsule
