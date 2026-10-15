import ModalityInference.Proofs.ComparisonCapsuleFrozenSelection
import ModalityInference.Proofs.ComparisonCapsuleBodyReplacement

namespace ModalityInference.ComparisonCapsuleContext

open ComparisonBody ComparisonDefinedCovers ComparisonPartialCarrier
open ComparisonPartialStructuredCapsule ComparisonStructuralProjection

/-- The whole source operand is recorded before function children reset their
scalar actions. Records depend only on the two public input types. -/
structure OperandRequest where
  source : Ty
  endpoint : Ty
  action : ModExpr
  isLower : Bool
  deriving Repr, DecidableEq

def operandRequests : Nat → Bool → Ty → Ty → ModExpr → ModExpr → List OperandRequest
  | 0, _, _, _, _, _ => []
  | fuel + 1, lower, source, target, sm, tm =>
      ⟨source, .modal target tm, sm, lower⟩ ::
        match source with
        | .modal a m => operandRequests fuel lower a target (.compose m sm) tm
        | _ => match target with
          | .modal b n => operandRequests fuel lower source b sm (.compose n tm)
          | _ => match source, target with
            | .prod a b, .prod c d | .sum a b, .sum c d =>
                operandRequests fuel lower a c sm tm ++ operandRequests fuel lower b d sm tm
            | .fn a b, .fn c d =>
                operandRequests fuel (!lower) a c .epsilon .epsilon ++
                  operandRequests fuel lower b d .epsilon .epsilon
            | _, _ => []

def OperandRequest.Holds (Δ : Bounds) (types : TypeVar → CompareTy)
    (modes : ModVar → ModExpr) (r : OperandRequest) : Prop :=
  Refines Δ r.isLower (.ofTy r.endpoint)
    (.modal (publicImage types modes r.source) (r.action.subst modes))

private theorem context_source_modal {Δ : Bounds} {types : TypeVar → CompareTy}
    {modes : ModVar → ModExpr} {lower : Bool} {a target : Ty} {m sm tm : ModExpr}
    (h : ContextHolds Δ types modes lower (.modal a m) target sm tm) :
    ContextHolds Δ types modes lower a target (.compose m sm) tm := by
  cases lower
  · exact (AlgebraSubtype.shaped (.composeRev (a := publicImage types modes a)
      h.wellShaped_left)).trans h
  · exact h.trans (.shaped (.compose (a := publicImage types modes a)
      h.wellShaped_right))

private theorem context_target_modal {Δ : Bounds} {types : TypeVar → CompareTy}
    {modes : ModVar → ModExpr} {lower : Bool} {source a : Ty} {m sm tm : ModExpr}
    (h : ContextHolds Δ types modes lower source (.modal a m) sm tm) :
    ContextHolds Δ types modes lower source a sm (.compose m tm) := by
  cases lower
  · exact h.trans (.shaped (.compose (a := .ofTy a) h.wellShaped_right))
  · exact (AlgebraSubtype.shaped (.composeRev (a := .ofTy a) h.wellShaped_left)).trans h

private theorem context_prod {Δ : Bounds} (hΔ : Residual Δ)
    {types : TypeVar → CompareTy} {modes : ModVar → ModExpr}
    {lower : Bool} {a b c d : Ty} {sm tm : ModExpr}
    (h : ContextHolds Δ types modes lower (.prod a b) (.prod c d) sm tm) :
    ContextHolds Δ types modes lower a c sm tm ∧
      ContextHolds Δ types modes lower b d sm tm := by
  cases lower <;> exact product_inversion hΔ h

private theorem context_sum {Δ : Bounds} (hΔ : Residual Δ)
    {types : TypeVar → CompareTy} {modes : ModVar → ModExpr}
    {lower : Bool} {a b c d : Ty} {sm tm : ModExpr}
    (h : ContextHolds Δ types modes lower (.sum a b) (.sum c d) sm tm) :
    ContextHolds Δ types modes lower a c sm tm ∧
      ContextHolds Δ types modes lower b d sm tm := by
  cases lower <;> exact sum_inversion hΔ h

private theorem context_fn {Δ : Bounds} (hΔ : Residual Δ)
    {types : TypeVar → CompareTy} {modes : ModVar → ModExpr}
    {lower : Bool} {a b c d : Ty} {sm tm : ModExpr}
    (h : ContextHolds Δ types modes lower (.fn a b) (.fn c d) sm tm) :
    ContextHolds Δ types modes (!lower) a c .epsilon .epsilon ∧
      ContextHolds Δ types modes lower b d .epsilon .epsilon := by
  cases lower
  · have hs := function_inversion hΔ h
    exact ⟨.congr hs.1 (.refl (by intro η _; rfl)), .congr hs.2 (.refl (by intro η _; rfl))⟩
  · have hs := function_inversion hΔ h
    exact ⟨.congr hs.1 (.refl (by intro η _; rfl)), .congr hs.2 (.refl (by intro η _; rfl))⟩

/-- Every whole-operand record is a consequence of the original comparison,
including the function operand before its child contexts are separated. -/
theorem operandRequests_holds {Δ : Bounds} (hΔ : Residual Δ)
    (types : TypeVar → CompareTy) (modes : ModVar → ModExpr)
    (fuel : Nat) (lower : Bool) (source target : Ty) (sm tm : ModExpr)
    (h : ContextHolds Δ types modes lower source target sm tm) :
    ∀ r ∈ operandRequests fuel lower source target sm tm, r.Holds Δ types modes := by
  induction fuel generalizing lower source target sm tm with
  | zero => simp [operandRequests]
  | succ fuel ih =>
    intro r hr
    rcases List.mem_cons.mp hr with hr | hr
    · subst r; exact h
    · cases source with
      | modal a m => exact ih _ _ _ _ _ (context_source_modal h) r hr
      | var v | unit | credit =>
        cases target
        all_goals try simp at hr
        exact ih _ _ _ _ _ (context_target_modal h) r hr
      | prod a b | sum a b | fn a b =>
        cases target
        all_goals try simp at hr
        all_goals first
          | exact ih _ _ _ _ _ (context_target_modal h) r hr
          | (rcases hr with hr | hr
             all_goals first
               | exact ih _ _ _ _ _ (context_prod hΔ h).1 r hr
               | exact ih _ _ _ _ _ (context_prod hΔ h).2 r hr
               | exact ih _ _ _ _ _ (context_sum hΔ h).1 r hr
               | exact ih _ _ _ _ _ (context_sum hΔ h).2 r hr
               | exact ih _ _ _ _ _ (context_fn hΔ h).1 r hr
               | exact ih _ _ _ _ _ (context_fn hΔ h).2 r hr)


noncomputable section
attribute [local instance] Classical.propDecidable

/-- Outermost source operands frozen by the actual shared modality witness.
Function children do not erase an already encountered partial ancestor. -/
def semanticFrozenOperands (Δ : Bounds) (modes : ModVar → ModExpr) : Ty → List Ty
  | .var _ | .unit | .credit => []
  | .prod a b | .sum a b | .fn a b =>
      semanticFrozenOperands Δ modes a ++ semanticFrozenOperands Δ modes b
  | .modal a m =>
      if Entails Δ (.defined (m.subst modes)) then semanticFrozenOperands Δ modes a else [a]

def TypeSupportWithin (a b : Ty) : Prop :=
  a.typeVars ⊆ b.typeVars ∧ a.modVars ⊆ b.modVars

theorem semanticFrozenOperands_scope (Δ : Bounds) (modes : ModVar → ModExpr) (body : Ty)
    {a : Ty} (ha : a ∈ semanticFrozenOperands Δ modes body) : TypeSupportWithin a body := by
  induction body with
  | var | unit | credit => simp [semanticFrozenOperands] at ha
  | prod b c ib ic | sum b c ib ic | fn b c ib ic =>
    rcases List.mem_append.mp ha with ha | ha
    · exact ⟨(ib ha).1.trans (Finset.subset_union_left),
        (ib ha).2.trans (Finset.subset_union_left)⟩
    · exact ⟨(ic ha).1.trans (Finset.subset_union_right),
        (ic ha).2.trans (Finset.subset_union_right)⟩
  | modal b m ib =>
    simp only [semanticFrozenOperands] at ha
    split at ha
    · exact ⟨(ib ha).1, (ib ha).2.trans Finset.subset_union_left⟩
    · cases List.mem_singleton.mp ha
      exact ⟨Finset.Subset.refl _, Finset.subset_union_left⟩

private theorem context_rootTag {Δ : Bounds} (hR : Residual Δ)
    {types : TypeVar → CompareTy} {modes : ModVar → ModExpr}
    {lower : Bool} {source target : Ty} {sm tm : ModExpr}
    (h : ContextHolds Δ types modes lower source target sm tm) :
    rootTag (publicImage types modes source).shape = rootTag (CompareTy.ofTy target).shape := by
  cases lower
  · exact rootTag_equivalent hR h.shape_equivalent
  · exact (rootTag_equivalent hR h.shape_equivalent).symm

/-- Every semantic frozen operand is contained in a recorded whole context
with a genuinely partial instantiated action. The root record is considered
before a function resets its children's scalar actions. -/
theorem operandRequests_frozen_cover {Δ : Bounds} (hR : Residual Δ)
    (types : TypeVar → CompareTy) (modes : ModVar → ModExpr)
    (fuel : Nat) (lower : Bool) (source target : Ty) (sm tm : ModExpr)
    (hsize : traversalSize source + traversalSize target < fuel)
    (h : ContextHolds Δ types modes lower source target sm tm)
    {a : Ty} (ha : a ∈ semanticFrozenOperands Δ modes source ∨
      (a = source ∧ ¬Entails Δ (.defined (sm.subst modes)))) :
    ∃ r ∈ operandRequests fuel lower source target sm tm,
      ¬Entails Δ (.defined (r.action.subst modes)) ∧ TypeSupportWithin a r.source := by
  induction fuel generalizing lower source target sm tm with
  | zero => omega
  | succ fuel ih =>
    by_cases hsm : Entails Δ (.defined (sm.subst modes))
    · have haf : a ∈ semanticFrozenOperands Δ modes source := ha.elim id (fun hn => (hn.2 hsm).elim)
      have htag := context_rootTag hR h
      cases source with
      | var | unit | credit => simp [semanticFrozenOperands] at haf
      | modal b m =>
        simp only [semanticFrozenOperands] at haf
        have hsz : traversalSize b + traversalSize target < fuel := by
          simp only [traversalSize] at hsize
          omega
        have hinput : a ∈ semanticFrozenOperands Δ modes b ∨
            (a = b ∧ ¬Entails Δ (.defined ((m.compose sm).subst modes))) := by
          split at haf
          · exact Or.inl haf
          · next hm =>
            refine Or.inr ⟨List.mem_singleton.mp haf, ?_⟩
            intro hc
            exact hm (Entails.defined_compose_iff.mp hc).1
        obtain ⟨r, hr, hp, hw⟩ := ih lower b target (.compose m sm) tm hsz
          (context_source_modal h) hinput
        exact ⟨r, List.mem_cons_of_mem _ hr, hp, hw⟩
      | prod b c =>
        cases target with
        | modal d n =>
          have hsz : traversalSize (.prod b c) + traversalSize d < fuel := by
            simp only [traversalSize] at hsize ⊢
            omega
          obtain ⟨r, hr, hp, hw⟩ := ih lower (.prod b c) d sm (.compose n tm) hsz
            (context_target_modal h) (Or.inl haf)
          exact ⟨r, List.mem_cons_of_mem _ hr, hp, hw⟩
        | prod d e =>
          have hleft : traversalSize b + traversalSize d < fuel := by
            simp only [traversalSize] at hsize
            omega
          have hright : traversalSize c + traversalSize e < fuel := by
            simp only [traversalSize] at hsize
            omega
          rcases List.mem_append.mp haf with haf | haf
          · obtain ⟨r, hr, hp, hw⟩ := ih lower b d sm tm hleft (context_prod hR h).1 (Or.inl haf)
            exact ⟨r, List.mem_cons_of_mem _ (List.mem_append_left _ hr), hp, hw⟩
          · obtain ⟨r, hr, hp, hw⟩ := ih lower c e sm tm hright (context_prod hR h).2 (Or.inl haf)
            exact ⟨r, List.mem_cons_of_mem _ (List.mem_append_right _ hr), hp, hw⟩
        | var | unit | credit | sum _ _ | fn _ _ =>
          simp [publicImage, CompareTy.ofTy, CompareTy.subst, CompareTy.shape, rootTag] at htag
      | sum b c =>
        cases target with
        | modal d n =>
          have hsz : traversalSize (.sum b c) + traversalSize d < fuel := by
            simp only [traversalSize] at hsize ⊢
            omega
          obtain ⟨r, hr, hp, hw⟩ := ih lower (.sum b c) d sm (.compose n tm) hsz
            (context_target_modal h) (Or.inl haf)
          exact ⟨r, List.mem_cons_of_mem _ hr, hp, hw⟩
        | sum d e =>
          have hleft : traversalSize b + traversalSize d < fuel := by
            simp only [traversalSize] at hsize
            omega
          have hright : traversalSize c + traversalSize e < fuel := by
            simp only [traversalSize] at hsize
            omega
          rcases List.mem_append.mp haf with haf | haf
          · obtain ⟨r, hr, hp, hw⟩ := ih lower b d sm tm hleft (context_sum hR h).1 (Or.inl haf)
            exact ⟨r, List.mem_cons_of_mem _ (List.mem_append_left _ hr), hp, hw⟩
          · obtain ⟨r, hr, hp, hw⟩ := ih lower c e sm tm hright (context_sum hR h).2 (Or.inl haf)
            exact ⟨r, List.mem_cons_of_mem _ (List.mem_append_right _ hr), hp, hw⟩
        | var | unit | credit | prod _ _ | fn _ _ =>
          simp [publicImage, CompareTy.ofTy, CompareTy.subst, CompareTy.shape, rootTag] at htag
      | fn b c =>
        cases target with
        | modal d n =>
          have hsz : traversalSize (.fn b c) + traversalSize d < fuel := by
            simp only [traversalSize] at hsize ⊢
            omega
          obtain ⟨r, hr, hp, hw⟩ := ih lower (.fn b c) d sm (.compose n tm) hsz
            (context_target_modal h) (Or.inl haf)
          exact ⟨r, List.mem_cons_of_mem _ hr, hp, hw⟩
        | fn d e =>
          have hleft : traversalSize b + traversalSize d < fuel := by
            simp only [traversalSize] at hsize
            omega
          have hright : traversalSize c + traversalSize e < fuel := by
            simp only [traversalSize] at hsize
            omega
          rcases List.mem_append.mp haf with haf | haf
          · obtain ⟨r, hr, hp, hw⟩ := ih (!lower) b d .epsilon .epsilon hleft (context_fn hR h).1 (Or.inl haf)
            exact ⟨r, List.mem_cons_of_mem _ (List.mem_append_left _ hr), hp, hw⟩
          · obtain ⟨r, hr, hp, hw⟩ := ih lower c e .epsilon .epsilon hright (context_fn hR h).2 (Or.inl haf)
            exact ⟨r, List.mem_cons_of_mem _ (List.mem_append_right _ hr), hp, hw⟩
        | var | unit | credit | prod _ _ | sum _ _ =>
          simp [publicImage, CompareTy.ofTy, CompareTy.subst, CompareTy.shape, rootTag] at htag
    · refine ⟨⟨source, .modal target tm, sm, lower⟩, List.mem_cons_self, hsm, ?_⟩
      rcases ha with ha | ⟨rfl, _⟩
      · exact semanticFrozenOperands_scope Δ modes source ha
      · exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩

/-- Every frozen type name is accounted for by an outermost frozen operand. -/
theorem semanticFrozenOperands_type_support (Δ : Bounds) (modes : ModVar → ModExpr)
    (body : Ty) (v : TypeVar) :
    v ∈ frozenTypeSupport (fun m => decide (Entails Δ (.defined (m.subst modes)))) body ↔
      ∃ a ∈ semanticFrozenOperands Δ modes body, v ∈ a.typeVars := by
  induction body with
  | var | unit | credit => simp [frozenTypeSupport, semanticFrozenOperands]
  | prod a b ia ib | sum a b ia ib | fn a b ia ib =>
    simpa only [frozenTypeSupport, Finset.mem_union, semanticFrozenOperands,
      List.mem_append, exists_prop, or_and_right, exists_or] using or_congr ia ib
  | modal a m ia =>
    by_cases hm : Entails Δ (.defined (m.subst modes))
    · simpa only [frozenTypeSupport, hm, decide_true, if_true, semanticFrozenOperands] using ia
    · simp [frozenTypeSupport, semanticFrozenOperands, hm]

def bodyOperandRequests (source target : Ty) : List OperandRequest :=
  operandRequests (traversalSize source + traversalSize target + 1)
    false source target .epsilon .epsilon

def bodyFrozenTypeCandidates (source target : Ty) : List CompareTy :=
  (bodyOperandRequests source target).flatMap fun r => structuredImageCandidates r.endpoint

def bodyFrozenModeCandidates (source target : Ty) : List ModExpr :=
  (bodyOperandRequests source target).flatMap fun r => structuredModeCandidates r.endpoint

theorem bodyOperandRequests_holds {Δ : Bounds} (hR : Residual Δ)
    (types : TypeVar → CompareTy) (modes : ModVar → ModExpr) {source target : Ty}
    (h : AlgebraSubtype Δ (publicImage types modes source) (.ofTy target)) :
    ∀ r ∈ bodyOperandRequests source target, r.Holds Δ types modes :=
  operandRequests_holds hR types modes _ false source target .epsilon .epsilon
    (.congr h (.refl (by intro η _; rfl)))

/-- All keys enclosed by a semantic frozen ancestor are pinned to input-only
literal candidates, including keys inside a function whose scalar child actions
restart at the identity. Both conclusions use the original shared witness. -/
theorem body_frozen_images {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) (hR : Residual Δ)
    (types : TypeVar → CompareTy) (modes : ModVar → ModExpr) {source target : Ty}
    (h : AlgebraSubtype Δ (publicImage types modes source) (.ofTy target))
    {a : Ty} (ha : a ∈ semanticFrozenOperands Δ modes source) :
    (∀ v ∈ a.typeVars, types v ∈ bodyFrozenTypeCandidates source target) ∧
      (∀ v ∈ a.modVars, modes v ∈ bodyFrozenModeCandidates source target) := by
  obtain ⟨r, hr, hp, hs⟩ := operandRequests_frozen_cover hR types modes
    (traversalSize source + traversalSize target + 1) false source target .epsilon .epsilon
    (by omega) (.congr h (.refl (by intro η _; rfl))) (Or.inl ha)
  have hh := bodyOperandRequests_holds hR types modes h r hr
  constructor
  · intro v hv
    exact List.mem_flatMap.mpr ⟨r, hr, structured_images hΔ hR r.source types modes hp hh v (hs.1 hv)⟩
  · intro v hv
    exact List.mem_flatMap.mpr ⟨r, hr, structured_modes hΔ hR r.source types modes hp hh v (hs.2 hv)⟩

theorem body_semantic_frozen_type_images {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) (hR : Residual Δ)
    (types : TypeVar → CompareTy) (modes : ModVar → ModExpr) {source target : Ty}
    (h : AlgebraSubtype Δ (publicImage types modes source) (.ofTy target)) :
    ∀ v ∈ frozenTypeSupport (fun m => decide (Entails Δ (.defined (m.subst modes)))) source,
      types v ∈ bodyFrozenTypeCandidates source target := by
  intro v hv
  obtain ⟨a, ha, hv⟩ := (semanticFrozenOperands_type_support Δ modes source v).mp hv
  exact (body_frozen_images hΔ hR types modes h ha).1 v hv

/-- Retaining exactly the semantic frozen support suffices for shared body
reconstruction. No totality restriction is placed on the original mode images. -/
theorem body_replacement_semantic {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (types replacement : TypeVar → CompareTy) (modes : ModVar → ModExpr)
    {source target : Ty}
    (h : AlgebraSubtype Δ (publicImage types modes source) (.ofTy target))
    (hp : ∀ v ∈ source.typeVars, PreservesBounds Δ (types v) (replacement v))
    (hf : ∀ v ∈ frozenTypeSupport (fun m => decide (Entails Δ (.defined (m.subst modes)))) source,
      replacement v = types v) :
    AlgebraSubtype Δ (publicImage replacement modes source) (.ofTy target) :=
  body_replacement hΔ (fun m => decide (Entails Δ (.defined (m.subst modes))))
    (fun _ hm => of_decide_eq_true hm) (Carrier.of_public target) h hp hf

def semanticFrozenTypeNames (Δ : Bounds) (modes : ModVar → ModExpr) (source : Ty) : List TypeVar :=
  (semanticFrozenOperands Δ modes source).flatMap TypeExpr.typeVariables

def semanticFrozenModeNames (Δ : Bounds) (modes : ModVar → ModExpr) (source : Ty) : List ModVar :=
  (semanticFrozenOperands Δ modes source).flatMap TypeExpr.modeVariables

/-- One pair of finite binding lists retains all semantic frozen images
literally. Repeated occurrences use the same original type and mode actions. -/
theorem body_frozen_assignments {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) (hR : Residual Δ)
    (types : TypeVar → CompareTy) (modes : ModVar → ModExpr) {source target : Ty}
    (h : AlgebraSubtype Δ (publicImage types modes source) (.ofTy target)) :
    ∃ fixedTypes : List (TypeVar × CompareTy), ∃ fixedModes : List (ModVar × ModExpr),
      fixedTypes.map Prod.fst = semanticFrozenTypeNames Δ modes source ∧
      fixedModes.map Prod.fst = semanticFrozenModeNames Δ modes source ∧
      (∀ v ∈ frozenTypeSupport (fun m => decide (Entails Δ (.defined (m.subst modes)))) source,
        fixedTypes.lookup v = some (types v)) ∧
      (∀ a ∈ semanticFrozenOperands Δ modes source, ∀ v ∈ a.modVars,
        fixedModes.lookup v = some (modes v)) ∧
      (∀ entry ∈ fixedTypes, entry.2 ∈ bodyFrozenTypeCandidates source target) ∧
      (∀ entry ∈ fixedModes, entry.2 ∈ bodyFrozenModeCandidates source target) := by
  refine ⟨(semanticFrozenTypeNames Δ modes source).map (fun v => (v, types v)),
    (semanticFrozenModeNames Δ modes source).map (fun v => (v, modes v)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [List.map_map, Function.comp_def]
  · simp [List.map_map, Function.comp_def]
  · intro v hv
    obtain ⟨a, ha, hv⟩ := (semanticFrozenOperands_type_support Δ modes source v).mp hv
    exact List.lookup_graph _ (List.mem_flatMap.mpr ⟨a, ha, (TypeExpr.mem_typeVariables _ _).mpr hv⟩)
  · intro a ha v hv
    exact List.lookup_graph _ (List.mem_flatMap.mpr ⟨a, ha, (TypeExpr.mem_modeVariables _ _).mpr hv⟩)
  · intro entry he
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp he
    obtain ⟨a, ha, hv⟩ := List.mem_flatMap.mp hv
    exact (body_frozen_images hΔ hR types modes h ha).1 v ((TypeExpr.mem_typeVariables _ _).mp hv)
  · intro entry he
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp he
    obtain ⟨a, ha, hv⟩ := List.mem_flatMap.mp hv
    exact (body_frozen_images hΔ hR types modes h ha).2 v ((TypeExpr.mem_modeVariables _ _).mp hv)

end

end ModalityInference.ComparisonCapsuleContext
