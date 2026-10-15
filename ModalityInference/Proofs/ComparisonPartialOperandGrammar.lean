import ModalityInference.Proofs.ComparisonPartialCancellation
import ModalityInference.Proofs.ComparisonPartialFrozenFragments

namespace ModalityInference.ComparisonPartialStructuredCapsule

open ComparisonStructuralProjection

/-- The outer modal spine, in outermost-first order. -/
def rootModes : CompareTy → List ModExpr
  | .modal a m => m :: rootModes a
  | _ => []

def wrapModes : List ModExpr → CompareTy → CompareTy
  | [], a => a
  | m :: modes, a => .modal (wrapModes modes a) m

/-- Public root context with the constructor's children erased. -/
def rootPublic : Ty → Ty
  | .modal a m => .modal (rootPublic a) m
  | _ => .unit

 theorem rootType_public (kind : Nat) (hk : kind ≠ 5) (a : Ty) :
    rootType kind (.ofTy a) = .ofTy (rootPublic a) := by
  induction a <;> simp_all [CompareTy.ofTy, rootType, rootPublic, rootBase]

 theorem rootPublic_nonpair (a : Ty) :
    rootTag (CompareTy.ofTy (rootPublic a)).shape = 1 := by
  induction a <;> first | rfl | assumption

 theorem rootPublic_modes (a : Ty) :
    rootModes (.ofTy (rootPublic a)) = rootModes (.ofTy a) := by
  induction a <;> simp_all only [CompareTy.ofTy, rootPublic, rootModes]

 theorem nonpair_fragment_below {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a b : Ty} {m : ModExpr}
    (hp : rootTag (CompareTy.ofTy a).shape ≠ 3) (hs : rootTag (CompareTy.ofTy a).shape ≠ 4)
    (hm : ¬Entails Δ (.defined m))
    (h : AlgebraSubtype Δ (.modal (.ofTy a) m) (.ofTy b)) :
    CompareTy.ofTy a ∈ frozenFragments (.ofTy b) none := by
  obtain ⟨token, ht, hprefix⟩ := partial_token_prefix hm (.ofTy a)
  have hl : ([], token) ∈ (observe Δ (.modal (.ofTy a) m) none).positive := by
    change ([], token) ∈ (observe Δ (.ofTy a) (some m)).positive
    rw [observe_public_nonpair a (some m) hm hp hs]
    exact ⟨token, ht, rfl⟩
  have hc := (observe_supported Δ (.ofTy b) none).1 ([], token) ((algebra_sound hΔ h).1 hl)
  exact List.mem_flatMap.mpr ⟨([], token), hc, hprefix.mem_modalBases⟩

 theorem nonpair_fragment_above {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a b : Ty} {m : ModExpr}
    (hp : rootTag (CompareTy.ofTy b).shape ≠ 3) (hs : rootTag (CompareTy.ofTy b).shape ≠ 4)
    (hm : ¬Entails Δ (.defined m))
    (h : AlgebraSubtype Δ (.ofTy a) (.modal (.ofTy b) m)) :
    CompareTy.ofTy b ∈ frozenFragments (.ofTy a) none := by
  obtain ⟨token, ht, hprefix⟩ := partial_token_prefix hm (.ofTy b)
  have hr : ([], token) ∈ (observe Δ (.modal (.ofTy b) m) none).negative := by
    change ([], token) ∈ (observe Δ (.ofTy b) (some m)).negative
    rw [observe_public_nonpair b (some m) hm hp hs]
    exact ⟨token, ht, rfl⟩
  have hc := (observe_supported Δ (.ofTy a) none).2 ([], token) ((algebra_sound hΔ h).2 hr)
  exact List.mem_flatMap.mpr ⟨([], token), hc, hprefix.mem_modalBases⟩

/-- Finite exact root spines supplied by the endpoint's frozen root context. -/
def rootSpines (endpoint : Ty) : List (List ModExpr) :=
  (frozenFragments (.ofTy (rootPublic endpoint)) none).map rootModes

 theorem rootSpines_below {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) (hR : Residual Δ)
    {a b : Ty} {m : ModExpr} {kind : Nat} (hk : kind ≠ 0) (hf : kind ≠ 5)
    (ha : rootTag (CompareTy.ofTy a).shape = kind) (hm : ¬Entails Δ (.defined m))
    (h : AlgebraSubtype Δ (.modal (.ofTy a) m) (.ofTy b)) :
    rootModes (.ofTy a) ∈ rootSpines b := by
  have hr := algebra_rootType hR h hk ha
  change AlgebraSubtype Δ (.modal (rootType kind (.ofTy a)) m) (rootType kind (.ofTy b)) at hr
  rw [rootType_public kind hf a, rootType_public kind hf b] at hr
  have hfrozen := nonpair_fragment_below hΔ
    (by rw [rootPublic_nonpair]; decide) (by rw [rootPublic_nonpair]; decide) hm hr
  exact List.mem_map.mpr ⟨_, hfrozen, rootPublic_modes a⟩

 theorem rootSpines_above {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) (hR : Residual Δ)
    {a b : Ty} {m : ModExpr} {kind : Nat} (hk : kind ≠ 0) (hf : kind ≠ 5)
    (hb : rootTag (CompareTy.ofTy b).shape = kind) (hm : ¬Entails Δ (.defined m))
    (h : AlgebraSubtype Δ (.ofTy a) (.modal (.ofTy b) m)) :
    rootModes (.ofTy b) ∈ rootSpines a := by
  have ha := (rootTag_equivalent hR h.shape_equivalent).trans hb
  have hr := algebra_rootType hR h hk ha
  change AlgebraSubtype Δ (rootType kind (.ofTy a)) (.modal (rootType kind (.ofTy b)) m) at hr
  rw [rootType_public kind hf a, rootType_public kind hf b] at hr
  have hfrozen := nonpair_fragment_above hΔ
    (by rw [rootPublic_nonpair]; decide) (by rw [rootPublic_nonpair]; decide) hm hr
  exact List.mem_map.mpr ⟨_, hfrozen, rootPublic_modes b⟩

def publicCore : Ty → Ty
  | .modal a _ => publicCore a
  | a => a

 theorem coreModes_eq (a : Ty) :
    wrapModes (rootModes (.ofTy a)) (.ofTy (publicCore a)) = .ofTy a := by
  induction a <;> simp_all only [CompareTy.ofTy, rootModes, wrapModes, publicCore]

 theorem publicCore_tag (a : Ty) :
    rootTag (CompareTy.ofTy (publicCore a)).shape = rootTag (CompareTy.ofTy a).shape := by
  induction a <;> first | rfl | assumption

 theorem publicCore_not_modal (a b : Ty) (m : ModExpr) : publicCore a ≠ .modal b m := by
  induction a <;> simp_all [publicCore]

def publicPairChild (right : Bool) : Ty → Ty
  | .prod a b | .sum a b => if right then b else a
  | .modal a m => .modal (publicPairChild right a) m
  | _ => .unit

 theorem pairChild_ofTy (right : Bool) (a : Ty) :
    pairChild right (.ofTy a) = .ofTy (publicPairChild right a) := by
  induction a <;> cases right <;> simp_all only [CompareTy.ofTy, pairChild, publicPairChild,
    Bool.false_eq_true, if_false, if_true]

 theorem pairChild_wrapModes (right : Bool) (modes : List ModExpr) (a : CompareTy) :
    pairChild right (wrapModes modes a) = wrapModes modes (pairChild right a) := by
  induction modes <;> simp_all only [wrapModes, pairChild]

 theorem wrapModes_shaped {Δ : Bounds} (modes : List ModExpr) {a : CompareTy}
    (ha : a.WellShaped Δ) : (wrapModes modes a).WellShaped Δ := by
  induction modes <;> first | exact ha | assumption

/-- Compose the original root spine with the inherited action in its original
order; no reassociation inside a partial operand is used. -/
def actModes : List ModExpr → ModExpr → ModExpr
  | [], m => m
  | n :: modes, m => actModes modes (.compose n m)

 theorem actModes_partial {Δ : Bounds} (modes : List ModExpr) {m : ModExpr}
    (hm : ¬Entails Δ (.defined m)) : ¬Entails Δ (.defined (actModes modes m)) := by
  induction modes generalizing m with
  | nil => exact hm
  | cons n modes ih => exact ih (fun h => hm (Entails.defined_compose_iff.mp h).2)

 theorem wrapModes_modal {Δ : Bounds} (modes : List ModExpr) {a : CompareTy}
    (ha : a.WellShaped Δ) (m : ModExpr) :
    AlgebraSubtype Δ (.modal (wrapModes modes a) m) (.modal a (actModes modes m)) ∧
      AlgebraSubtype Δ (.modal a (actModes modes m)) (.modal (wrapModes modes a) m) := by
  induction modes generalizing m with
  | nil => exact ⟨.refl ha, .refl ha⟩
  | cons n modes ih =>
    have hh := ih (.compose n m)
    exact ⟨(AlgebraSubtype.shaped (.compose (wrapModes_shaped modes ha))).trans hh.1,
      hh.2.trans (.shaped (.composeRev (wrapModes_shaped modes ha)))⟩

/-- Only product/sum branching contributes recursive grammar depth. Frozen
functions are literal fragments, and modal spines are separately finite. -/
def pairDepth : Ty → Nat
  | .prod a b | .sum a b => max (pairDepth a) (pairDepth b) + 1
  | .modal a _ => pairDepth a
  | _ => 0

def shapePairDepth : ComparisonShape → Nat
  | .prod a b | .sum a b => max (shapePairDepth a) (shapePairDepth b) + 1
  | _ => 0

 theorem pairDepth_shape (a : Ty) :
    shapePairDepth ((CompareTy.ofTy a).shape.subst unitShapes) = pairDepth a := by
  induction a <;> simp_all only [CompareTy.ofTy, CompareTy.shape, ComparisonShape.subst,
    unitShapes, shapePairDepth, pairDepth]

 theorem pairDepth_equivalent {Δ : Bounds} (hR : Residual Δ) {a b : Ty}
    (h : ComparisonShape.Equivalent Δ (CompareTy.ofTy a).shape (CompareTy.ofTy b).shape) :
    pairDepth a = pairDepth b := by
  have hh := congrArg shapePairDepth (h unitShapes (residual_unitShapes hR))
  simpa only [pairDepth_shape] using hh

 theorem pairDepth_core (a : Ty) : pairDepth (publicCore a) = pairDepth a := by
  induction a <;> first | rfl | assumption

open ComparisonDefinedCovers (Refines)

 theorem refines_rootTag {Δ : Bounds} (hR : Residual Δ) {lower : Bool}
    {source target : Ty} {m : ModExpr}
    (h : Refines Δ lower (.ofTy target) (.modal (.ofTy source) m)) :
    rootTag (CompareTy.ofTy source).shape = rootTag (CompareTy.ofTy target).shape := by
  cases lower
  · exact rootTag_equivalent hR h.shape_equivalent
  · exact (rootTag_equivalent hR h.shape_equivalent).symm

 theorem refines_pairDepth {Δ : Bounds} (hR : Residual Δ) {lower : Bool}
    {source target : Ty} {m : ModExpr}
    (h : Refines Δ lower (.ofTy target) (.modal (.ofTy source) m)) :
    pairDepth source = pairDepth target := by
  cases lower
  · exact pairDepth_equivalent hR h.shape_equivalent
  · exact (pairDepth_equivalent hR h.shape_equivalent).symm

 theorem rootSpines_refines {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) (hR : Residual Δ)
    {lower : Bool} {source target : Ty} {m : ModExpr} {kind : Nat}
    (hk : kind ≠ 0) (hf : kind ≠ 5) (ha : rootTag (CompareTy.ofTy source).shape = kind)
    (hm : ¬Entails Δ (.defined m))
    (h : Refines Δ lower (.ofTy target) (.modal (.ofTy source) m)) :
    rootModes (.ofTy source) ∈ rootSpines target := by
  cases lower
  · exact rootSpines_below hΔ hR hk hf ha hm h
  · exact rootSpines_above hΔ hR hk hf ha hm h

 theorem nonpair_fragment_refines {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {lower : Bool} {source target : Ty} {m : ModExpr}
    (hp : rootTag (CompareTy.ofTy source).shape ≠ 3) (hs : rootTag (CompareTy.ofTy source).shape ≠ 4)
    (hm : ¬Entails Δ (.defined m))
    (h : Refines Δ lower (.ofTy target) (.modal (.ofTy source) m)) :
    CompareTy.ofTy source ∈ frozenFragments (.ofTy target) none := by
  cases lower
  · exact nonpair_fragment_below hΔ hp hs hm h
  · exact nonpair_fragment_above hΔ hp hs hm h

 theorem pairChild_refines {Δ : Bounds} (hR : Residual Δ) {lower isSum : Bool}
    {source target : Ty} {m : ModExpr} (ha : PairRoot isSum (.ofTy source))
    (h : Refines Δ lower (.ofTy target) (.modal (.ofTy source) m)) (right : Bool) :
    Refines Δ lower (.ofTy (publicPairChild right target))
      (.modal (pairChild right (.ofTy source)) m) := by
  cases lower
  · simpa only [pairChild, pairChild_ofTy] using algebra_pairChild hR h (.modal ha) right
  · have hb := ha.transport hR h.wellShaped_left h.shape_equivalent.symm
    simpa only [pairChild, pairChild_ofTy] using algebra_pairChild hR h hb right

 theorem refines_unwrapModes {Δ : Bounds} {lower : Bool} {endpoint : CompareTy}
    (modes : List ModExpr) {a : CompareTy} (ha : a.WellShaped Δ) (m : ModExpr)
    (h : Refines Δ lower endpoint (.modal (wrapModes modes a) m)) :
    Refines Δ lower endpoint (.modal a (actModes modes m)) := by
  have hh := wrapModes_modal modes ha m
  cases lower
  · exact hh.2.trans h
  · exact h.trans hh.1

def pairWords (isSum : Bool) (spines : List (List ModExpr))
    (left right : List CompareTy) : List CompareTy :=
  spines.flatMap fun modes => left.flatMap fun a => right.map fun b =>
    wrapModes modes (if isSum then .sum a b else .prod a b)

 theorem mem_pairWords {isSum : Bool} {spines : List (List ModExpr)}
    {left right : List CompareTy} {modes : List ModExpr} {a b : CompareTy}
    (hm : modes ∈ spines) (ha : a ∈ left) (hb : b ∈ right) :
    wrapModes modes (if isSum then .sum a b else .prod a b) ∈ pairWords isSum spines left right :=
  List.mem_flatMap.mpr ⟨modes, hm, List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨b, hb, rfl⟩⟩⟩

/-- A finite input-relative grammar. Its depth counts only endpoint
product/sum layers; every modal spine and frozen leaf comes literally from
an input fragment. Membership alone makes no subtyping assertion. -/
def operandGrammar : Nat → Ty → List CompareTy
  | 0, endpoint => frozenFragments (.ofTy endpoint) none
  | fuel + 1, endpoint => frozenFragments (.ofTy endpoint) none ++
      if rootTag (CompareTy.ofTy endpoint).shape = 3 then
        pairWords false (rootSpines endpoint)
          (operandGrammar fuel (publicPairChild false endpoint))
          (operandGrammar fuel (publicPairChild true endpoint))
      else if rootTag (CompareTy.ofTy endpoint).shape = 4 then
        pairWords true (rootSpines endpoint)
          (operandGrammar fuel (publicPairChild false endpoint))
          (operandGrammar fuel (publicPairChild true endpoint))
      else []

 theorem operandGrammar_frozen {a : CompareTy} {endpoint : Ty}
    (h : a ∈ frozenFragments (.ofTy endpoint) none) (fuel : Nat) :
    a ∈ operandGrammar fuel endpoint := by
  cases fuel
  · exact h
  · exact List.mem_append_left _ h

 theorem operandGrammar_pair {fuel : Nat} {endpoint : Ty} {isSum : Bool}
    (htag : rootTag (CompareTy.ofTy endpoint).shape = if isSum then 4 else 3)
    {modes : List ModExpr} {a b : CompareTy} (hm : modes ∈ rootSpines endpoint)
    (ha : a ∈ operandGrammar fuel (publicPairChild false endpoint))
    (hb : b ∈ operandGrammar fuel (publicPairChild true endpoint)) :
    wrapModes modes (if isSum then .sum a b else .prod a b) ∈ operandGrammar (fuel + 1) endpoint := by
  cases isSum <;> simp only [Bool.false_eq_true, if_false, if_true] at htag ⊢
  all_goals apply List.mem_append_right
  all_goals simp only [htag, ↓reduceIte]
  · exact mem_pairWords (isSum := false) hm ha hb
  · exact mem_pairWords (isSum := true) hm ha hb

 theorem pairRoot_of_tag {Δ : Bounds} (hR : Residual Δ) {a : CompareTy}
    (ha : a.WellShaped Δ) (isSum : Bool)
    (htag : rootTag a.shape = if isSum then 4 else 3) : PairRoot isSum a := by
  apply PairRoot.of_head hR ha isSum
  cases he : a.shape <;> cases isSum <;> simp_all [rootTag, pairHead]

 theorem pairChild_core {source left right : Ty} {isSum : Bool}
    (hc : publicCore source = if isSum then .sum left right else .prod left right) (side : Bool) :
    pairChild side (.ofTy source) = wrapModes (rootModes (.ofTy source))
      (.ofTy (if side then right else left)) := by
  calc
    pairChild side (.ofTy source) =
        pairChild side (wrapModes (rootModes (.ofTy source)) (.ofTy (publicCore source))) :=
      congrArg (pairChild side) (coreModes_eq source).symm
    _ = wrapModes (rootModes (.ofTy source)) (pairChild side (.ofTy (publicCore source))) :=
      pairChild_wrapModes side _ _
    _ = _ := by rw [hc]; cases isSum <;> cases side <;> rfl

 theorem pairCore_tag {source left right : Ty} {isSum : Bool}
    (hc : publicCore source = if isSum then .sum left right else .prod left right) :
    rootTag (CompareTy.ofTy source).shape = if isSum then 4 else 3 := by
  rw [← publicCore_tag source, hc]
  cases isSum <;> rfl

 theorem pairCore_depth {source left right : Ty} {isSum : Bool}
    (hc : publicCore source = if isSum then .sum left right else .prod left right) :
    pairDepth source = max (pairDepth left) (pairDepth right) + 1 := by
  rw [← pairDepth_core source, hc]
  cases isSum <;> rfl

 theorem operandGrammar_pair_complete {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) (hR : Residual Δ)
    {fuel : Nat}
    (ih : ∀ {source target : Ty} {m : ModExpr} {lower : Bool}, pairDepth source ≤ fuel →
      ¬Entails Δ (.defined m) → Refines Δ lower (.ofTy target) (.modal (.ofTy source) m) →
      CompareTy.ofTy source ∈ operandGrammar fuel target)
    {source target left right : Ty} {isSum lower : Bool} {m : ModExpr}
    (hc : publicCore source = if isSum then .sum left right else .prod left right)
    (hd : pairDepth source ≤ fuel + 1) (hm : ¬Entails Δ (.defined m))
    (h : Refines Δ lower (.ofTy target) (.modal (.ofTy source) m)) :
    CompareTy.ofTy source ∈ operandGrammar (fuel + 1) target := by
  have hs := pairCore_tag hc
  have ht := (refines_rootTag hR h).symm.trans hs
  have hroot := pairRoot_of_tag hR (CompareTy.wellShaped_ofTy source Δ) isSum hs
  have hspine := rootSpines_refines hΔ hR
    (by cases isSum <;> decide : (if isSum then 4 else 3) ≠ 0)
    (by cases isSum <;> decide : (if isSum then 4 else 3) ≠ 5) hs hm h
  rw [pairCore_depth hc] at hd
  have hmax : max (pairDepth left) (pairDepth right) ≤ fuel := Nat.le_of_succ_le_succ hd
  have hl := pairChild_refines hR hroot h false
  have hr := pairChild_refines hR hroot h true
  rw [pairChild_core hc false] at hl
  rw [pairChild_core hc true] at hr
  have hl' := refines_unwrapModes (rootModes (.ofTy source)) (CompareTy.wellShaped_ofTy left Δ) m hl
  have hr' := refines_unwrapModes (rootModes (.ofTy source)) (CompareTy.wellShaped_ofTy right Δ) m hr
  have hlmem := ih ((Nat.le_max_left _ _).trans hmax)
    (actModes_partial (rootModes (.ofTy source)) hm) hl'
  have hrmem := ih ((Nat.le_max_right _ _).trans hmax)
    (actModes_partial (rootModes (.ofTy source)) hm) hr'
  have hmem := operandGrammar_pair ht hspine hlmem hrmem
  have he : wrapModes (rootModes (.ofTy source))
      (if isSum then CompareTy.sum (.ofTy left) (.ofTy right) else .prod (.ofTy left) (.ofTy right)) =
      .ofTy source := by
    have he := coreModes_eq source
    rw [hc] at he
    cases isSum <;> exact he
  exact he ▸ hmem

 theorem pairDepth_zero_nonpair (source : Ty) (hd : pairDepth source ≤ 0) :
    rootTag (CompareTy.ofTy source).shape ≠ 3 ∧ rootTag (CompareTy.ofTy source).shape ≠ 4 := by
  induction source with
  | modal a m ih => exact ih hd
  | prod a b ia ib | sum a b ia ib => simp only [pairDepth] at hd; omega
  | _ => simp [CompareTy.ofTy, CompareTy.shape, rootTag]

 theorem operandGrammar_complete_depth {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) (hR : Residual Δ)
    (fuel : Nat) {source target : Ty} {m : ModExpr} {lower : Bool}
    (hd : pairDepth source ≤ fuel) (hm : ¬Entails Δ (.defined m))
    (h : Refines Δ lower (.ofTy target) (.modal (.ofTy source) m)) :
    CompareTy.ofTy source ∈ operandGrammar fuel target := by
  induction fuel generalizing source target m lower with
  | zero =>
    have hp := pairDepth_zero_nonpair source hd
    exact operandGrammar_frozen (nonpair_fragment_refines hΔ hp.1 hp.2 hm h) 0
  | succ fuel ih =>
    cases hc : publicCore source with
    | prod left right =>
      exact operandGrammar_pair_complete (isSum := false) hΔ hR
        (fun hd hm h => ih hd hm h) hc hd hm h
    | sum left right =>
      exact operandGrammar_pair_complete (isSum := true) hΔ hR
        (fun hd hm h => ih hd hm h) hc hd hm h
    | modal a n => exact (publicCore_not_modal source a n hc).elim
    | _ =>
      apply operandGrammar_frozen (fuel := fuel + 1)
      apply nonpair_fragment_refines hΔ (hm := hm) (h := h)
      all_goals rw [← publicCore_tag source, hc]
      all_goals simp only [CompareTy.ofTy, CompareTy.shape, rootTag]; decide

/-- Every public operand under a genuinely partial action belongs to a finite
grammar determined solely by its public comparison endpoint. The source
operand, root spine, and inherited children are reconstructed exactly. -/
 theorem public_operandGrammar_complete {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) (hR : Residual Δ)
    {source target : Ty} {m : ModExpr} {lower : Bool} (hm : ¬Entails Δ (.defined m))
    (h : Refines Δ lower (.ofTy target) (.modal (.ofTy source) m)) :
    CompareTy.ofTy source ∈ operandGrammar (pairDepth target) target :=
  operandGrammar_complete_depth hΔ hR _ (le_of_eq (refines_pairDepth hR h)) hm h

/-- The finite grammar covers arbitrary internal witnesses as well: a partial
public boundary first forces the complete operand to be public. -/
 theorem internal_operandGrammar_complete {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) (hR : Residual Δ)
    {source : CompareTy} {target : Ty} {m : ModExpr} {lower : Bool}
    (hm : ¬Entails Δ (.defined m))
    (h : Refines Δ lower (.ofTy target) (.modal source m)) :
    source ∈ operandGrammar (pairDepth target) target := by
  have hp : Public source := by
    cases lower
    · exact partial_context_public_below hΔ hm h
    · exact partial_context_public_above hΔ hm h
  obtain ⟨a, rfl⟩ := hp
  exact public_operandGrammar_complete hΔ hR hm h

 theorem wrapModes_public (modes : List ModExpr) {a : CompareTy} (ha : Public a) :
    Public (wrapModes modes a) := by
  induction modes with
  | nil => exact ha
  | cons m modes ih => exact ih.modal m

 theorem pairWords_public {isSum : Bool} {spines : List (List ModExpr)}
    {left right : List CompareTy}
    (hl : ∀ a ∈ left, Public a) (hr : ∀ a ∈ right, Public a)
    {a : CompareTy} (ha : a ∈ pairWords isSum spines left right) : Public a := by
  obtain ⟨modes, _, hspine⟩ := List.mem_flatMap.mp ha
  obtain ⟨leftTy, hleft, hrightMap⟩ := List.mem_flatMap.mp hspine
  obtain ⟨rightTy, hright, rfl⟩ := List.mem_map.mp hrightMap
  apply wrapModes_public
  cases isSum
  · exact (hl leftTy hleft).prod (hr rightTy hright)
  · exact (hl leftTy hleft).sum (hr rightTy hright)

 theorem operandGrammar_public (fuel : Nat) (endpoint : Ty) {a : CompareTy}
    (ha : a ∈ operandGrammar fuel endpoint) : Public a := by
  induction fuel generalizing endpoint a with
  | zero => exact frozenFragments_public endpoint none ha
  | succ fuel ih =>
    rcases List.mem_append.mp ha with ha | ha
    · exact frozenFragments_public endpoint none ha
    · split at ha
      · exact pairWords_public (fun _ h => ih _ h) (fun _ h => ih _ h) ha
      · split at ha
        · exact pairWords_public (fun _ h => ih _ h) (fun _ h => ih _ h) ha
        · exact (List.not_mem_nil ha).elim

end ModalityInference.ComparisonPartialStructuredCapsule
