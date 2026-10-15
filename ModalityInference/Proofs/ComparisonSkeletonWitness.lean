import ModalityInference.Proofs.ComparisonSkeletonContextBounds

namespace ModalityInference.ComparisonSkeleton

open ComparisonAlgebra ComparisonStructuralProjection ComparisonSkeletonCoordinates ComparisonShapeSolver ComparisonPreparation

namespace Tree

def canonical (Δ : Bounds) : (s : ComparisonShape) → ComparisonSkeletonCoordinates.Tree Δ s
  | .var v => .atom ⟨.var v, trivial, (by intro η hη c hc; cases hc), .refl⟩
  | .unit => .unit Scalar.identity
  | .credit => .credit Scalar.identity
  | .prod a b => .prod (canonical Δ a) (canonical Δ b) Scalar.identity
  | .sum a b => .sum (canonical Δ a) (canonical Δ b) Scalar.identity
  | .fn a b => .fn (canonical Δ a) (canonical Δ b) Scalar.identity

end Tree

noncomputable def witnessTrees {p : SchemePreparation.Prepared}
    (hR : Residual p.assumptions) (solved : ComparisonShapeSolver.Solved) (σ : CompareSubstitution)
    (hs : σ.WellShaped p.assumptions) (ρ : TypeVar → ComparisonShape)
    (hρ : Fixes (sourceAllowed p) ρ)
    (hr : ∀ v, v.index < p.nextType → ComparisonShape.Equivalent p.assumptions (σ.type v).shape
      ((solved.resolveAll v).subst ρ)) : CoordinateTrees p.assumptions p solved := by
  classical
  exact fun n => if hn : n < p.nextType then
    if hd : (σ.type (.flex n)).DefinedUnder p.assumptions then
      rebase hR p ρ hρ (solved.resolveAll (.flex n)) (σ.type (.flex n)) (hs.type _) hd (hr _ hn)
    else Tree.canonical p.assumptions _
  else Tree.canonical p.assumptions _

theorem witnessTrees_eq {p : SchemePreparation.Prepared}
    (hR : Residual p.assumptions) (solved : ComparisonShapeSolver.Solved) (σ : CompareSubstitution)
    (hs : σ.WellShaped p.assumptions) (ρ : TypeVar → ComparisonShape)
    (hρ : Fixes (sourceAllowed p) ρ)
    (hr : ∀ v, v.index < p.nextType → ComparisonShape.Equivalent p.assumptions (σ.type v).shape
      ((solved.resolveAll v).subst ρ)) (n : Nat) (hn : n < p.nextType)
    (hd : (σ.type (.flex n)).DefinedUnder p.assumptions) :
    witnessTrees hR solved σ hs ρ hρ hr n =
      rebase hR p ρ hρ (solved.resolveAll (.flex n)) (σ.type (.flex n)) (hs.type _) hd (hr _ hn) := by
  simp [witnessTrees, hn, hd]

def normalizedAction {Δ : Bounds} (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p solved)
    (σ : CompareSubstitution) : CompareSubstitution :=
  { types := (List.range' p.firstType (p.nextType - p.firstType)).map (fun n => (n, (trees n).reify))
    modes := σ.modes }

private theorem lookup_map_function {α : Type} (f : Nat → α) {ns : List Nat} {n : Nat}
    (hn : n ∈ ns) : (ns.map (fun k => (k, f k))).lookup n = some (f n) := by
  induction ns with
  | nil => cases hn
  | cons k ns ih =>
    by_cases he : n = k
    · simp [he]
    · have hh : n ∈ ns := (List.mem_cons.mp hn).resolve_left he
      have hb : (n == k) = false := beq_eq_false_iff_ne.mpr he
      simpa only [List.map_cons, List.lookup_cons, hb] using ih hh

theorem normalizedAction_type {Δ : Bounds} (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p solved)
    (σ : CompareSubstitution) {n : Nat} (hn : sourceAllowed p (.flex n) = true) :
    (normalizedAction p solved trees σ).type (.flex n) = (trees n).reify := by
  have hr : n ∈ List.range' p.firstType (p.nextType - p.firstType) := by
    simp only [sourceAllowed, Bool.and_eq_true, decide_eq_true_eq] at hn
    simp only [List.mem_range'_1]
    omega
  simp only [normalizedAction, CompareSubstitution.type, lookup_map_function (fun n => (trees n).reify) hr, Option.getD_some]

theorem normalizedAction_fixed {Δ : Bounds} (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p solved)
    (σ : CompareSubstitution) (v : TypeVar) (hv : sourceAllowed p v = false) :
    (normalizedAction p solved trees σ).type v = .var v := by
  cases v with
  | rigid => rfl
  | flex n =>
    have hl : (normalizedAction p solved trees σ).types.lookup n = none := by
      apply List.lookup_eq_none_iff.mpr
      rintro entry he
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp he
      apply bne_iff_ne.mpr
      intro he
      change n = k at he
      subst k
      simp only [sourceAllowed, Bool.and_eq_false_iff, decide_eq_false_iff_not,
        not_le, not_lt] at hv
      simp only [List.mem_range'_1] at hk
      omega
    simp only [CompareSubstitution.type, hl, Option.getD_none]

theorem normalizedAction_mode {Δ : Bounds} (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p solved)
    (σ : CompareSubstitution) (v : ModVar) : (normalizedAction p solved trees σ).mode v = σ.mode v := by
  cases v <;> rfl

theorem normalizedAction_wellShaped {Δ : Bounds} (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p solved)
    (σ : CompareSubstitution) : (normalizedAction p solved trees σ).WellShaped Δ := by
  intro entry he
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp he
  exact ComparisonSkeletonCoordinates.Tree.reify_shaped _

theorem normalizedAction_domains {Δ : Bounds} (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p solved)
    (σ : CompareSubstitution) (hs : σ.DomainsAbove p.firstType p.firstMode) :
    (normalizedAction p solved trees σ).DomainsAbove p.firstType p.firstMode := by
  refine ⟨?_, hs.2⟩
  intro entry he
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp he
  exact (List.mem_range'_1.mp hn).1

theorem resolved_fixedShape {fuel : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved}
    (h : ComparisonShapeSolver.prepare fuel p = .success (.solved solved))
    (hscope : ∀ w ∈ Measure.vars (ComparisonShape.pairs p.assumptions),
      sourceAllowed p w = false) {v : TypeVar} (hv : sourceAllowed p v = false) :
    FixedShape p (solved.resolveAll v) := by
  rw [prepare_resolve_fixed h hscope hv]
  apply fixedShape_of_vars
  intro w hw
  obtain ⟨hfixed, himages⟩ := unify_support (prepare_solved_iff.mp h).1
    (Measure.vars (ComparisonShape.pairs p.assumptions)) Finset.Subset.rfl
  by_cases hmem : v ∈ Measure.vars (ComparisonShape.pairs p.assumptions)
  · exact hscope w (himages v hmem (List.mem_toFinset.mpr hw))
  · change w ∈ (action solved.fixed v).vars at hw
    rw [hfixed v hmem] at hw
    have he : w = v := by simpa [ComparisonShape.vars] using hw
    exact he ▸ hv

theorem fixedShape_subst {p : SchemePreparation.Prepared} (s : ComparisonShape)
    (θ : TypeVar → ComparisonShape) (hf : ∀v∈s.vars, FixedShape p (θ v)) :
    FixedShape p (s.subst θ) := by
  induction s <;> simp_all [ComparisonShape.subst, ComparisonShape.vars, FixedShape]

theorem rebase_fixed_variable {Δ : Bounds} (hR : Residual Δ) (p : SchemePreparation.Prepared)
    (ρ : TypeVar → ComparisonShape) (hρ : Fixes (sourceAllowed p) ρ)
    (s : ComparisonShape) (hf : FixedShape p s) (v : TypeVar)
    (hd : (CompareTy.var v).DefinedUnder Δ)
    (he : ComparisonShape.Equivalent Δ (CompareTy.var v).shape (s.subst ρ)) :
    (rebase hR p ρ hρ s (.var v) trivial hd he).reify = .var v := by
  rw [rebase_fixed_reify hR p ρ hρ s hf]
  have hh := rootTag_equivalent hR he
  rw [shape_subst_fixed hρ hf] at hh
  cases s
  · rfl
  all_goals simp only [CompareTy.shape, rootTag] at hh; omega

theorem rebase_image_eq_var {Δ : Bounds} (hR : Residual Δ) (p : SchemePreparation.Prepared)
    (ρ : TypeVar → ComparisonShape) (hρ : Fixes (sourceAllowed p) ρ)
    (s : ComparisonShape) (hf : FixedShape p s) (a : CompareTy) (hs : a.WellShaped Δ)
    (hd : a.DefinedUnder Δ) (he : ComparisonShape.Equivalent Δ a.shape (s.subst ρ))
    (v : TypeVar) (hv : a = .var v) :
    (rebase hR p ρ hρ s a hs hd he).reify = .var v := by
  subst a
  exact rebase_fixed_variable hR p ρ hρ s hf v hd he

/-- The finite normalized action replaces exactly source parameters and keeps
all mode choices shared with the original witness. -/
theorem normalizedAction_rebased {ambient : Bounds} {source target : Scheme}
    {fuel : Nat} {solved : ComparisonShapeSolver.Solved} {σ : CompareSubstitution}
    (hshape : ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare ambient source target) =
      .success (.solved solved))
    (hw : PreparedWitness (SchemePreparation.prepare ambient source target) σ)
    (hR : Residual (SchemePreparation.prepare ambient source target).assumptions)
    (types : Finset TypeVar)
    (ht : ∀v∈types, v.index < (SchemePreparation.prepare ambient source target).nextType) :
    let p := SchemePreparation.prepare ambient source target
    let ρ := shapeRealizer p σ solved.fixedShapes
    let hr := prepared_witness_shape_realizer hshape hw
    let trees := witnessTrees hR solved σ hw.2.1 ρ hr.1 hr.2
    Rebased hR p ρ hr.1 solved.resolveAll σ (normalizedAction p solved trees σ) types := by
  dsimp only
  let p := SchemePreparation.prepare ambient source target
  let ρ := shapeRealizer p σ solved.fixedShapes
  have hr := prepared_witness_shape_realizer hshape hw
  let trees := witnessTrees hR solved σ hw.2.1 ρ hr.1 hr.2
  refine ⟨hw.2.1, (fun v hv => hr.2 v (ht v hv)), ?_, normalizedAction_mode p solved trees σ⟩
  intro v hv hd
  by_cases ha : sourceAllowed p v = true
  · obtain ⟨n, rfl, hn, hn'⟩ := (sourceAllowed_iff p v).mp ha
    rw [normalizedAction_type p solved trees σ ha]
    exact congrArg (ComparisonSkeletonCoordinates.Tree.reify)
      (witnessTrees_eq hR solved σ hw.2.1 ρ hr.1 hr.2 n hn' hd)
  · have ha : sourceAllowed p v = false := Bool.eq_false_iff.mpr ha
    have hs := prepared_witness_fixed hw v (ht v hv) ha
    rw [normalizedAction_fixed p solved trees σ v ha]
    symm
    have hf := resolved_fixedShape hshape (prepared_assumptions_fixed ambient source target) ha
    exact rebase_image_eq_var hR p ρ hr.1 _ hf (σ.type v) _ hd _ v hs

theorem prepared_target_fixedShape {ambient : Bounds} {source target : Scheme}
    {fuel : Nat} {solved : ComparisonShapeSolver.Solved}
    (h : ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare ambient source target) =
      .success (.solved solved)) :
    FixedShape (SchemePreparation.prepare ambient source target)
      ((ComparisonShape.ofTy (SchemePreparation.prepare ambient source target).targetType).subst solved.resolveAll) := by
  apply fixedShape_subst
  intro v hv
  apply resolved_fixedShape h (prepared_assumptions_fixed ambient source target)
  have hi := ((TypeExpr.bounded_iff _ _ _).mp
    (SchemePreparation.prepare_targetType_bounded_first ambient source target)).1 v ((mem_vars_ofTy _ _).mp hv)
  cases v <;> simp_all [sourceAllowed, TypeVar.index, Nat.not_le_of_gt]

theorem prepared_body_fixedShape {ambient : Bounds} {source target : Scheme}
    {fuel : Nat} {solved : ComparisonShapeSolver.Solved}
    (h : ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare ambient source target) =
      .success (.solved solved)) :
    FixedShape (SchemePreparation.prepare ambient source target)
      ((ComparisonShape.ofTy (SchemePreparation.prepare ambient source target).sourceType).subst solved.resolveAll) := by
  have he := (prepare_sound h).2
    (ComparisonShape.ofTy (SchemePreparation.prepare ambient source target).sourceType,
      ComparisonShape.ofTy (SchemePreparation.prepare ambient source target).targetType)
    (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  rw [he]
  exact prepared_target_fixedShape h

/-- Every defined prepared comparison has a simultaneous source-domain witness
whose images are the coordinate trees of the actual solved templates. Guarded
source bounds and the public target are preserved unchanged. -/
theorem prepared_normalized {ambient : Bounds} {source target : Scheme}
    {fuel : Nat} {solved : ComparisonShapeSolver.Solved} {σ : CompareSubstitution}
    (hshape : ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare ambient source target) =
      .success (.solved solved))
    (hw : PreparedWitness (SchemePreparation.prepare ambient source target) σ)
    (hR : Residual (SchemePreparation.prepare ambient source target).assumptions)
    (hs : (σ.ty (SchemePreparation.prepare ambient source target).sourceType).DefinedUnder
      (SchemePreparation.prepare ambient source target).assumptions)
    (hd : (CompareTy.ofTy (SchemePreparation.prepare ambient source target).targetType).DefinedUnder
      (SchemePreparation.prepare ambient source target).assumptions) :
    let p := SchemePreparation.prepare ambient source target
    let ρ := shapeRealizer p σ solved.fixedShapes
    let hr := prepared_witness_shape_realizer hshape hw
    let trees := witnessTrees hR solved σ hw.2.1 ρ hr.1 hr.2
    PreparedWitness p (normalizedAction p solved trees σ) := by
  dsimp only
  let p := SchemePreparation.prepare ambient source target
  let ρ := shapeRealizer p σ solved.fixedShapes
  have hr := prepared_witness_shape_realizer hshape hw
  let trees := witnessTrees hR solved σ hw.2.1 ρ hr.1 hr.2
  let types := p.sourceType.typeVars ∪ p.sourceBounds.typeVars
  have ht : ∀v∈types, v.index < p.nextType := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact ((TypeExpr.bounded_iff _ _ _).mp
        (SchemePreparation.prepare_sourceType_bounded ambient source target)).1 v hv
    · exact ((Bounds.bounded_iff _ _ _).mp
        (SchemePreparation.prepare_sourceBounds_bounded ambient source target)).1 v hv
  have hm := normalizedAction_rebased hshape hw hR types ht
  refine ⟨normalizedAction_domains p solved trees σ hw.1,
    normalizedAction_wellShaped p solved trees σ, ?_, ?_⟩
  · exact hm.bounds p.sourceBounds (fun _ hv => Finset.mem_union_right _ hv)
      (fun pair hp => (prepare_sound hshape).2 pair (List.mem_append_left _ hp)) hw.2.2.1
  · exact hm.body (fun _ hv => Finset.mem_union_left _ hv)
      (prepared_body_fixedShape hshape) hs hd hw.2.2.2

end ModalityInference.ComparisonSkeleton
