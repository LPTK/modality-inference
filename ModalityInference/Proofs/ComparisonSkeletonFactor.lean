import ModalityInference.Proofs.ComparisonSkeletonWitness

namespace ModalityInference.ComparisonSkeleton

open ComparisonSkeletonCoordinates ComparisonShapeSolver ComparisonPreparation

/-- Fresh coordinate modes precede the original shared source-mode assignment.
The ranges are disjoint on every prepared input expression. -/
def forestExtension {Δ : Bounds} (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p solved)
    (names : List Nat) (nt nm : Nat) (σ : CompareSubstitution) : CompareSubstitution :=
  { types := forestTypes p solved trees names nt
    modes := forestModes p solved trees names nm ++ σ.modes }

private theorem lookup_mem_keys_nodup {α : Type} {entries : List (Nat × α)}
    (hn : (entries.map Prod.fst).Nodup) {n : Nat} {a : α} (ha : (n, a) ∈ entries) :
    entries.lookup n = some a := by
  induction entries with
  | nil => contradiction
  | cons entry entries ih =>
    rcases entry with ⟨key, value⟩
    have hh := List.nodup_cons.mp hn
    rcases List.mem_cons.mp ha with he | he
    · cases he
      simp
    · have hne : n ≠ key := by
        intro hn
        exact hh.1 (hn ▸ List.mem_map.mpr ⟨(n, a), he, rfl⟩)
      have hb : (n == key) = false := beq_eq_false_iff_ne.mpr hne
      simpa only [List.lookup_cons, hb] using ih hh.2 he

theorem forestExtension_realizes {Δ : Bounds} (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p solved)
    (names : List Nat) (nt nm : Nat) (σ : CompareSubstitution) :
    ∀ entry ∈ (allocate p solved names nt nm).substitution.types,
      (forestExtension p solved trees names nt nm σ).ty entry.2 = (trees entry.1).reify := by
  apply allocate_coordinates p solved trees names nt nm
  · intro entry he
    have hh := lookup_mem_keys_nodup
      ((forestTypes_keys p solved trees names nt).symm ▸ List.nodup_range') he
    simp only [forestExtension, CompareSubstitution.type, hh, Option.getD_some]
  · intro entry he
    have hh := lookup_mem_keys_nodup
      ((forestModes_keys p solved trees names nm).symm ▸ List.nodup_range') he
    simp only [forestExtension, CompareSubstitution.mode, List.lookup_append, hh, Option.some_or,
      Option.getD_some]

theorem forestExtension_type {Δ : Bounds} (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p solved)
    (names : List Nat) (nt nm : Nat) (σ : CompareSubstitution) {v : Nat} (hv : v ∈ names) :
    (forestExtension p solved trees names nt nm σ).ty
      ((allocate p solved names nt nm).substitution.type (.flex v)) = (trees v).reify := by
  cases hl : (allocate p solved names nt nm).substitution.types.lookup v with
  | none =>
    have hn := List.lookup_eq_none_iff.mp hl
    have hm : v ∈ (allocate p solved names nt nm).substitution.types.map Prod.fst :=
      (allocate_domain p solved names nt nm).symm ▸ hv
    obtain ⟨entry, he, hh⟩ := List.mem_map.mp hm
    have hne := hn entry he
    simp only [bne_iff_ne] at hne
    exact False.elim (hne hh.symm)
  | some body =>
    obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp hl
    have hh : (v, body) ∈ (allocate p solved names nt nm).substitution.types := by simp [he]
    simpa only [Substitution.type, hl, Option.getD_some] using
      forestExtension_realizes p solved trees names nt nm σ (v, body) hh

theorem forestExtension_type_fixed {Δ : Bounds} (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p solved)
    (names : List Nat) (nt nm : Nat) (σ : CompareSubstitution) (v : TypeVar) (hv : v.index < nt) :
    (forestExtension p solved trees names nt nm σ).type v = .var v := by
  cases v with
  | rigid => rfl
  | flex n =>
    have hl : (forestTypes p solved trees names nt).lookup n = none := by
      apply List.lookup_eq_none_iff.mpr
      intro entry he
      have hk : entry.1 ∈ (forestTypes p solved trees names nt).map Prod.fst :=
        List.mem_map.mpr ⟨entry, he, rfl⟩
      rw [forestTypes_keys] at hk
      have hi := (List.mem_range'_1.mp hk).1
      apply bne_iff_ne.mpr
      intro heq
      simp only [TypeVar.index] at hv
      omega
    simp only [forestExtension, CompareSubstitution.type, hl, Option.getD_none]

theorem forestExtension_mode {Δ : Bounds} (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p solved)
    (names : List Nat) (nt nm : Nat) (σ : CompareSubstitution) (v : ModVar) (hv : v.index < nm) :
    (forestExtension p solved trees names nt nm σ).mode v = σ.mode v := by
  cases v with
  | rigid => rfl
  | flex n =>
    have hl : (forestModes p solved trees names nm).lookup n = none := by
      apply List.lookup_eq_none_iff.mpr
      intro entry he
      have hk : entry.1 ∈ (forestModes p solved trees names nm).map Prod.fst :=
        List.mem_map.mpr ⟨entry, he, rfl⟩
      rw [forestModes_keys] at hk
      have hi := (List.mem_range'_1.mp hk).1
      apply bne_iff_ne.mpr
      intro heq
      simp only [ModVar.index] at hv
      omega
    simp only [forestExtension, CompareSubstitution.mode, List.lookup_append, hl, Option.none_or]

theorem allocate_modes_empty (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (names : List Nat) (nt nm : Nat) :
    (allocate p solved names nt nm).substitution.modes = [] := by
  cases names <;> rfl

theorem prepare_mode (p : SchemePreparation.Prepared) (solved : ComparisonShapeSolver.Solved)
    (v : ModVar) : (prepare p solved).substitution.mode v = .var v := by
  cases v with
  | rigid => rfl
  | flex n =>
    change ((prepare p solved).substitution.modes.lookup n).getD _ = _
    rw [prepare, allocate_modes_empty]
    rfl

def preparedForest {Δ : Bounds} (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p solved)
    (σ : CompareSubstitution) : CompareSubstitution :=
  forestExtension p solved trees (List.range' p.firstType (p.nextType - p.firstType))
    p.nextType p.nextMode σ

theorem preparedForest_type {Δ : Bounds} (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p solved)
    (σ : CompareSubstitution) (v : TypeVar) (hv : v.index < p.nextType) :
    (ComparisonExactContext.finish (prepare p solved).substitution (preparedForest p solved trees σ)).type v =
      (normalizedAction p solved trees σ).type v := by
  rw [ComparisonExactContext.finish_type]
  by_cases ha : sourceAllowed p v = true
  · obtain ⟨n, rfl, hn, hn'⟩ := (sourceAllowed_iff p v).mp ha
    rw [normalizedAction_type p solved trees σ ha]
    apply forestExtension_type
    simp only [List.mem_range'_1]
    omega
  · have ha : sourceAllowed p v = false := Bool.eq_false_iff.mpr ha
    rw [prepare_fixes p solved v ha, normalizedAction_fixed p solved trees σ v ha]
    exact forestExtension_type_fixed p solved trees _ _ _ σ v hv

theorem preparedForest_mode {Δ : Bounds} (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p solved)
    (σ : CompareSubstitution) (v : ModVar) (hv : v.index < p.nextMode) :
    (ComparisonExactContext.finish (prepare p solved).substitution (preparedForest p solved trees σ)).mode v =
      (normalizedAction p solved trees σ).mode v := by
  rw [ComparisonExactContext.finish_mode, prepare_mode, ModExpr.subst, normalizedAction_mode]
  exact forestExtension_mode p solved trees _ _ _ σ v hv

theorem preparedForest_ty {Δ : Bounds} (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p solved)
    (σ : CompareSubstitution) (t : Ty) (ht : t.Bounded p.nextType p.nextMode) :
    (preparedForest p solved trees σ).ty ((prepare p solved).substitution.ty t) =
      (normalizedAction p solved trees σ).ty t := by
  rw [←ComparisonExactContext.finish_ty]
  apply CompareSubstitution.ty_congr_on
  · exact fun v hv => preparedForest_type p solved trees σ v ((TypeExpr.bounded_iff _ _ _).mp ht |>.1 v hv)
  · exact fun v hv => preparedForest_mode p solved trees σ v ((TypeExpr.bounded_iff _ _ _).mp ht |>.2 v hv)

theorem preparedForest_bounds {Δ : Bounds} (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p solved)
    (σ : CompareSubstitution) (cs : Bounds) (ht : cs.Bounded p.nextType p.nextMode) :
    AlgebraEntailsAll Δ ((preparedForest p solved trees σ).bounds ((prepare p solved).substitution.bounds cs)) ↔
      AlgebraEntailsAll Δ ((normalizedAction p solved trees σ).bounds cs) := by
  rw [←ComparisonExactContext.finish_bounds]
  apply CompareSubstitution.algebra_bounds_congr
  · exact fun c hc v hv => preparedForest_type p solved trees σ v
      (((Constraint.bounded_iff _ _ _).mp (ht c hc)).1 v hv)
  · exact fun c hc v hv => preparedForest_mode p solved trees σ v
      (((Constraint.bounded_iff _ _ _).mp (ht c hc)).2 v hv)

theorem preparedForest_guarded {Δ : Bounds} (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p solved)
    (σ : CompareSubstitution) :
    (preparedForest p solved trees σ).WellShaped Δ ∧
      ∀entry∈(preparedForest p solved trees σ).types, entry.2.DefinedUnder Δ := by
  have h := forestTypes_guarded p solved trees (List.range' p.firstType (p.nextType - p.firstType)) p.nextType
  exact ⟨fun entry he => (h entry he).1, fun entry he => (h entry he).2⟩

/-- Actual structural allocation preserves a defined prepared witness with one
joint finite coordinate assignment and the same original source-mode choices. -/
theorem prepared_template_factor {ambient : Bounds} {source target : Scheme}
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
    ∃ trees : CoordinateTrees p.assumptions p solved,
      let core := preparedForest p solved trees σ
      core.WellShaped p.assumptions ∧
      (∀entry∈core.types, entry.2.DefinedUnder p.assumptions) ∧
      AlgebraEntailsAll p.assumptions (core.bounds ((prepare p solved).substitution.bounds p.sourceBounds)) ∧
      AlgebraSubtype p.assumptions (core.ty ((prepare p solved).substitution.ty p.sourceType)) (.ofTy p.targetType) := by
  let p := SchemePreparation.prepare ambient source target
  let ρ := shapeRealizer p σ solved.fixedShapes
  have hr := prepared_witness_shape_realizer hshape hw
  let trees := witnessTrees hR solved σ hw.2.1 ρ hr.1 hr.2
  have hn := prepared_normalized hshape hw hR hs hd
  refine ⟨trees, (preparedForest_guarded p solved trees σ).1,
    (preparedForest_guarded p solved trees σ).2, ?_, ?_⟩
  · exact (preparedForest_bounds p solved trees σ p.sourceBounds
      (SchemePreparation.prepare_sourceBounds_bounded ambient source target)).mpr hn.2.2.1
  · rw [preparedForest_ty p solved trees σ p.sourceType
      (SchemePreparation.prepare_sourceType_bounded ambient source target)]
    exact hn.2.2.2

end ModalityInference.ComparisonSkeleton
