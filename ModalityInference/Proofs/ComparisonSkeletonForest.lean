import ModalityInference.Proofs.ComparisonSkeletonRealization

namespace ModalityInference.ComparisonSkeleton

open ComparisonSkeletonCoordinates ComparisonShapeSolver

abbrev CoordinateTrees (Δ : Bounds) (p : SchemePreparation.Prepared) (shapes : ComparisonShapeSolver.Solved) :=
  ∀ v : Nat, Tree Δ (defaultShape p (shapes.resolveAll (.flex v)))

def typeSpan (p : SchemePreparation.Prepared) (shapes : ComparisonShapeSolver.Solved) : List Nat → Nat
  | [] => 0
  | v :: rest => typeCount p (shapes.resolveAll (.flex v)) + typeSpan p shapes rest

def modeSpan (p : SchemePreparation.Prepared) (shapes : ComparisonShapeSolver.Solved) : List Nat → Nat
  | [] => 0
  | v :: rest => modeCount p (shapes.resolveAll (.flex v)) + modeSpan p shapes rest

def forestTypes {Δ : Bounds} (p : SchemePreparation.Prepared) (shapes : ComparisonShapeSolver.Solved)
    (trees : CoordinateTrees Δ p shapes) : List Nat → Nat → List (Nat × CompareTy)
  | [], _ => []
  | v :: rest, nt => coordinateTypes p (trees v) nt ++
      forestTypes p shapes trees rest (nt + typeCount p (shapes.resolveAll (.flex v)))

def forestModes {Δ : Bounds} (p : SchemePreparation.Prepared) (shapes : ComparisonShapeSolver.Solved)
    (trees : CoordinateTrees Δ p shapes) : List Nat → Nat → List (Nat × ModExpr)
  | [], _ => []
  | v :: rest, nm => coordinateModes p (trees v) nm ++
      forestModes p shapes trees rest (nm + modeCount p (shapes.resolveAll (.flex v)))

def forestAction {Δ : Bounds} (p : SchemePreparation.Prepared) (shapes : ComparisonShapeSolver.Solved)
    (trees : CoordinateTrees Δ p shapes) (names : List Nat) (nt nm : Nat) : CompareSubstitution :=
  ⟨forestTypes p shapes trees names nt, forestModes p shapes trees names nm⟩

theorem allocate_next {p : SchemePreparation.Prepared} {shapes : ComparisonShapeSolver.Solved}
    (names : List Nat) (nt nm : Nat) :
    (allocate p shapes names nt nm).nextType = nt + typeSpan p shapes names ∧
      (allocate p shapes names nt nm).nextMode = nm + modeSpan p shapes names := by
  induction names generalizing nt nm with
  | nil => simp [allocate, typeSpan, modeSpan]
  | cons v rest ih =>
    simp only [allocate, typeSpan, modeSpan]
    have hh := ih (nt + typeCount p (shapes.resolveAll (.flex v)))
      (nm + modeCount p (shapes.resolveAll (.flex v)))
    exact ⟨hh.1.trans (Nat.add_assoc _ _ _), hh.2.trans (Nat.add_assoc _ _ _)⟩

theorem forestTypes_keys {Δ : Bounds} (p : SchemePreparation.Prepared) (shapes : ComparisonShapeSolver.Solved)
    (trees : CoordinateTrees Δ p shapes) (names : List Nat) (nt : Nat) :
    (forestTypes p shapes trees names nt).map Prod.fst = List.range' nt (typeSpan p shapes names) := by
  induction names generalizing nt with
  | nil => simp [forestTypes, typeSpan]
  | cons v rest ih =>
    simp only [forestTypes, List.map_append, coordinateTypes_keys p (trees v) (defaultShape_fixed p _),
      typeCount_defaultShape, ih, typeSpan]
    simpa only [Nat.one_mul] using List.range'_append (s := nt) (step := 1)

theorem forestModes_keys {Δ : Bounds} (p : SchemePreparation.Prepared) (shapes : ComparisonShapeSolver.Solved)
    (trees : CoordinateTrees Δ p shapes) (names : List Nat) (nm : Nat) :
    (forestModes p shapes trees names nm).map Prod.fst = List.range' nm (modeSpan p shapes names) := by
  induction names generalizing nm with
  | nil => simp [forestModes, modeSpan]
  | cons v rest ih =>
    simp only [forestModes, List.map_append, coordinateModes_keys p (trees v) (defaultShape_fixed p _),
      modeCount_defaultShape, ih, modeSpan]
    simpa only [Nat.one_mul] using List.range'_append (s := nm) (step := 1)


/-- The same global coordinate assignment realizes every image emitted by
`allocate`, so shared source variables keep one simultaneous witness. -/
theorem allocate_coordinates {Δ : Bounds} (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p shapes)
    (names : List Nat) (nt nm : Nat) (σ : CompareSubstitution)
    (ht : ∀ entry ∈ forestTypes p shapes trees names nt, σ.type (.flex entry.1) = entry.2)
    (hm : ∀ entry ∈ forestModes p shapes trees names nm, σ.mode (.flex entry.1) = entry.2) :
    ∀ entry ∈ (allocate p shapes names nt nm).substitution.types,
      σ.ty entry.2 = (trees entry.1).reify := by
  induction names generalizing nt nm with
  | nil => simp [allocate]
  | cons v rest ih =>
    intro entry he
    rcases List.mem_cons.mp he with he | he
    · subst entry
      have hh := build_coordinates p (trees v) (defaultShape_fixed p _) nt nm σ
        (fun entry he => ht entry (List.mem_append_left _ he))
        (fun entry he => hm entry (List.mem_append_left _ he))
      simpa only [build_defaultShape] using hh
    · exact ih _ _
        (fun entry he => ht entry (List.mem_append_right _ he))
        (fun entry he => hm entry (List.mem_append_right _ he)) entry he

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
      have hb : (n == key) = false := by simp [hne]
      simpa only [List.lookup_cons, hb] using ih hh.2 he

theorem forestAction_realizes {Δ : Bounds} (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p shapes)
    (names : List Nat) (nt nm : Nat) :
    ∀ entry ∈ (allocate p shapes names nt nm).substitution.types,
      (forestAction p shapes trees names nt nm).ty entry.2 = (trees entry.1).reify := by
  apply allocate_coordinates p shapes trees names nt nm
  · intro entry he
    have hh := lookup_mem_keys_nodup
      ((forestTypes_keys p shapes trees names nt).symm ▸ List.nodup_range') he
    simp only [forestAction, CompareSubstitution.type, hh, Option.getD_some]
  · intro entry he
    have hh := lookup_mem_keys_nodup
      ((forestModes_keys p shapes trees names nm).symm ▸ List.nodup_range') he
    simp only [forestAction, CompareSubstitution.mode, hh, Option.getD_some]

theorem forestAction_type {Δ : Bounds} (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p shapes)
    (names : List Nat) (nt nm : Nat) {v : Nat} (hv : v ∈ names) :
    (forestAction p shapes trees names nt nm).ty
      ((allocate p shapes names nt nm).substitution.type (.flex v)) = (trees v).reify := by
  cases hl : (allocate p shapes names nt nm).substitution.types.lookup v with
  | none =>
    have hn := List.lookup_eq_none_iff.mp hl
    have hm : v ∈ (allocate p shapes names nt nm).substitution.types.map Prod.fst :=
      (allocate_domain p shapes names nt nm).symm ▸ hv
    obtain ⟨entry, he, hh⟩ := List.mem_map.mp hm
    have hne := hn entry he
    simp only [bne_iff_ne] at hne
    exact False.elim (hne hh.symm)
  | some body =>
    obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp hl
    have hh : (v, body) ∈ (allocate p shapes names nt nm).substitution.types := by simp [he]
    simpa only [Substitution.type, hl, Option.getD_some] using
      forestAction_realizes p shapes trees names nt nm (v, body) hh


theorem forestTypes_guarded {Δ : Bounds} (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p shapes)
    (names : List Nat) (nt : Nat) :
    ∀ entry ∈ forestTypes p shapes trees names nt, entry.2.WellShaped Δ ∧ entry.2.DefinedUnder Δ := by
  induction names generalizing nt with
  | nil => simp [forestTypes]
  | cons v rest ih =>
    intro entry he
    rcases List.mem_append.mp he with he | he
    · exact coordinateTypes_guarded p (trees v) nt entry he
    · exact ih _ entry he

theorem forestModes_defined {Δ : Bounds} (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p shapes)
    (names : List Nat) (nm : Nat) :
    ∀ entry ∈ forestModes p shapes trees names nm, Entails Δ (.defined entry.2) := by
  induction names generalizing nm with
  | nil => simp [forestModes]
  | cons v rest ih =>
    intro entry he
    rcases List.mem_append.mp he with he | he
    · exact coordinateModes_defined p (trees v) nm entry he
    · exact ih _ entry he

/-- Every finite family of normalized witnesses factors simultaneously through
exactly the fresh variables allocated by the production template builder. -/
theorem allocate_factor {Δ : Bounds} (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p shapes)
    (names : List Nat) (nt nm : Nat) :
    let templates := allocate p shapes names nt nm
    let σ := forestAction p shapes trees names nt nm
    (∀ v ∈ names, σ.ty (templates.substitution.type (.flex v)) = (trees v).reify) ∧
      σ.types.map Prod.fst = List.range' nt (templates.nextType - nt) ∧
      σ.modes.map Prod.fst = List.range' nm (templates.nextMode - nm) ∧
      σ.WellShaped Δ ∧ (∀ entry ∈ σ.types, entry.2.DefinedUnder Δ) ∧
      (∀ entry ∈ σ.modes, Entails Δ (.defined entry.2)) := by
  refine ⟨fun v hv => forestAction_type p shapes trees names nt nm hv, ?_, ?_,
    fun entry he => (forestTypes_guarded p shapes trees names nt entry he).1,
    fun entry he => (forestTypes_guarded p shapes trees names nt entry he).2,
    forestModes_defined p shapes trees names nm⟩
  · simp only [(allocate_next names nt nm).1, Nat.add_sub_cancel_left]
    exact forestTypes_keys p shapes trees names nt
  · simp only [(allocate_next names nt nm).2, Nat.add_sub_cancel_left]
    exact forestModes_keys p shapes trees names nm

end ModalityInference.ComparisonSkeleton
