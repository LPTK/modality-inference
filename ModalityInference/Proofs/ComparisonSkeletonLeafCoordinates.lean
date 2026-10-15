import ModalityInference.Proofs.ComparisonSkeletonFactor

namespace ModalityInference.ComparisonSkeleton

open ComparisonSkeletonCoordinates ComparisonShapeSolver

theorem leaves_defaultShape (p : SchemePreparation.Prepared) (s : ComparisonShape) (nt : Nat) :
    leaves p (defaultShape p s) nt = leaves p s nt := by
  induction s generalizing nt <;> simp_all only [defaultShape, leaves, typeCount_defaultShape]
  split <;> simp_all [leaves]

theorem coordinateTypes_leaf {Δ : Bounds} (p : SchemePreparation.Prepared)
    {s : ComparisonShape} (tree : ComparisonSkeletonCoordinates.Tree Δ s)
    (hf : FixedShape p s) (nt : Nat) :
    ∀leaf∈leaves p s nt, ∃a, (leaf.name, a) ∈ coordinateTypes p tree nt ∧
      ComparisonShape.Equivalent Δ a.shape (.var leaf.shapeClass) := by
  induction tree generalizing nt with
  | atom a =>
    simp only [FixedShape] at hf
    intro leaf hl
    simp only [leaves, hf, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hl
    subst leaf
    exact ⟨a.type, List.mem_singleton_self _, a.shape_eq⟩
  | unit | credit => simp [leaves]
  | prod a b m iha ihb | sum a b m iha ihb | fn a b m iha ihb =>
    intro leaf hl
    rcases List.mem_append.mp hl with hl | hl
    · obtain ⟨image, hi, hs⟩ := iha hf.1 nt leaf hl
      exact ⟨image, List.mem_append_left _ hi, hs⟩
    · obtain ⟨image, hi, hs⟩ := ihb hf.2 _ leaf hl
      exact ⟨image, List.mem_append_right _ hi, hs⟩

theorem forestTypes_leaf {Δ : Bounds} (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p solved)
    (names : List Nat) (nt nm : Nat) :
    ∀leaf∈(allocate p solved names nt nm).leaves,
      ∃a, (leaf.name, a) ∈ forestTypes p solved trees names nt ∧
        ComparisonShape.Equivalent Δ a.shape (.var leaf.shapeClass) := by
  induction names generalizing nt nm with
  | nil => simp [allocate]
  | cons v rest ih =>
    intro leaf hl
    rcases List.mem_append.mp hl with hl | hl
    · have hh := coordinateTypes_leaf p (trees v)
        (defaultShape_fixed p (solved.resolveAll (.flex v))) nt
      rw [leaves_defaultShape] at hh
      obtain ⟨a, ha, hs⟩ := hh leaf hl
      exact ⟨a, List.mem_append_left _ ha, hs⟩
    · obtain ⟨a, ha, hs⟩ := ih _ _ leaf hl
      exact ⟨a, List.mem_append_right _ ha, hs⟩

private theorem lookup_nodup {α : Type} {entries : List (Nat × α)}
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

/-- Each coordinate lookup inhabits its actual allocated opaque shape class. -/
theorem forestExtension_leaf {Δ : Bounds} (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p solved)
    (names : List Nat) (nt nm : Nat) (σ : CompareSubstitution)
    {leaf : Leaf} (hl : leaf ∈ (allocate p solved names nt nm).leaves) :
    ComparisonShape.Equivalent Δ ((forestExtension p solved trees names nt nm σ).type (.flex leaf.name)).shape
      (.var leaf.shapeClass) := by
  obtain ⟨a, ha, hs⟩ := forestTypes_leaf p solved trees names nt nm leaf hl
  have hh := lookup_nodup ((forestTypes_keys p solved trees names nt).symm ▸ List.nodup_range') ha
  simpa only [forestExtension, CompareSubstitution.type, hh, Option.getD_some] using hs

theorem preparedForest_leaf {Δ : Bounds} (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p solved)
    (σ : CompareSubstitution) {leaf : Leaf} (hl : leaf ∈ (prepare p solved).leaves) :
    ComparisonShape.Equivalent Δ ((preparedForest p solved trees σ).type (.flex leaf.name)).shape
      (.var leaf.shapeClass) :=
  forestExtension_leaf p solved trees _ _ _ σ hl

theorem preparedForest_domains {Δ : Bounds} (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p solved)
    (σ : CompareSubstitution) (hm : p.firstMode ≤ p.nextMode)
    (hσ : σ.DomainsAbove p.firstType p.firstMode) :
    (preparedForest p solved trees σ).DomainsAbove p.nextType p.firstMode := by
  constructor
  · intro entry he
    have hk : entry.1 ∈ (forestTypes p solved trees
        (List.range' p.firstType (p.nextType - p.firstType)) p.nextType).map Prod.fst :=
      List.mem_map.mpr ⟨entry, he, rfl⟩
    rw [forestTypes_keys] at hk
    exact (List.mem_range'_1.mp hk).1
  · intro entry he
    rcases List.mem_append.mp he with he | he
    · have hk : entry.1 ∈ (forestModes p solved trees
          (List.range' p.firstType (p.nextType - p.firstType)) p.nextMode).map Prod.fst :=
        List.mem_map.mpr ⟨entry, he, rfl⟩
      rw [forestModes_keys] at hk
      exact hm.trans (List.mem_range'_1.mp hk).1
    · exact hσ.2 entry he

end ModalityInference.ComparisonSkeleton
