import ModalityInference.Proofs.ComparisonBareShapes
import ModalityInference.Proofs.ComparisonPreparedBounds
import ModalityInference.Proofs.ComparisonContextSupport

namespace ModalityInference.ComparisonChecker

/-- The deterministic preparations performed between scalar discovery and
structural reduction. -/
structure Setup where
  original : SchemePreparation.Prepared
  before : Substitution
  shapes : ComparisonShapeSolver.Solved
  known : List ModExpr
  shared : Bool

def Setup.input (s : Setup) : SchemePreparation.Prepared :=
  ComparisonExactContext.rewrite s.original s.before

def Setup.total (s : Setup) : ModExpr → Bool := ComparisonBody.isTotal s.known

def Setup.absorption (s : Setup) : ComparisonAbsorption.Result :=
  ComparisonAbsorption.plan s.input s.total

def Setup.absorbed (s : Setup) : SchemePreparation.Prepared :=
  { s.input with sourceType := s.absorption.body }

def Setup.annotations (s : Setup) : ComparisonPartialModes.Result :=
  ComparisonAnnotations.prepare s.absorbed s.total

def Setup.work (s : Setup) : SchemePreparation.Prepared :=
  { s.absorbed with sourceType := s.annotations.substitution.ty s.absorbed.sourceType }

def Setup.bare (s : Setup) : List Nat :=
  (if s.shared then ComparisonBody.eligible s.work s.total else ComparisonPartial.eligible s.work).filter
    (fun n => !(s.before.types.map Prod.fst).contains n)

def Setup.names (s : Setup) : List Nat :=
  (List.range' s.original.firstType (s.original.nextType - s.original.firstType)).filter
    (fun n => !(s.before.types.map Prod.fst).contains n && !s.bare.contains n)

def Setup.templates (s : Setup) : ComparisonSkeleton.Templates :=
  ComparisonSkeleton.allocate s.work s.shapes s.names s.original.nextType s.annotations.nextMode

def Setup.reduced (s : Setup) (result : ComparisonReduction.State) : ComparisonReduction.State :=
  { result with modes :=
    (s.annotations.bounds ++ ComparisonGuardedTotal.scalarBounds s.input.sourceBounds) ++ result.modes }

def Setup.modeIds (s : Setup) : List Nat :=
  (List.range' s.original.firstMode (s.templates.nextMode - s.original.firstMode)).filter
    (fun n => !(s.before.modes.map Prod.fst ++ s.absorption.modes ++
      s.annotations.images.map Prod.fst).contains n)

theorem Setup.bare_range (s : Setup) {n : Nat} (hn : n ∈ s.bare) :
    s.original.firstType ≤ n ∧ n < s.original.nextType := by
  have hn := (List.mem_filter.mp hn).1
  split at hn
  all_goals have hr := (List.mem_filter.mp hn).1
  all_goals simp only [List.mem_range'] at hr
  all_goals change ∃ i < s.original.nextType - s.original.firstType,
    n = s.original.firstType + 1 * i at hr
  all_goals obtain ⟨i, hi, he⟩ := hr
  all_goals constructor <;> omega

theorem Setup.bare_avoids_bounds (s : Setup) {n : Nat} (hn : n ∈ s.bare) :
    ∀ c ∈ s.work.sourceBounds, TypeVar.flex n ∉ c.typeVars := by
  have hn := (List.mem_filter.mp hn).1
  split at hn
  all_goals
    have hb := (List.mem_filter.mp hn).2
    simp only [Bool.and_eq_true] at hb
    exact (ComparisonPartial.absentFromBounds_correct n s.work.sourceBounds).mp hb.1

theorem Setup.bare_before_fixed (s : Setup) {n : Nat} (hn : n ∈ s.bare) :
    s.before.type (.flex n) = .var (.flex n) := by
  apply Substitution.type_fresh
  simpa using (List.mem_filter.mp hn).2

theorem Setup.bare_not_names (s : Setup) {n : Nat} (hn : n ∈ s.bare) : n ∉ s.names := by
  intro hm
  have hm := (List.mem_filter.mp hm).2
  simp only [Bool.and_eq_true] at hm
  have ha : n ∉ s.bare := by simpa using hm.2
  exact ha hn

theorem Setup.names_range (s : Setup) {n : Nat} (hn : n ∈ s.names) :
    s.original.firstType ≤ n ∧ n < s.original.nextType := by
  have hr := (List.mem_filter.mp hn).1
  simp only [List.mem_range'] at hr
  obtain ⟨i, hi, he⟩ := hr
  constructor <;> omega

theorem Setup.templates_modes (s : Setup) : s.templates.substitution.modes = [] := by
  have hm (p : SchemePreparation.Prepared) (shape : ComparisonShapeSolver.Solved)
      (names : List Nat) (nt nm : Nat) :
      (ComparisonSkeleton.allocate p shape names nt nm).substitution.modes = [] := by
    induction names generalizing nt nm <;> simp_all [ComparisonSkeleton.allocate]
  exact hm s.work s.shapes s.names s.original.nextType s.annotations.nextMode

theorem Setup.work_typeVars (s : Setup) : s.work.sourceType.typeVars = s.input.sourceType.typeVars := by
  have ha : s.absorption.body.typeVars = s.input.sourceType.typeVars := by
    ext v
    rw [← ComparisonShapeSolver.mem_vars_ofTy, ← ComparisonShapeSolver.mem_vars_ofTy]
    change v ∈ (ComparisonShape.ofTy (ComparisonAbsorption.plan s.input s.total).body).vars ↔ _
    rw [ComparisonAbsorption.plan_shape]
  ext v
  change v ∈ (s.annotations.substitution.ty s.absorption.body).typeVars ↔ _
  rw [Substitution.ty, TypeExpr.mem_typeVars_subst]
  simp only [Setup.annotations, ComparisonAnnotations.prepare_type,
    TypeExpr.typeVars, Finset.mem_singleton, ha]
  simp

theorem Setup.original_types_bounded (s : Setup)
    (ha : s.original.assumptions.Bounded s.original.nextType s.original.nextMode)
    (ht : s.original.targetType.Bounded s.original.nextType s.original.nextMode)
    (hs : s.original.sourceType.Bounded s.original.nextType s.original.nextMode)
    (hb : s.original.sourceBounds.Bounded s.original.nextType s.original.nextMode)
    (hbefore : s.before.Bounded s.original.nextType s.original.nextMode) :
    ∀ v ∈ s.work.assumptions.typeVariables ++ s.work.targetType.typeVariables ++
      s.work.sourceType.typeVariables ++ s.work.sourceBounds.typeVariables, v.index < s.original.nextType := by
  intro v hv
  simp only [List.mem_append, TypeExpr.mem_typeVariables, Bounds.mem_typeVariables] at hv
  rcases hv with ((hv | hv) | hv) | hv
  · exact (Bounds.bounded_iff _ _ _).mp ha |>.1 v hv
  · exact (TypeExpr.bounded_iff _ _ _).mp ht |>.1 v hv
  · rw [s.work_typeVars] at hv
    exact (TypeExpr.bounded_iff _ _ _).mp (hbefore.ty hs) |>.1 v hv
  · exact (Bounds.bounded_iff _ _ _).mp (hbefore.bounds hb) |>.1 v hv

theorem Setup.leaves_fresh (s : Setup)
    (h : ∀ v ∈ s.work.assumptions.typeVariables ++ s.work.targetType.typeVariables ++
      s.work.sourceType.typeVariables ++ s.work.sourceBounds.typeVariables, v.index < s.original.nextType) :
    ∀ leaf ∈ s.templates.leaves,
      ∀ v ∈ s.work.assumptions.typeVariables ++ s.work.targetType.typeVariables ++
        s.work.sourceType.typeVariables ++ s.work.sourceBounds.typeVariables, v ≠ .flex leaf.name := by
  intro leaf hl v hv he
  have hb := h v hv
  have hlo := (ComparisonSkeleton.allocate_leaf_range _ _ _ _ _ leaf hl).1
  subst v
  change leaf.name < s.original.nextType at hb
  omega

theorem Setup.initial_pinned (s : Setup)
    (ht : s.original.targetType.Bounded s.original.firstType s.original.firstMode) :
    ComparisonReduction.PinnedHolds s.bare (fun v => v ∈ s.original.targetType.typeVars)
      (ComparisonReduction.initial (s.templates.substitution.bounds s.work.sourceBounds)
        (s.templates.substitution.ty s.work.sourceType) s.work.targetType) := by
  apply ComparisonReduction.initial_pinnedHolds
  · exact ComparisonReduction.bounds_typeFree_subst (fun _ hn => s.bare_avoids_bounds hn)
      (ComparisonReduction.typeFree_type_of_images
        (ComparisonSkeleton.allocate_images_free s.work s.shapes s.names s.bare
          s.original.nextType s.annotations.nextMode (fun n hn => (s.bare_range hn).2)))
  · intro n hn hv
    have hlo := (s.bare_range hn).1
    have hhi := (TypeExpr.bounded_iff _ _ _).mp ht |>.1 (.flex n) hv
    change n < s.original.firstType at hhi
    omega
  · exact fun _ hv => hv

end ModalityInference.ComparisonChecker
