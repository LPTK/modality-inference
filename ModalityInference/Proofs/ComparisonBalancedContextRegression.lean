import ModalityInference.Proofs.ComparisonBalancedDecision

namespace ModalityInference.ComparisonBalancedContextRegression

open ComparisonBalancedDerivation ComparisonBalancedContext

def bad : ModExpr := .leftResidual .epsilon .bottom

theorem bad_not_defined {Δ : Bounds} (hΔ : ModeModels Δ (fun _ => Mode.identity)) :
    ¬Entails Δ (.defined bad) :=
  fun h => Bool.noConfusion (show false = true from h (fun _ => Mode.identity) hΔ)

theorem partial_not_defined {Δ : Bounds} (hΔ : ModeModels Δ (fun _ => Mode.identity))
    (a : Ty) : ¬(a.modal bad).DefinedUnder Δ :=
  fun h => bad_not_defined hΔ
    (CompareTy.definedUnder_modal_iff.mp ((CompareTy.definedUnder_ofTy _ _).mpr h)).2

def left : Ty := .modal .unit bad
def right : Ty := .modal (.modal .unit .epsilon) bad
def bounds : Bounds := [.sub left right]

theorem scalar_model : ModeModels bounds (fun _ => Mode.identity) := by
  simp [ModeModels, bounds, ModeSatisfies]

theorem balanced : Balanced bounds := by
  intro a b h
  obtain ⟨rfl, rfl⟩ := show a = left ∧ b = right by simpa [bounds] using h
  exact iff_of_false (partial_not_defined scalar_model .unit)
    (partial_not_defined scalar_model (.modal .unit .epsilon))

theorem not_all_defined : ¬bounds.TypeBoundsDefined :=
  fun h => partial_not_defined scalar_model .unit (h left right (List.mem_singleton_self _)).1

theorem distinct : left ≠ right := by decide

theorem pruned : prune bounds = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro c hc
  have he : c = .sub left right := by simpa [bounds] using prune_subset bounds hc
  exact partial_not_defined scalar_model .unit ((sub_mem_prune _ _ _).mp (he ▸ hc)).2.1

theorem shapes (ρ : TypeVar → ComparisonShape) : ComparisonShape.Models bounds ρ := by
  simp [ComparisonShape.Models, bounds, left, right, ComparisonShape.pairs,
    ComparisonShape.ofTy, ComparisonShape.subst]

/-- A non-reflexive partial edge can be removed for every defined comparison,
without assuming its guard or requiring a recursive declared shape. -/
theorem defined_comparison_iff {a b : CompareTy}
    (ha : a.DefinedUnder bounds) (hb : b.DefinedUnder bounds) :
    AlgebraSubtype [] a b ↔ AlgebraSubtype bounds a b := by
  simpa only [pruned] using algebra_prune_iff balanced (fun ρ _ => shapes ρ) ha hb

def mixed : Bounds := [.sub .unit left, .sub left .credit]

theorem mixed_scalar_model : ModeModels mixed (fun _ => Mode.identity) := by
  simp [ModeModels, mixed, ModeSatisfies]

theorem mixed_not_balanced : ¬Balanced mixed := by
  intro h
  exact partial_not_defined mixed_scalar_model .unit
    ((h .unit left (by simp [mixed])).mp (fun _ _ _ hc => False.elim (List.not_mem_nil hc)))

/-- Crossing the partial boundary can establish a comparison between defined
types, so deleting all partial endpoints would be unsound. -/
theorem mixed_comparison : AlgebraSubtype mixed .unit .credit := by
  exact (AlgebraSubtype.shaped (.bound (a := .unit) (b := left) (by simp [mixed]))).trans
    (.shaped (.bound (a := left) (b := .credit) (by simp [mixed])))

theorem mixed_pruned : prune mixed = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro c hc
  have he : c = .sub .unit left ∨ c = .sub left .credit := by
    simpa [mixed] using prune_subset mixed hc
  rcases he with rfl | rfl
  all_goals first
    | exact partial_not_defined mixed_scalar_model .unit ((sub_mem_prune _ _ _).mp hc).2.2
    | exact partial_not_defined mixed_scalar_model .unit ((sub_mem_prune _ _ _).mp hc).2.1

theorem empty_rejects : ¬AlgebraSubtype [] .unit .credit := by
  intro h
  exact ComparisonShape.noConfusion
    (h.shape_equivalent (fun _ => .unit) (by simp [ComparisonShape.Models, ComparisonShape.pairs]))

def shapeBounds : Bounds := [.sub left (.modal .credit bad)]

theorem shape_scalar_model : ModeModels shapeBounds (fun _ => Mode.identity) := by
  simp [ModeModels, shapeBounds, ModeSatisfies]

theorem shape_balanced : Balanced shapeBounds := by
  intro a b h
  obtain ⟨rfl, rfl⟩ := show a = left ∧ b = .modal .credit bad by simpa [shapeBounds] using h
  exact iff_of_false (partial_not_defined shape_scalar_model .unit)
    (partial_not_defined shape_scalar_model .credit)

theorem shape_no_model : ¬ ∃ ρ, ComparisonShape.Models shapeBounds ρ := by
  rintro ⟨ρ, hρ⟩
  exact ComparisonShape.noConfusion (hρ (.unit, .credit)
    (by simp [shapeBounds, left, ComparisonShape.pairs, ComparisonShape.ofTy]))

theorem shape_comparison : AlgebraSubtype shapeBounds .unit (.join .unit .credit) := by
  apply AlgebraSubtype.shaped
  exact .joinLeft ⟨True.intro, True.intro, fun ρ hρ => False.elim (shape_no_model ⟨ρ, hρ⟩)⟩

/-- Shape equations from discarded partial edges remain available to the
actual projected observer query. -/
theorem shape_project_query_valid : ∀ world,
    (ComparisonObserverDecision.query (ComparisonBalancedProjection.project shapeBounds)
      .unit (.join .unit .credit)).eval world = true :=
  (ComparisonBalancedProjection.query_valid shape_balanced shape_no_model
    (fun _ _ _ hc => False.elim (List.not_mem_nil hc))
    (fun _ _ _ hc => False.elim (List.not_mem_nil hc))).mpr shape_comparison

theorem empty_join_rejects : ¬AlgebraSubtype [] .unit (.join .unit .credit) := by
  intro h
  exact ComparisonShape.noConfusion
    (h.shape_invariant.2.1.2.2 (fun _ => .unit)
      (by simp [ComparisonShape.Models, ComparisonShape.pairs]))

end ModalityInference.ComparisonBalancedContextRegression
