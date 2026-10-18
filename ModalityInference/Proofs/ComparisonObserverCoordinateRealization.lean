import ModalityInference.Proofs.ComparisonObserverBoundary
import ModalityInference.Proofs.ComparisonCoordinateTransition

/-! A modality-restricted genuine observer has one coordinate and one scalar
world for every guarded action at once. Constant observers use the unaffected
coordinate; the finite generator theorem handles every other guarded label. -/
namespace ModalityInference.ComparisonObserverCoordinateRealization

open ComparisonAlgebra ComparisonControls ComparisonObserverGluing
  ComparisonObserverActions ComparisonObserverProfiles ComparisonStructuralAlignment
  ComparisonCoordinateTransition ComparisonModeRestriction

noncomputable def labels (Δ : Bounds) (names : Finset ModVar) : List (GuardedMode Δ) :=
  (generators names).attach.map fun m => GuardedMode.ofDefined m.val (generator_defined m.property)

theorem mem_labels {Δ names m} (hm : m ∈ generators names) :
    GuardedMode.ofDefined m (generator_defined hm) ∈ labels Δ names :=
  List.mem_map.mpr ⟨⟨m, hm⟩, List.mem_attach _ _, rfl⟩

theorem action_carrier {Δ} (g : Child Δ) (a : Carrier Δ .unit) {m : ModExpr}
    (hm : Entails Δ (.defined m)) :
    g.transition.apply m (observer g.observer a) = observer g.observer (a.modal m hm) := by
  have h := g.action m hm a.type ⟨a.shaped, a.defined, a.shape_eq⟩
  rw [booleanValue_carrier g.observer a] at h
  exact h.trans (booleanValue_carrier g.observer (a.modal m hm))

theorem supported_realization {Δ : Bounds} (g : Child Δ) (names : Finset ModVar) :
    ∃ c η, (c = Coordinate.unaffected ∨ ModeModels Δ η) ∧
      (c ≠ .unaffected → g.Range false ∧ g.Range true) ∧
      ∀ m, Entails Δ (.defined m) → m.vars ⊆ names → ∀ x, g.Range x →
        g.transition.apply m x = coordinateValue c x (m.complete η) := by
  classical
  by_cases hr : g.Range false ∧ g.Range true
  · obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hr
    obtain ⟨c, η, hη, hg⟩ := observer_global_realizable g.observer a b ha hb (labels Δ names)
    refine ⟨c, η, hη, fun _ => ⟨⟨a, ha⟩, ⟨b, hb⟩⟩, ?_⟩
    have hgen (m : ModExpr) (hm : m ∈ generators names) (x : Bool) (hx : g.Range x) :
        g.transition.apply m x = (transition c η hη).apply m x := by
      obtain ⟨z, rfl⟩ := hx
      rw [action_carrier g z (generator_defined hm)]
      have hh := hg z (GuardedMode.ofDefined m (generator_defined hm)) (mem_labels hm)
      change observer g.observer (z.modal m (generator_defined hm)) =
        coordinateValue c (observer g.observer z)
          ((GuardedMode.ofDefined m (generator_defined hm)).value η) at hh
      rw [hh]
      rcases hη with rfl | hη
      · rfl
      · exact congrArg (coordinateValue c (observer g.observer z))
          (ModExpr.complete_of_eval ((GuardedMode.ofDefined m (generator_defined hm)).eval η hη)).symm
    intro m hm hs x hx
    exact supported_agree_on g.transition (transition c η hη) g.Range
      (fun m hm x hx => ComparisonObserverFiniteMachine.range_action g hm hx) hgen hm hs hx
  · refine ⟨.unaffected, fun _ => Mode.identity, .inl rfl, fun h => False.elim (h rfl), ?_⟩
    intro m hm _ x hx
    have hy := ComparisonObserverFiniteMachine.range_action g hm hx
    change g.transition.apply m x = x
    by_contra he
    cases hx' : x <;> cases hy' : g.transition.apply m x <;> simp_all

def world (names : Finset ModVar) (η : ModVar → Mode) (v : ModVar) : Mode :=
  if v ∈ names then η v else Mode.identity

theorem world_outside (names : Finset ModVar) (η : ModVar → Mode) {v : ModVar}
    (hv : v ∉ names) : world names η v = Mode.identity := by simp [world, hv]

theorem world_models {Δ names} (hs : Δ.modVars ⊆ names) {η : ModVar → Mode}
    (hη : ModeModels Δ η) : ModeModels Δ (world names η) := by
  apply (ModeModels.congr Δ ?_).mpr hη
  intro v hv
  simp [world, hs hv]

theorem complete_world (names : Finset ModVar) (η : ModVar → Mode) (m : ModExpr) :
    (m.subst (restrict names)).complete η = m.complete (world names η) := by
  induction m <;> simp_all [ModExpr.subst, ModExpr.complete, restrict, world, ModExpr.epsilon]
  split <;> rfl

/-- Literal transfer invariance outside the retained names upgrades finite
generator realization to every guarded modality, including residuals. -/
theorem realization {Δ names} (hs : Δ.modVars ⊆ names) (g : Child Δ)
    (hfixed : ∀ m x, g.transition.apply (m.subst (restrict names)) x = g.transition.apply m x) :
    ∃ c η, (∀ v ∉ names, η v = Mode.identity) ∧
      (c = Coordinate.unaffected ∨ ModeModels Δ η) ∧
      (c ≠ .unaffected → g.Range false ∧ g.Range true) ∧
      ∀ m, Entails Δ (.defined m) → ∀ x, g.Range x →
        g.transition.apply m x = coordinateValue c x (m.complete η) := by
  obtain ⟨c, η, hη, hc, ht⟩ := supported_realization g names
  refine ⟨c, world names η, fun _ => world_outside names η,
    hη.imp_right (world_models hs), hc, ?_⟩
  intro m hm x hx
  rw [← hfixed m x, ht _ ((restrict_fixed Δ names hs).defined hm)
    (restrict_support names m) x hx, complete_world]

theorem representative_realization {Δ names} (hs : Δ.modVars ⊆ names)
    {boundary : List CompareTy} {g : Child Δ}
    (hg : g ∈ ComparisonObserverRepresentatives.representatives hs boundary) :
    ∃ c η, (∀ v ∉ names, η v = Mode.identity) ∧
      (c = Coordinate.unaffected ∨ ModeModels Δ η) ∧
      (c ≠ .unaffected → g.Range false ∧ g.Range true) ∧
      ∀ m, Entails Δ (.defined m) → ∀ x, g.Range x →
        g.transition.apply m x = coordinateValue c x (m.complete η) :=
  realization hs g (ComparisonObserverRepresentatives.representatives_transfer_fixed hs hg)

end ModalityInference.ComparisonObserverCoordinateRealization
