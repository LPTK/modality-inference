import ModalityInference.Proofs.ComparisonShapedObserverGluing
import ModalityInference.Proofs.ComparisonOpaqueObserver
import ModalityInference.Proofs.ComparisonObserverProfiles

/-! Concrete coordinate worlds supply all-label guarded transitions for
structural observer extension. Product and sum inheritance shares the world;
constant child action is also permitted. -/
namespace ModalityInference.ComparisonCoordinateTransition

open ComparisonControls ComparisonAlgebra ComparisonObserverActions

theorem coordinate_applyMode (c : Coordinate) (x : Bool) (m : Mode) :
    coordinateValue c x m=ComparisonOpaqueObserver.applyMode c x m := by cases c <;> rfl

def transition {Δ : Bounds} (c : Coordinate) (η : ModVar → Mode)
    (hη : c=.unaffected ∨ ModeModels Δ η) : Transition Δ where
  apply m x := coordinateValue c x (m.complete η)
  monotone m _ := by
    intro a b hab
    apply Bool.le_iff_imp.mpr
    simpa only [coordinate_applyMode] using ComparisonOpaqueObserver.applyMode_mono c
      (Bool.le_iff_imp.mp hab) (Mode.le_refl (m.complete η))
  epsilon x := by
    simp only [coordinate_applyMode,ModExpr.epsilon,ModExpr.complete,
      ComparisonOpaqueObserver.applyMode_identity]
  compose m n _ _ x := by
    simp only [coordinate_applyMode,ModExpr.complete,
      ComparisonOpaqueObserver.applyMode_compose]
  join m n _ _ x := by
    simpa only [coordinate_applyMode,ModExpr.complete,
      ComparisonLattice.Profile.blendMode,ComparisonOpaqueObserver.blend]
      using ComparisonOpaqueObserver.applyMode_scalar c true x (m.complete η) (n.complete η)
  meet m n _ _ x := by
    simpa only [coordinate_applyMode,ModExpr.complete,
      ComparisonLattice.Profile.blendMode,ComparisonOpaqueObserver.blend]
      using ComparisonOpaqueObserver.applyMode_scalar c false x (m.complete η) (n.complete η)
  submode m n hm x := by
    apply Bool.le_iff_imp.mpr
    simpa only [coordinate_applyMode] using
      ComparisonOpaqueObserver.applyMode_submode hη (fun h => h) hm (a := x)

theorem transition_apply {Δ : Bounds} (c : Coordinate) (η : ModVar → Mode)
    (hη : c=.unaffected ∨ ModeModels Δ η) (m : ModExpr) (x : Bool) :
    (transition c η hη).apply m x=coordinateValue c x (m.complete η) := rfl

theorem pair_absorption (parent child : Coordinate) (m : Mode) (x : Bool)
    (h : child=.unaffected ∨ child=parent) :
    coordinateValue parent (coordinateValue child x m) m=coordinateValue parent x m := by
  rcases h with rfl|rfl
  · rfl
  · cases child <;> simp [coordinateValue]

theorem transition_absorption {Δ : Bounds} (parent child : Coordinate)
    (η : ModVar → Mode) (hp : parent=.unaffected ∨ ModeModels Δ η)
    (hc : child=.unaffected ∨ ModeModels Δ η) (hi : child=.unaffected ∨ child=parent)
    (m : ModExpr) (x : Bool) :
    (transition parent η hp).apply m ((transition child η hc).apply m x)=
      (transition parent η hp).apply m x := pair_absorption _ _ _ _ hi

theorem transition_profile {Δ : Bounds} {shape : ComparisonShape}
    (g : ComparisonShapedObserverGluing.Child Δ shape) (c : Coordinate)
    (η : ModVar → Mode) (hη : c=.unaffected ∨ ModeModels Δ η)
    (names : Finset ModVar)
    (hp : ComparisonObserverProfiles.profile g.transition names=
      ComparisonObserverProfiles.profile (transition c η hη) names)
    {m : ModExpr} (hm : Entails Δ (.defined m)) (hs : m.vars⊆names)
    {a : CompareTy} (ha : Representable Δ shape a) :
    booleanValue g.observer (.modal a m)=
      coordinateValue c (booleanValue g.observer a) (m.complete η) := by
  rw [←g.action m hm a ha]
  exact ComparisonObserverProfiles.profile_supported hp hm hs _

theorem generated_agree_on {Δ : Bounds} {names : Finset ModVar}
    (t u : Transition Δ) (range : Bool → Prop)
    (hclosed : ∀m,Entails Δ (.defined m) → ∀x,range x → range (t.apply m x))
    (hg : ∀m∈ComparisonObserverProfiles.generators names,∀x,range x → t.apply m x=u.apply m x)
    {m : ModExpr} (hm : ComparisonObserverProfiles.Generated names m) :
    ∀x,range x → t.apply m x=u.apply m x := by
  induction hm with
  | const m => exact hg _ (ComparisonObserverProfiles.const_mem_generators names m)
  | control q hq => exact hg _ (ComparisonObserverProfiles.control_mem_generators q hq)
  | compose hm hn ih₁ ih₂ =>
    intro x hx
    rw [t.compose _ _ hm.defined hn.defined,u.compose _ _ hm.defined hn.defined,
      ←ih₁ x hx,ih₂ _ (hclosed _ hm.defined x hx)]
  | join hm hn ih₁ ih₂ =>
    intro x hx
    rw [t.join _ _ hm.defined hn.defined,u.join _ _ hm.defined hn.defined,ih₁ x hx,ih₂ x hx]
  | meet hm hn ih₁ ih₂ =>
    intro x hx
    rw [t.meet _ _ hm.defined hn.defined,u.meet _ _ hm.defined hn.defined,ih₁ x hx,ih₂ x hx]

theorem supported_agree_on {Δ : Bounds} {names : Finset ModVar}
    (t u : Transition Δ) (range : Bool → Prop)
    (hclosed : ∀m,Entails Δ (.defined m) → ∀x,range x → range (t.apply m x))
    (hg : ∀m∈ComparisonObserverProfiles.generators names,∀x,range x → t.apply m x=u.apply m x)
    {m : ModExpr} (hm : Entails Δ (.defined m)) (hs : m.vars⊆names) {x} (hx : range x) :
    t.apply m x=u.apply m x := by
  rw [←ComparisonObserverProfiles.Transition.normal_apply t hm x,
    ←ComparisonObserverProfiles.Transition.normal_apply u hm x]
  exact generated_agree_on t u range hclosed hg
    (ComparisonObserverProfiles.normal_generated hs) x hx

theorem range_action {Δ shape} (g : ComparisonShapedObserverGluing.Child Δ shape)
    (m : ModExpr) (hm : Entails Δ (.defined m)) (x : Bool) (hx : g.Range x) :
    g.Range (g.transition.apply m x) := by
  obtain ⟨a,rfl⟩ := hx
  refine ⟨a.modal m hm,?_⟩
  have h := g.action m hm a.type ⟨a.shaped,a.defined,a.shape_eq⟩
  rw [booleanValue_carrier g.observer a] at h
  exact (booleanValue_represented g.observer _
    (ComparisonShapedObserverGluing.representable_modal
      ⟨a.shaped,a.defined,a.shape_eq⟩ hm)).symm.trans h.symm

theorem generator_defined {Δ names m}
    (h : m∈ComparisonObserverProfiles.generators names) : Entails Δ (.defined m) := by
  rcases List.mem_append.mp h with h|h
  · obtain ⟨v,_,rfl⟩ := List.mem_map.mp h
    intro η _;rfl
  · obtain ⟨q,_,rfl⟩ := List.mem_map.mp h
    intro η _;exact ComparisonControls.control_total q η

theorem child_action_of_generators {Δ shape names}
    (g : ComparisonShapedObserverGluing.Child Δ shape) (u : Transition Δ)
    (hg : ∀m (hm : m∈ComparisonObserverProfiles.generators names),∀a : Carrier Δ shape,
      observer g.observer (a.modal m (generator_defined hm))=
        u.apply m (observer g.observer a))
    {m : ModExpr} (hm : Entails Δ (.defined m)) (hs : m.vars⊆names)
    {a : CompareTy} (ha : Representable Δ shape a) :
    booleanValue g.observer (.modal a m)=u.apply m (booleanValue g.observer a) := by
  rw [←g.action m hm a ha]
  apply supported_agree_on g.transition u g.Range (range_action g) _ hm hs (g.range_value ha)
  intro n hn x hx
  obtain ⟨a,rfl⟩ := hx
  have h := g.action n (generator_defined hn) a.type ⟨a.shaped,a.defined,a.shape_eq⟩
  have hh := hg n hn a
  rw [booleanValue_carrier g.observer a] at h
  exact h.trans ((booleanValue_represented g.observer _
    (ComparisonShapedObserverGluing.representable_modal
      ⟨a.shaped,a.defined,a.shape_eq⟩ (generator_defined hn))).trans hh)

end ModalityInference.ComparisonCoordinateTransition
