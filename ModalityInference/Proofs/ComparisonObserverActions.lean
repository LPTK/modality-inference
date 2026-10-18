import ModalityInference.Proofs.ComparisonStructuralObservers

/-! A Boolean lattice observer carries one coherent Boolean action for every
guarded modality. The construction handles constant observers without assuming
that the scalar context has a model. -/

namespace ModalityInference.ComparisonObserverActions

open ComparisonAlgebra ComparisonStructuralObservers

/-- The action induced on the two fibers of a Boolean lattice observer. -/
structure Transition (Δ : Bounds) where
  apply : ModExpr → Bool → Bool
  monotone : ∀ m, Entails Δ (.defined m) → Monotone (apply m)
  epsilon : ∀ x, apply .epsilon x = x
  compose : ∀ m n, Entails Δ (.defined m) → Entails Δ (.defined n) → ∀ x,
    apply (.compose m n) x = apply n (apply m x)
  join : ∀ m n, Entails Δ (.defined m) → Entails Δ (.defined n) → ∀ x,
    apply (.join m n) x = (apply m x || apply n x)
  meet : ∀ m n, Entails Δ (.defined m) → Entails Δ (.defined n) → ∀ x,
    apply (.meet m n) x = (apply m x && apply n x)
  submode : ∀ m n, Submode Δ m n → ∀ x, apply m x ≤ apply n x

def Transition.identity (Δ : Bounds) : Transition Δ where
  apply _ x := x
  monotone _ _ := monotone_id
  epsilon _ := rfl
  compose _ _ _ _ _ := rfl
  join _ _ _ _ _ := (Bool.or_self _).symm
  meet _ _ _ _ _ := (Bool.and_self _).symm
  submode _ _ _ _ := le_rfl

private theorem monotone_or (g : Bool → Bool) (hg : Monotone g) (a b : Bool) :
    g (a || b) = (g a || g b) := by
  have hle := hg (show false ≤ true from by decide)
  cases a <;> cases b <;> cases h₀ : g false <;> cases h₁ : g true <;>
    simp_all [Bool.le_iff_imp]

private theorem monotone_and (g : Bool → Bool) (hg : Monotone g) (a b : Bool) :
    g (a && b) = (g a && g b) := by
  have hle := hg (show false ≤ true from by decide)
  cases a <;> cases b <;> cases h₀ : g false <;> cases h₁ : g true <;>
    simp_all [Bool.le_iff_imp]

private theorem monotone_clamp (g : Bool → Bool) (hg : Monotone g)
    {b a t : Bool} (hba : b ≤ a) (hat : a ≤ t) :
    g a = ((a || g b) && g t) := by
  have hle := hg (show false ≤ true from by decide)
  cases a <;> cases b <;> cases t <;> cases h₀ : g false <;> cases h₁ : g true <;>
    simp_all [Bool.le_iff_imp]

theorem Transition.modal_join {Δ} (t : Transition Δ) {m}
    (hm : Entails Δ (.defined m)) (a b : Bool) :
    t.apply m (a || b) = (t.apply m a || t.apply m b) :=
  monotone_or _ (t.monotone m hm) a b

theorem Transition.modal_meet {Δ} (t : Transition Δ) {m}
    (hm : Entails Δ (.defined m)) (a b : Bool) :
    t.apply m (a && b) = (t.apply m a && t.apply m b) :=
  monotone_and _ (t.monotone m hm) a b

theorem Transition.clamp {Δ} (t : Transition Δ) {m}
    (hm : Entails Δ (.defined m)) {b a u : Bool} (hba : b ≤ a) (hau : a ≤ u) :
    t.apply m a = ((a || t.apply m b) && t.apply m u) :=
  monotone_clamp _ (t.monotone m hm) hba hau

noncomputable section
attribute [local instance] Classical.propDecidable

noncomputable def fiberAction {Δ shape} (f : LatticeHom (Order Δ shape) Bool)
    (pick : Bool → Carrier Δ shape) (m : ModExpr) (x : Bool) : Bool :=
  if hm : Entails Δ (.defined m) then observer f ((pick x).modal m hm) else x

theorem fiberAction_value {Δ shape} (f : LatticeHom (Order Δ shape) Bool)
    (pick : Bool → Carrier Δ shape) (m : ModExpr) (hm : Entails Δ (.defined m)) (x : Bool) :
    fiberAction f pick m x = observer f ((pick x).modal m hm) := by
  simp [fiberAction, hm]

theorem fiberAction_observer {Δ shape} (f : LatticeHom (Order Δ shape) Bool)
    (pick : Bool → Carrier Δ shape) (hp : ∀ x, observer f (pick x) = x)
    (m : ModExpr) (hm : Entails Δ (.defined m)) (a : Carrier Δ shape) :
    fiberAction f pick m (observer f a) = observer f (a.modal m hm) := by
  rw [fiberAction_value f pick m hm]
  exact observer_modal_congr f (.ofDefined m hm) _ _ (hp _)

theorem fiberAction_monotone {Δ shape} (f : LatticeHom (Order Δ shape) Bool)
    (pick : Bool → Carrier Δ shape) (hp : ∀ x, observer f (pick x) = x)
    (m : ModExpr) (hm : Entails Δ (.defined m)) : Monotone (fiberAction f pick m) := by
  have h₀ : observer f ((pick false).meet (pick true)) = false := by
    simp [observer_meet, hp]
  have h₁ : observer f ((pick false).join (pick true)) = true := by
    simp [observer_join, hp]
  have he₀ := fiberAction_observer f pick hp m hm ((pick false).meet (pick true))
  have he₁ := fiberAction_observer f pick hp m hm ((pick false).join (pick true))
  rw [h₀] at he₀
  rw [h₁] at he₁
  have hle : fiberAction f pick m false ≤ fiberAction f pick m true := by
    rw [he₀, he₁]
    exact observer_mono f (.congr ((Carrier.meet_le_left _ _).trans
      (Carrier.le_join_left _ _)) (.refl hm))
  intro x y hxy
  cases x <;> cases y <;> simp_all [Bool.le_iff_imp]

theorem fiberAction_epsilon {Δ shape} (f : LatticeHom (Order Δ shape) Bool)
    (pick : Bool → Carrier Δ shape) (hp : ∀ x, observer f (pick x) = x) (x : Bool) :
    fiberAction f pick .epsilon x = x := by
  have he : Entails Δ (.defined .epsilon) := by intro η _; rfl
  rw [fiberAction_value f pick .epsilon he]
  exact (congrArg f (Quotient.sound ⟨AlgebraSubtype.identity (pick x).shaped,
    AlgebraSubtype.identityRev (pick x).shaped⟩)).trans (hp x)

theorem fiberAction_compose {Δ shape} (f : LatticeHom (Order Δ shape) Bool)
    (pick : Bool → Carrier Δ shape) (hp : ∀ x, observer f (pick x) = x)
    (m n : ModExpr) (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n)) (x : Bool) :
    fiberAction f pick (.compose m n) x = fiberAction f pick n (fiberAction f pick m x) := by
  rw [fiberAction_value f pick (.compose m n) (Entails.defined_compose_iff.mpr ⟨hm, hn⟩),
    fiberAction_value f pick m hm, fiberAction_observer f pick hp n hn]
  exact congrArg f (Quotient.sound ⟨AlgebraSubtype.composeRev (pick x).shaped,
    AlgebraSubtype.compose (pick x).shaped⟩)

theorem fiberAction_join {Δ shape} (f : LatticeHom (Order Δ shape) Bool)
    (pick : Bool → Carrier Δ shape)
    (m n : ModExpr) (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n)) (x : Bool) :
    fiberAction f pick (.join m n) x = (fiberAction f pick m x || fiberAction f pick n x) := by
  have hmn := ComparisonDefinedCovers.modeOp_defined true hm hn
  change Entails Δ (.defined (.join m n)) at hmn
  rw [fiberAction_value f pick (.join m n) hmn, fiberAction_value f pick m hm,
    fiberAction_value f pick n hn]
  have he : Order.of ((pick x).modal (.join m n) hmn) =
      Order.of (((pick x).modal m hm).join ((pick x).modal n hn)) :=
    Quotient.sound ⟨.equation (.scalar true (pick x).shaped (pick x).defined hm hn),
      .equationRev (.scalar true (pick x).shaped (pick x).defined hm hn)⟩
  exact (congrArg f he).trans (observer_join f _ _)

theorem fiberAction_meet {Δ shape} (f : LatticeHom (Order Δ shape) Bool)
    (pick : Bool → Carrier Δ shape)
    (m n : ModExpr) (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n)) (x : Bool) :
    fiberAction f pick (.meet m n) x = (fiberAction f pick m x && fiberAction f pick n x) := by
  have hmn := ComparisonDefinedCovers.modeOp_defined false hm hn
  change Entails Δ (.defined (.meet m n)) at hmn
  rw [fiberAction_value f pick (.meet m n) hmn, fiberAction_value f pick m hm,
    fiberAction_value f pick n hn]
  have he : Order.of ((pick x).modal (.meet m n) hmn) =
      Order.of (((pick x).modal m hm).meet ((pick x).modal n hn)) :=
    Quotient.sound ⟨.equation (.scalar false (pick x).shaped (pick x).defined hm hn),
      .equationRev (.scalar false (pick x).shaped (pick x).defined hm hn)⟩
  exact (congrArg f he).trans (observer_meet f _ _)

theorem fiberAction_submode {Δ shape} (f : LatticeHom (Order Δ shape) Bool)
    (pick : Bool → Carrier Δ shape) (m n : ModExpr) (h : Submode Δ m n) (x : Bool) :
    fiberAction f pick m x ≤ fiberAction f pick n x := by
  rw [fiberAction_value f pick m h.defined.1, fiberAction_value f pick n h.defined.2]
  exact observer_mono f (.congr (.refl (pick x).shaped) h)

noncomputable def fiberTransition {Δ shape} (f : LatticeHom (Order Δ shape) Bool)
    (pick : Bool → Carrier Δ shape) (hp : ∀ x, observer f (pick x) = x) : Transition Δ where
  apply := fiberAction f pick
  monotone := fiberAction_monotone f pick hp
  epsilon := fiberAction_epsilon f pick hp
  compose := fiberAction_compose f pick hp
  join := fiberAction_join f pick
  meet := fiberAction_meet f pick
  submode := fiberAction_submode f pick

/-- Every Boolean observer has one action on its fibers, simultaneously for
all modalities whose guards are established by the context. -/
theorem observer_transition {Δ shape} (f : LatticeHom (Order Δ shape) Bool)
    (a₀ : Carrier Δ shape) :
    ∃ t : Transition Δ, ∀ m (hm : Entails Δ (.defined m)) a,
      t.apply m (observer f a) = observer f (a.modal m hm) := by
  by_cases hv : ∃ a b, observer f a = false ∧ observer f b = true
  · obtain ⟨a, b, ha, hb⟩ := hv
    let pick : Bool → Carrier Δ shape := fun x => if x then b else a
    have hp : ∀ x, observer f (pick x) = x := by intro x; cases x <;> assumption
    exact ⟨fiberTransition f pick hp, fiberAction_observer f pick hp⟩
  · have hc (a : Carrier Δ shape) : observer f a = observer f a₀ := by
      by_contra h
      cases ea : observer f a <;> cases e₀ : observer f a₀
      · exact h (ea.trans e₀.symm)
      · exact hv ⟨a, a₀, ea, e₀⟩
      · exact hv ⟨a₀, a, e₀, ea⟩
      · exact h (ea.trans e₀.symm)
    exact ⟨Transition.identity Δ, fun m hm a => (hc a).trans (hc (a.modal m hm)).symm⟩

end
end ModalityInference.ComparisonObserverActions
