import ModalityInference.Proofs.ComparisonStructuralAlignment

/-! Product and sum profiles use the same scalar world as their parent.
Alignment preserves every supported residual projection, while the parent's
mode model retains the original guards. Constant profiles keep their range. -/
namespace ModalityInference.ComparisonStructuralAlignment

open ComparisonControls ComparisonAlgebra

theorem coordinateValue_congr_neutral {coordinate : Coordinate} {left right : Mode}
    (h : neutral coordinate left = neutral coordinate right) (value : Bool) :
    coordinateValue coordinate value left = coordinateValue coordinate value right := by
  cases coordinate <;> simp_all [neutral, coordinateValue]

theorem Model.rebase {Δ : Bounds} {shape : ComparisonShape}
    {f : LatticeHom (Order Δ shape) Bool} {labels : List (GuardedMode Δ)}
    {names : List ModVar} {parent child : Coordinate} {η θ : ModVar → Mode}
    (hmodel : Model f labels child θ)
    (hparent : parent = .unaffected ∨ ModeModels Δ η)
    (halign : Aligned names parent child (encodeModes η) (encodeModes θ))
    (hsupport : ∀m∈labels, ∀v∈m.expression.freeVariables, v∈names) :
    Model f labels child η := by
  by_cases hc : child = .unaffected
  · subst child
    exact ⟨.inl rfl, hmodel.action⟩
  · obtain ⟨rfl, he⟩ := halign.resolve_left hc
    have hη := hparent.resolve_left hc
    have hθ := hmodel.modeModel.resolve_left hc
    refine ⟨.inr hη, ?_⟩
    intro x m hm
    refine (hmodel.action x m hm).trans ?_
    apply coordinateValue_congr_neutral
    have hbits := he.neutralFormula (hsupport m hm)
    rw [neutralFormula_of_eval (m.eval η hη), neutralFormula_of_eval (m.eval θ hθ)] at hbits
    exact hbits.symm

theorem aligned_same_world {names parent child σ} :
    Aligned names parent child σ σ ↔ child = .unaffected ∨ child = parent := by
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact .inl h
    · exact .inr h
  · rintro (h | rfl)
    · exact .inl h
    · refine .inr ⟨rfl, ?_⟩
      cases child <;> simp [SameInputs]

theorem transition_same_world {parent child parentAtom childAtom names} {σ world : Nat → Bool}
    (hp : ∀i, world (parentAtom i) = σ i) (hc : ∀i, world (childAtom i) = σ i) :
    (transition parent child parentAtom childAtom names).eval world = true ↔
      child = .unaffected ∨ child = parent :=
  (transition_correct hp hc).trans aligned_same_world

def SharedProfile {Δ : Bounds} {shape : ComparisonShape}
    (f : LatticeHom (Order Δ shape) Bool) (labels : List (GuardedMode Δ))
    (parent : Coordinate) (η : ModVar → Mode) : Prop :=
  (∃value, ∀x, observer f x = value) ∨
    ∃child, Model f labels child η ∧ (child = .unaffected ∨ child = parent) ∧
      ∃a b, observer f a = false ∧ observer f b = true

theorem Profile.shared {Δ : Bounds} {shape : ComparisonShape}
    {f : LatticeHom (Order Δ shape) Bool} {labels : List (GuardedMode Δ)}
    {names : List ModVar} {parent : Coordinate} {η : ModVar → Mode}
    (h : Profile f labels names parent η)
    (hparent : parent = .unaffected ∨ ModeModels Δ η)
    (hsupport : ∀m∈labels, ∀v∈m.expression.freeVariables, v∈names) :
    SharedProfile f labels parent η := by
  rcases h with hconstant | ⟨child, θ, hmodel, halign, hnonconstant⟩
  · exact .inl hconstant
  · refine .inr ⟨child, hmodel.rebase hparent halign hsupport, ?_, hnonconstant⟩
    exact halign.imp_right And.left

open ComparisonStructuralObservers ComparisonStructuralLattice

theorem pair_shared_profile {Δ : Bounds} {s t : ComparisonShape} (isSum : Bool)
    (f : LatticeHom (Order Δ ((if isSum then Kind.sum else Kind.prod).shape s t)) Bool)
    (a₀ : Carrier Δ s) (b₀ : Carrier Δ t)
    {labels : List (GuardedMode Δ)} {names : List ModVar}
    {parent : Coordinate} {η : ModVar → Mode}
    (hparent : Model f labels parent η)
    (htests : ∀m∈tests names, ∃n∈labels, n.expression = m)
    (hsupport : ∀m∈labels, ∀v∈m.expression.freeVariables, v∈names) :
    let k := if isSum then Kind.sum else Kind.prod
    ((∀a b, observer f (opCarrier k a b) = observer (leftObserver k f b₀) a) ∧
      SharedProfile (leftObserver k f b₀) labels parent η) ∨
    ((∀a b, observer f (opCarrier k a b) = observer (rightObserver k f a₀) b) ∧
      SharedProfile (rightObserver k f a₀) labels parent η) := by
  rcases pair_profile_realizable isSum f a₀ b₀ hparent htests with hl | hr
  · exact .inl ⟨hl.1, hl.2.shared hparent.modeModel hsupport⟩
  · exact .inr ⟨hr.1, hr.2.shared hparent.modeModel hsupport⟩

end ModalityInference.ComparisonStructuralAlignment
