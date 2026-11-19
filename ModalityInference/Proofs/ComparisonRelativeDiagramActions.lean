import ModalityInference.Proofs.ComparisonRelativeCoordinates

/-! Total actions on an optional-cut diagram preserve mixed comparisons exactly
when they transport the existing lower and upper shadows in the proper
directions. Their coordinate orbits then reflect the original mixed order. -/
namespace ModalityInference.ComparisonRelativeDiagramActions

open ComparisonRelativeIntervals ComparisonRelativeCoordinates

section Action

variable {D P : Type*} [Lattice D] [Preorder P]

structure Action (I : IntervalData D P) where
  defined : D →o D
  boundary : P →o P
  lower_shadow : ∀ {p a}, I.lower p = some a →
    ∃ b, I.lower (boundary p) = some b ∧ defined a ≤ b
  upper_shadow : ∀ {p b}, I.upper p = some b →
    ∃ a, I.upper (boundary p) = some a ∧ a ≤ defined b

namespace Action

variable {I : IntervalData D P} (s : Action I)

def map : D ⊕ P → D ⊕ P
  | .inl a => .inl (s.defined a)
  | .inr p => .inr (s.boundary p)

theorem rel_mono {x y : D ⊕ P} (h : I.Rel x y) : I.Rel (s.map x) (s.map y) := by
  cases x <;> cases y
  case inl.inl => exact s.defined.monotone h
  case inr.inr => exact s.boundary.monotone h
  case inl.inr a p =>
    obtain ⟨b,hb,hab⟩ := h
    obtain ⟨c,hc,hbc⟩ := s.lower_shadow hb
    exact ⟨c,hc,(s.defined.monotone hab).trans hbc⟩
  case inr.inl p b =>
    obtain ⟨a,ha,hab⟩ := h
    obtain ⟨c,hc,hca⟩ := s.upper_shadow ha
    exact ⟨c,hc,hca.trans (s.defined.monotone hab)⟩

end Action
end Action

section Orbits

variable {D P M : Type*} [DistribLattice D] [Preorder P] [Preorder M]
  {I : IntervalData D P} (act : M → Action I)
  (hd : ∀ a, Monotone (fun m => (act m).defined a))
  (hp : ∀ p, Monotone (fun m => (act m).boundary p))

include hd hp

theorem index_mono (x : D ⊕ P) : Monotone (fun m => I.embed ((act m).map x)) := by
  intro m n hmn
  apply (I.embed_le_iff _ _).mpr
  cases x with
  | inl a => exact hd a hmn
  | inr p => exact hp p hmn

def diagramOrbit (x : D ⊕ P) : Coordinates M I.Completion :=
  orbit I.embed (fun m => (act m).map) (index_mono act hd hp) x

@[simp] theorem diagramOrbit_apply (x : D ⊕ P) (m : M) :
    diagramOrbit act hd hp x m = I.embed ((act m).map x) := rfl

/-- A pinned interface anchor has the same entire orbit as its defined value. -/
theorem diagramOrbit_anchor {p : P} {a : D}
    (hl : I.lower p = some a) (hu : I.upper p = some a) :
    diagramOrbit act hd hp (.inr p) = diagramOrbit act hd hp (.inl a) := by
  apply le_antisymm
  · intro m
    exact (I.embed_le_iff _ _).mpr ((act m).rel_mono
      (show I.Rel (.inr p) (.inl a) from ⟨a,hu,le_rfl⟩))
  · intro m
    exact (I.embed_le_iff _ _).mpr ((act m).rel_mono
      (show I.Rel (.inl a) (.inr p) from ⟨a,hl,le_rfl⟩))

/-- Unit laws need only hold up to the diagram's preorder, allowing interface
anchors with equal semantic values to remain distinct tags. -/
theorem diagramOrbit_le_iff [One M]
    (hunit : ∀ x, I.Rel ((act 1).map x) x ∧ I.Rel x ((act 1).map x))
    (x y : D ⊕ P) : diagramOrbit act hd hp x ≤ diagramOrbit act hd hp y ↔ I.Rel x y := by
  have hu : ∀ x, I.embed ((act 1).map x) = I.embed x := fun x =>
    le_antisymm ((I.embed_le_iff _ _).mpr (hunit x).1) ((I.embed_le_iff _ _).mpr (hunit x).2)
  have ht : ∀ m x y, I.embed x ≤ I.embed y → I.embed ((act m).map x) ≤ I.embed ((act m).map y) := by
    intro m x y hxy
    exact (I.embed_le_iff _ _).mpr ((act m).rel_mono ((I.embed_le_iff _ _).mp hxy))
  exact (orbit_le_iff I.embed (fun m => (act m).map) (index_mono act hd hp) hu ht x y).trans
    (I.embed_le_iff x y)

end Orbits

section Composition

variable {D P M : Type*} [DistribLattice D] [Preorder P]
  [PartialOrder M] [CommMonoid M] {I : IntervalData D P}
  (hmul : ∀ a : M, Monotone (a * ·)) (act : M → Action I)
  (hd : ∀ a, Monotone (fun m => (act m).defined a))
  (hp : ∀ p, Monotone (fun m => (act m).boundary p))

theorem shift_diagramOrbit
    (hact : ∀ m n x,
      I.Rel ((act m).map ((act n).map x)) ((act (n * m)).map x) ∧
      I.Rel ((act (n * m)).map x) ((act m).map ((act n).map x)))
    (n : M) (x : D ⊕ P) :
    shift hmul n (diagramOrbit act hd hp x) = diagramOrbit act hd hp ((act n).map x) := by
  apply shift_orbit hmul I.embed (fun m => (act m).map) (index_mono act hd hp)
  intro m n x
  exact le_antisymm ((I.embed_le_iff _ _).mpr (hact m n x).1)
    ((I.embed_le_iff _ _).mpr (hact m n x).2)

end Composition
end ModalityInference.ComparisonRelativeDiagramActions
