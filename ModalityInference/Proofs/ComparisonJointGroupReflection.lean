import ModalityInference.Proofs.ComparisonTupleReflection
import ModalityInference.Proofs.ComparisonJointGroup

/-! Reflect the original coordinated group obligations into algebraic subtyping
for one common family of generated type images. -/
namespace ModalityInference.ComparisonJointGroup

open ComparisonAlgebra ComparisonControls ComparisonTupleReification

theorem generated_sound {Δ assumptions required : Bounds} {shape : ComparisonShape}
    {b : Basis} {g : ComparisonGroups.Group}
    (generated : ComparisonGroups.Atom → ComparisonControls.Generated b)
    (parameters : (CompareTy → Bool) → (ModVar → Mode) → Nat → Bool)
    (values : (CompareTy → Bool) → (ModVar → Mode) → Fin (4 * g.leaves.length) → Bool)
    (hh : ∀ t ∈ b.heads, Representable Δ shape t)
    (hd : ∀ pair ∈ g.assumptions ++ g.goals,
      (generated pair.1).term.DefinedUnder Δ ∧ (generated pair.2).term.DefinedUnder Δ)
    (ha : ∀ pair ∈ g.assumptions,
      AlgebraSubtype Δ (generated pair.1).term (generated pair.2).term)
    (hgroup : ∀ heads η, GroupHolds assumptions required g (parameters heads η) (values heads η))
    (hguards : ∀ heads η coordinate, (coordinate = Coordinate.unaffected ∨ ModeModels Δ η) →
      coordinate = .unaffected ∨
        (guards assumptions required).eval (modes g.heads.length (parameters heads η)) = true)
    (hfixed : ∀ heads η coordinate, (coordinate = Coordinate.unaffected ∨ ModeModels Δ η) →
      ∀ pair ∈ g.assumptions,
        observe coordinate heads η (generated pair.1) = fixedValue g.heads coordinate (parameters heads η) pair.1 ∧
        observe coordinate heads η (generated pair.2) = fixedValue g.heads coordinate (parameters heads η) pair.2)
    (hgoals : ∀ heads η coordinate, (coordinate = Coordinate.unaffected ∨ ModeModels Δ η) →
      ∀ pair ∈ g.goals,
        observe coordinate heads η (generated pair.1) =
          atomValue g.heads g.leaves coordinate (parameters heads η) (values heads η) pair.1 ∧
        observe coordinate heads η (generated pair.2) =
          atomValue g.heads g.leaves coordinate (parameters heads η) (values heads η) pair.2) :
    ∀ pair ∈ g.goals, AlgebraSubtype Δ (generated pair.1).term (generated pair.2).term := by
  intro pair hp
  let premises := g.assumptions.map fun p => (generated p.1, generated p.2)
  have hdp := hd pair (List.mem_append_right _ hp)
  apply ComparisonTupleReflection.subtype_of_coordinates
    (generated pair.1) (generated pair.2) premises hh hdp.1 hdp.2
  · intro p hp'
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hp'
    have hdo := hd original (List.mem_append_left _ ho)
    exact ⟨hdo.1, hdo.2, ha original ho⟩
  · intro coordinate η heads hη hbase hleft
    have htheory : TheoryHolds assumptions required g coordinate (parameters heads η) := by
      refine ⟨?_, hguards heads η coordinate hη⟩
      intro original ho hleft
      have he := hfixed heads η coordinate hη original ho
      have hm : (generated original.1, generated original.2) ∈ premises :=
        List.mem_map.mpr ⟨original, ho, rfl⟩
      rw [← he.2]
      exact hbase _ hm (he.1.trans hleft)
    have he := hgoals heads η coordinate hη pair hp
    rw [he.1] at hleft
    rw [he.2]
    exact (hgroup heads η).1 coordinate htheory pair hp hleft

end ModalityInference.ComparisonJointGroup
