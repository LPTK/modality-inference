import ModalityInference.Proofs.ComparisonRawHeadSoundness

/-! Whole partial-constructor-head locality for raw endpoints and defined
witnesses under arbitrary ambient bounds. The restricted relation is independent
of the unrestricted comparison relation. -/
namespace ModalityInference.ComparisonRawHeadRestriction

theorem algebra_iff_derivation {Δ H a b} (hc : Covers Δ H)
    (ha : support Δ a none ⊆ H) (hb : support Δ b none ⊆ H)
    (hga : GuardedLattice Δ a) (hgb : GuardedLattice Δ b) :
    AlgebraSubtype Δ a b ↔ Derivation Δ H a b :=
  ⟨fun h => Related.derivation ha hb hga hgb h.wellShaped_left h.wellShaped_right
      (algebra_related hc h), Derivation.algebra⟩

theorem algebra_iff_derivation_defined {Δ H a b} (hc : Covers Δ H)
    (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) :
    AlgebraSubtype Δ a b ↔ Derivation Δ H a b :=
  algebra_iff_derivation hc
    (by rw [support_defined ha]; exact Set.empty_subset _)
    (by rw [support_defined hb]; exact Set.empty_subset _)
    (GuardedLattice.of_defined ha) (GuardedLattice.of_defined hb)

/-- Lattice nodes in the queried endpoints have their original definedness
guards. This includes all public raw types and all admissible finite images. -/
theorem algebra_iff_boundary_derivation (Δ : Bounds) (a b : CompareTy)
    (ha : GuardedLattice Δ a) (hb : GuardedLattice Δ b) :
    AlgebraSubtype Δ a b ↔ Derivation Δ (boundary Δ a b) a b :=
  algebra_iff_derivation (boundary_covers Δ a b) (boundary_left Δ a b)
    (boundary_right Δ a b) ha hb

theorem finite_head_locality (Δ : Bounds) (a b : CompareTy)
    (ha : GuardedLattice Δ a) (hb : GuardedLattice Δ b) :
    ∃ H : Set CompareTy, H.Finite ∧ Covers Δ H ∧
      support Δ a none ⊆ H ∧ support Δ b none ⊆ H ∧
      (AlgebraSubtype Δ a b ↔ Derivation Δ H a b) :=
  ⟨boundary Δ a b, boundary_finite Δ a b, boundary_covers Δ a b,
    boundary_left Δ a b, boundary_right Δ a b, algebra_iff_boundary_derivation Δ a b ha hb⟩

theorem raw_algebra_iff_boundary_derivation (Δ : Bounds) (a b : Ty) :
    AlgebraSubtype Δ (.ofTy a) (.ofTy b) ↔
      Derivation Δ (boundary Δ (.ofTy a) (.ofTy b)) (.ofTy a) (.ofTy b) :=
  algebra_iff_boundary_derivation Δ (.ofTy a) (.ofTy b)
    (GuardedLattice.ofTy Δ a) (GuardedLattice.ofTy Δ b)

/-- A defined source contributes no partial heads, so the chosen head set can
depend solely on the raw context and the target endpoint. -/
theorem defined_raw_algebra_iff_derivation {Δ H a} (b : Ty) (hc : Covers Δ H)
    (ha : a.DefinedUnder Δ) (hb : support Δ (.ofTy b) none ⊆ H) :
    AlgebraSubtype Δ a (.ofTy b) ↔ Derivation Δ H a (.ofTy b) :=
  algebra_iff_derivation hc (by rw [support_defined ha]; exact Set.empty_subset _) hb
    (GuardedLattice.of_defined ha) (GuardedLattice.ofTy Δ b)

end ModalityInference.ComparisonRawHeadRestriction
