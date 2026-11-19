import ModalityInference.Proofs.ComparisonRawHeadBoundary
import ModalityInference.Proofs.ComparisonRawHeadReflection
import ModalityInference.Proofs.ComparisonRawHeadStructural

/-! Soundness of the comparison rules in the whole-head ideal model. -/
namespace ModalityInference.ComparisonRawHeadRestriction

theorem Related.bound {Δ H a b} (hc : Covers Δ H) (h : Constraint.sub a b ∈ Δ) :
    Related Δ H (.ofTy a) (.ofTy b) :=
  .of_derivation (hc a b h).1 (hc a b h).2 (GuardedLattice.ofTy Δ a) (GuardedLattice.ofTy Δ b)
    (.atom (carrier_of_support (suffix := none) (GuardedLattice.ofTy Δ a) (hc a b h).1)
      (carrier_of_support (suffix := none) (GuardedLattice.ofTy Δ b) (hc a b h).2) (.bound h))

theorem Related.equation {Δ H a b} (h : ComparisonAlgebra.Equation Δ a b) :
    Related Δ H a b :=
  .of_derivation_defined (ComparisonDefinedCovers.equation_defined h).1
    (ComparisonDefinedCovers.equation_defined h).2
    (.atom (carrier_defined (ComparisonDefinedCovers.equation_defined h).1)
      (carrier_defined (ComparisonDefinedCovers.equation_defined h).2) (.equation h))

theorem Related.equationRev {Δ H a b} (h : ComparisonAlgebra.Equation Δ a b) :
    Related Δ H b a :=
  .of_derivation_defined (ComparisonDefinedCovers.equation_defined h).2
    (ComparisonDefinedCovers.equation_defined h).1
    (.atom (carrier_defined (ComparisonDefinedCovers.equation_defined h).2)
      (carrier_defined (ComparisonDefinedCovers.equation_defined h).1) (.equationRev h))

theorem Related.clamp {Δ H b a t m}
    (hba : ComparisonAlgebra.Compatible Δ b a)
    (hat : ComparisonAlgebra.Compatible Δ a t) (hm : ComparisonAlgebra.DefinedMode Δ m)
    (h₁ : Related Δ H b a) (h₂ : Related Δ H a t) :
    Related Δ H (.modal a m) (.meet (.join a (.modal b m)) (.modal t m)) :=
  .of_derivation_defined (CompareTy.definedUnder_modal_iff.mpr ⟨hba.2.2,hm⟩)
    (CompareTy.definedUnder_meet_iff.mpr
      ⟨CompareTy.definedUnder_join_iff.mpr
        ⟨hba.2.2,CompareTy.definedUnder_modal_iff.mpr ⟨hba.2.1,hm⟩⟩,
        CompareTy.definedUnder_modal_iff.mpr ⟨hat.2.2,hm⟩⟩)
    (.clamp hba hat hm
      (Related.derivation_defined hba.2.1 hba.2.2 hba.1.1 hba.1.2.1 h₁)
      (Related.derivation_defined hat.2.1 hat.2.2 hat.1.1 hat.1.2.1 h₂))

theorem Related.clampRev {Δ H b a t m}
    (hba : ComparisonAlgebra.Compatible Δ b a)
    (hat : ComparisonAlgebra.Compatible Δ a t) (hm : ComparisonAlgebra.DefinedMode Δ m)
    (h₁ : Related Δ H b a) (h₂ : Related Δ H a t) :
    Related Δ H (.meet (.join a (.modal b m)) (.modal t m)) (.modal a m) :=
  .of_derivation_defined
    (CompareTy.definedUnder_meet_iff.mpr
      ⟨CompareTy.definedUnder_join_iff.mpr
        ⟨hba.2.2,CompareTy.definedUnder_modal_iff.mpr ⟨hba.2.1,hm⟩⟩,
        CompareTy.definedUnder_modal_iff.mpr ⟨hat.2.2,hm⟩⟩)
    (CompareTy.definedUnder_modal_iff.mpr ⟨hba.2.2,hm⟩)
    (.clampRev hba hat hm
      (Related.derivation_defined hba.2.1 hba.2.2 hba.1.1 hba.1.2.1 h₁)
      (Related.derivation_defined hat.2.1 hat.2.2 hat.1.1 hat.1.2.1 h₂))

theorem shaped_related {Δ H a b} (hc : Covers Δ H) (h : ShapedSubtype Δ a b) :
    Related Δ H a b := by
  induction h with
  | refl _ => exact .refl
  | trans _ _ ha hb => exact ha.trans hb
  | bound h => exact .bound hc h
  | identity _ => exact .identity
  | identityRev _ => exact .identityRev
  | compose _ => exact .compose
  | composeRev _ => exact .composeRev
  | congr _ hm ih => exact ih.congr hm
  | prod _ _ ha hb => exact ha.prod hb
  | sum _ _ ha hb => exact ha.sum hb
  | fn _ _ hm ha hb => exact ha.fn hb hm
  | joinLeft _ => exact .joinLeft
  | joinRight _ => exact .joinRight
  | meetLeft _ => exact .meetLeft
  | meetRight _ => exact .meetRight
  | joinLeast _ _ ha hb => exact ha.joinLeast hb
  | meetGreatest _ _ ha hb => exact ha.meetGreatest hb

theorem algebra_related {Δ H a b} (hc : Covers Δ H) (h : AlgebraSubtype Δ a b) :
    Related Δ H a b := by
  induction h with
  | shaped h => exact shaped_related hc h
  | trans _ _ ha hb => exact ha.trans hb
  | equation h => exact .equation h
  | equationRev h => exact .equationRev h
  | congr _ hm ih => exact ih.congr hm
  | prod _ _ ha hb => exact ha.prod hb
  | sum _ _ ha hb => exact ha.sum hb
  | fn _ _ hm ha hb => exact ha.fn hb hm
  | joinLeast _ _ ha hb => exact ha.joinLeast hb
  | meetGreatest _ _ ha hb => exact ha.meetGreatest hb
  | clamp hab hat hm _ _ hb ht => exact .clamp hab hat hm hb ht
  | clampRev hab hat hm _ _ hb ht => exact .clampRev hab hat hm hb ht

end ModalityInference.ComparisonRawHeadRestriction
