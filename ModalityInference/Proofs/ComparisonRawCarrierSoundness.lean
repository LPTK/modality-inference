import ModalityInference.Proofs.ComparisonRawCarrierLattice
import ModalityInference.Proofs.ComparisonRawCarrierInterpretationPartial

/-! Capsule locality for arbitrary mixed raw subtype bounds. The ideal model
is sound for the unchanged comparison algebra, and comparison of supported
endpoints reflects into the independently defined supported subcalculus. -/
namespace ModalityInference.ComparisonRawCarrierRestriction

noncomputable section
attribute [local instance] Classical.propDecidable

theorem Related.prod {Δ K a b c d m}
    (hac : Related Δ K (.modal a m) (.modal c m))
    (hbd : Related Δ K (.modal b m) (.modal d m)) :
    Related Δ K (.modal (.prod a b) m) (.modal (.prod c d) m) :=
  if hm : Entails Δ (.defined m) then .prod_total hm hac hbd else .prod_partial hm hac hbd

theorem Related.sum {Δ K a b c d m}
    (hac : Related Δ K (.modal a m) (.modal c m))
    (hbd : Related Δ K (.modal b m) (.modal d m)) :
    Related Δ K (.modal (.sum a b) m) (.modal (.sum c d) m) :=
  if hm : Entails Δ (.defined m) then .sum_total hm hac hbd else .sum_partial hm hac hbd

theorem shaped_related {Δ K a b} (hc : Covers Δ K) (h : ShapedSubtype Δ a b) :
    Related Δ K a b := by
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

theorem algebra_related {Δ K a b} (hc : Covers Δ K) (h : AlgebraSubtype Δ a b) :
    Related Δ K a b := by
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
  | clamp hab hat hm _ _ hb ht => exact hb.clamp hab hat hm ht
  | clampRev hab hat hm _ _ hb ht => exact hb.clampRev hab hat hm ht

/-- Exact reflection into the capsule-supported calculus under raw bounds.
No annotation-definedness assumption is imposed on declared subtype edges. -/
theorem algebra_iff_derivation {Δ K a b} (hc : Covers Δ K)
    (ha : Carrier Δ K a) (hb : Carrier Δ K b) :
    AlgebraSubtype Δ a b ↔ Derivation Δ K a b :=
  ⟨fun h => (algebra_related hc h).derivation ha hb h.wellShaped_left h.wellShaped_right,
    Derivation.algebra⟩

/-- The finite protected capsule set is determined solely by the raw subtype
edge endpoints and the requested endpoints. Defined structure is unrestricted. -/
theorem algebra_iff_boundary_derivation (Δ : Bounds) (a b : CompareTy) :
    AlgebraSubtype Δ a b ↔ Derivation Δ (boundary Δ a b) a b :=
  algebra_iff_derivation (boundary_covers Δ a b) (boundary_left Δ a b) (boundary_right Δ a b)

theorem finite_capsule_locality (Δ : Bounds) (a b : CompareTy) :
    ∃ K : Set Token, K.Finite ∧ Covers Δ K ∧ Carrier Δ K a ∧ Carrier Δ K b ∧
      (AlgebraSubtype Δ a b ↔ Derivation Δ K a b) :=
  ⟨boundary Δ a b, boundary_finite Δ a b, boundary_covers Δ a b,
    boundary_left Δ a b, boundary_right Δ a b, algebra_iff_boundary_derivation Δ a b⟩

end
end ModalityInference.ComparisonRawCarrierRestriction
