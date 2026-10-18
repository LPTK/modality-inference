import ModalityInference.Proofs.ComparisonShapeCandidates
import ModalityInference.Proofs.ComparisonUnanchoredProjection

/-! Input-relative shape selection supplies the local hypotheses for sound
constructor projection. The declared bounds remain unchanged. -/
namespace ModalityInference.ComparisonShape

theorem unselected_zone {Δ : Bounds} {assignment : ComparisonShapeSolver.Assignment}
    {names : List TypeVar} {ρ : TypeVar → ComparisonShape}
    {templates : List ComparisonShape} {s : ComparisonShape} {v : TypeVar}
    (hmodel : Models Δ (ComparisonShapeSolver.action assignment))
    (hkeys : ∀ entry ∈ assignment, entry.1 ∈ names)
    (hbounds : ∀ {a b}, Constraint.sub a b ∈ Δ → ofTy a ∈ templates)
    (hv : v ∈ s.vars)
    (hn : ρ v ∉ candidates names (ComparisonShapeSolver.action assignment) templates)
    (hroot : ∀ w, s.subst ρ ≠ .var w) :
    ComparisonUnanchoredProjection.Zone Δ (ComparisonShapeSolver.action assignment)
      (s.subst ρ) := by
  refine ⟨hmodel, unselected_ne_action hkeys hv hn hroot, ?_⟩
  intro a b hab he
  rw [CompareTy.shape_ofTy] at he
  exact (unselected_ne_template hv (hbounds hab) hn) he.symm

/-- All declared endpoints and all fixed assignment keys suffice to establish
the projection zone at every constructor ancestor of a discarded parameter. -/
theorem declared_unselected_zone {Δ : Bounds}
    {assignment : ComparisonShapeSolver.Assignment} {ρ : TypeVar → ComparisonShape}
    {s : ComparisonShape} {v : TypeVar}
    (hmodel : Models Δ (ComparisonShapeSolver.action assignment))
    (hv : v ∈ s.vars)
    (hn : ρ v ∉ candidates (assignment.map Prod.fst)
      (ComparisonShapeSolver.action assignment) (declaredTemplates Δ))
    (hroot : ∀ w, s.subst ρ ≠ .var w) :
    ComparisonUnanchoredProjection.Zone Δ (ComparisonShapeSolver.action assignment)
      (s.subst ρ) :=
  unselected_zone hmodel (fun entry he => List.mem_map.mpr ⟨entry, he, rfl⟩)
    sub_left_mem_declaredTemplates hv hn hroot

end ModalityInference.ComparisonShape
