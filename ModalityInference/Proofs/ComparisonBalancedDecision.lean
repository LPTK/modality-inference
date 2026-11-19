import ModalityInference.Proofs.ComparisonBalancedProjection
import ModalityInference.Proofs.ComparisonObserverDecision

/-! The existing finite observer checker is exact after a balanced projection
when the original shape equations have no finite model. The projection retains
those equations and all scalar models while removing partial subtype edges. -/
namespace ModalityInference.ComparisonBalancedProjection

theorem query_valid {Δ : Bounds} (hΔ : ComparisonBalancedDerivation.Balanced Δ)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) {a b : CompareTy}
    (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) :
    (∀ world, (ComparisonObserverDecision.query (project Δ) a b).eval world = true) ↔
      AlgebraSubtype Δ a b :=
  (ComparisonObserverDecision.query_valid
    (fun ⟨ρ, hρ⟩ => hn ⟨ρ, (shapeModels_project Δ ρ).mp hρ⟩) (project_defined Δ)
    (fun η hη => ha η ((modeModels_project Δ η).mp hη))
    (fun η hη => hb η ((modeModels_project Δ η).mp hη))).trans
      (algebra_project_iff hΔ ha hb)

theorem run_correct {fuel Δ a b report}
    (h : ComparisonObserverDecision.run fuel (project Δ) a b = .success report)
    (hΔ : ComparisonBalancedDerivation.Balanced Δ)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (ha : CompareTy.DefinedUnder a Δ) (hb : CompareTy.DefinedUnder b Δ) :
    report.valid = true ↔ AlgebraSubtype Δ a b :=
  (ConcreteBackend.decideFormula_correct h).trans (query_valid hΔ hn ha hb)

theorem run_complete (Δ : Bounds) (a b : CompareTy) :
    ∃ threshold report, ∀ fuel ≥ threshold,
      ComparisonObserverDecision.run fuel (project Δ) a b = .success report :=
  ComparisonObserverDecision.run_complete (project Δ) a b

end ModalityInference.ComparisonBalancedProjection
