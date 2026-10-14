import ModalityInference.Proofs.GenerationCompletenessBase
import ModalityInference.Proofs.SolverGround

/-! Ground context coverage survives allocation outside the original support. -/
namespace ModalityInference

theorem AlgorithmicContextCovers.source_agreesBelow {ρ η τ : GroundAssignment}
    {A Γ used nt nm} (h : AlgorithmicContextCovers ρ τ A Γ used)
    (hb : A.Bounded nt nm) (ha : SolverGround.AgreesBelow η ρ nt nm) :
    AlgorithmicContextCovers η τ A Γ used := by
  intro i hi target ht
  obtain ⟨source, hl, hc⟩ := h i hi target ht
  have hs := lookupScheme_bounded hb hl.lookupScheme
  refine ⟨source, hl, hc.source_congr ?_ ?_⟩
  · intro v hv
    apply ha.1
    have hv := Finset.mem_filter.mp hv |>.1
    exact (Finset.mem_union.mp hv).elim
      ((source.body.bounded_iff nt nm).mp hs.1 |>.1 v)
      ((source.bounds.bounded_iff nt nm).mp hs.2 |>.1 v)
  · intro v hv
    apply ha.2
    have hv := Finset.mem_filter.mp hv |>.1
    exact (Finset.mem_union.mp hv).elim
      ((source.body.bounded_iff nt nm).mp hs.1 |>.2 v)
      ((source.bounds.bounded_iff nt nm).mp hs.2 |>.2 v)

end ModalityInference
