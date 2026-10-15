import ModalityInference.Proofs.ComparisonDefinedInstances
import ModalityInference.Proofs.ComparisonAlgebraInstances

/-! Defined comparison witnesses preserve every ordinary public instance and
its resource interpretation. -/
namespace ModalityInference

theorem AlgebraSubsumesUnder.ground_covers {ρ : GroundAssignment} {Δ : Bounds}
    {source target : Scheme} (h : AlgebraSubsumesUnder Δ source target)
    (hΔ : GroundModels ρ Δ) : SchemeCovers ρ ρ source target := by
  intro η ground hη htarget
  obtain ⟨θ, hb, he, hft, hfm⟩ := hη.skolemize (s := source) hΔ
  have hb := hb.assumptions_right
  obtain ⟨σ, hσ, hs, _, hd, hcs, hab⟩ := h
  have hi := hσ.ground (hcs.groundModels hb)
  obtain ⟨x, hx⟩ := hd.realize_defined (hs.ty source.body) hb
  have hbody := source.body.realize_compareGround hx
  obtain ⟨hreb, hrebase⟩ := hi.rebase hft hfm
  exact ⟨source.rebase ρ (σ.ground θ), x, hreb, hrebase.trans hbody,
    (hab.ground_instance hb hbody (he.trans htarget)).to_subtype⟩

theorem AlgebraSubsumesUnder.resource_semantic
    {ρ w Δ source target v reserved}
    (h : AlgebraSubsumesUnder Δ source target) (hΔ : GroundModels ρ Δ)
    (hv : ResourceSchemeInterpretation ρ w source v reserved) :
    ResourceSchemeInterpretation ρ w target v reserved :=
  (h.ground_covers hΔ).resource_semantic hv

end ModalityInference
