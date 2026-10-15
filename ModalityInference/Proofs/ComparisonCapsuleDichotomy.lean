import ModalityInference.Proofs.ComparisonCapsuleTotality
import ModalityInference.Proofs.ComparisonDefinedCoverFamilies

namespace ModalityInference.ComparisonAnnotations

/-- A public type is defined exactly when all of its written annotations are. -/
theorem defined_iff_expressions (Δ : Bounds) (t : Ty) :
    (CompareTy.ofTy t).DefinedUnder Δ ↔
      ∀ m ∈ expressions t, Entails Δ (.defined m) := by
  induction t with
  | var | unit | credit =>
    simp [expressions, CompareTy.ofTy, CompareTy.DefinedUnder,
      CompareTy.wellFormedBounds, ModeModels]
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    simpa only [expressions, CompareTy.ofTy, CompareTy.definedUnder_prod_iff,
      CompareTy.definedUnder_sum_iff, CompareTy.definedUnder_fn_iff,
      List.mem_append, or_imp, forall_and] using and_congr iha ihb
  | modal a m ih =>
    simp only [expressions, CompareTy.ofTy, CompareTy.definedUnder_modal_iff,
      List.forall_mem_cons, ih, and_comm]

/-- The production totality pass classifies public types exactly on the input
residual support, including partial annotations nested below total wrappers. -/
theorem hasPartial_known_false_iff {Δ : Bounds} {fuel : Nat}
    {input known : List ModExpr}
    (hknown : ComparisonBody.knownTotal fuel Δ input = .success known)
    (t : Ty)
    (hcovered : ComparisonBody.typeResiduals t ⊆ input.flatMap ComparisonBody.residuals) :
    hasPartial (ComparisonBody.isTotal known) t = false ↔
      (CompareTy.ofTy t).DefinedUnder Δ := by
  rw [defined_iff_expressions]
  simp only [hasPartial, List.any_eq_false, Bool.not_eq_true', Bool.not_eq_false]
  constructor
  · intro h m hm
    exact ComparisonBody.isTotal_defined (ComparisonBody.knownTotal_sound hknown) (h m hm)
  · intro h m hm
    apply ComparisonBody.knownTotal_isTotal_complete hknown m _ (h m hm)
    intro r hr
    exact hcovered (List.mem_flatMap.mpr ⟨m, hm, hr⟩)

theorem hasPartial_known_true_iff {Δ : Bounds} {fuel : Nat}
    {input known : List ModExpr}
    (hknown : ComparisonBody.knownTotal fuel Δ input = .success known)
    (t : Ty)
    (hcovered : ComparisonBody.typeResiduals t ⊆ input.flatMap ComparisonBody.residuals) :
    hasPartial (ComparisonBody.isTotal known) t = true ↔
      ¬(CompareTy.ofTy t).DefinedUnder Δ := by
  rw [←hasPartial_known_false_iff hknown t hcovered]
  exact Bool.ne_false_iff.symm

end ModalityInference.ComparisonAnnotations

namespace ModalityInference.ComparisonCapsuleIntervals

open ComparisonPartialCarrier ComparisonDefinedCovers

/-- Opposite carrier boundaries of one internal image have the same
 definedness status through any total occurrence actions. -/
theorem carrier_interval_defined_iff {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a b W : CompareTy} {m n : ModExpr}
    (ha : Carrier Δ a) (hb : Carrier Δ b)
    (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n))
    (hl : AlgebraSubtype Δ a (.modal W m))
    (hu : AlgebraSubtype Δ (.modal W n) b) :
    a.DefinedUnder Δ ↔ b.DefinedUnder Δ := by
  constructor
  · intro hd
    obtain ⟨_, c, _, hc, hcw, _⟩ := defined_lower_modal_cover hΔ hd hl
    exact hb.defined_of_above hΔ (CompareTy.definedUnder_modal_iff.mpr ⟨hc, hn⟩)
      ((AlgebraSubtype.congr hcw (.refl hn)).trans hu)
  · intro hd
    obtain ⟨_, c, _, hc, hwc, _⟩ := defined_upper_modal_cover hΔ hd hu
    exact ha.defined_of_below hΔ (CompareTy.definedUnder_modal_iff.mpr ⟨hc, hm⟩)
      (hl.trans (.congr hwc (.refl hm)))

/-- Every endpoint in a mixed family shares its definedness status with any
chosen lower endpoint. There is no shape restriction on this statement. -/
theorem mixed_requests_defined_iff {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (requests : List Request) (W : CompareTy)
    (haction : ∀ r ∈ requests, Entails Δ (.defined r.action))
    (hholds : ∀ r ∈ requests, r.AlgebraHolds Δ W)
    {lo hi : Request} (hlo : lo ∈ requests) (hloPol : lo.isLower = true)
    (hhi : hi ∈ requests) (hhiPol : hi.isLower = false) :
    ∀ r ∈ requests, (CompareTy.ofTy r.endpoint).DefinedUnder Δ ↔
      (CompareTy.ofTy lo.endpoint).DefinedUnder Δ := by
  have hl := hholds lo hlo
  have hu := hholds hi hhi
  simp only [Request.AlgebraHolds, hloPol, ↓reduceIte] at hl
  simp only [Request.AlgebraHolds, hhiPol, Bool.false_eq_true, ↓reduceIte] at hu
  have hcommon := carrier_interval_defined_iff hΔ (Carrier.of_public lo.endpoint)
    (Carrier.of_public hi.endpoint) (haction lo hlo) (haction hi hhi) hl hu
  intro r hr
  have h := hholds r hr
  cases hp : r.isLower
  · simp only [Request.AlgebraHolds, hp, Bool.false_eq_true, ↓reduceIte] at h
    exact (carrier_interval_defined_iff hΔ (Carrier.of_public lo.endpoint)
      (Carrier.of_public r.endpoint) (haction lo hlo) (haction r hr) hl h).symm
  · simp only [Request.AlgebraHolds, hp, ↓reduceIte] at h
    exact (carrier_interval_defined_iff hΔ (Carrier.of_public r.endpoint)
      (Carrier.of_public hi.endpoint) (haction r hr) (haction hi hhi) h hu).trans hcommon.symm

theorem mixed_requests_dichotomy {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (requests : List Request) (W : CompareTy)
    (haction : ∀ r ∈ requests, Entails Δ (.defined r.action))
    (hholds : ∀ r ∈ requests, r.AlgebraHolds Δ W)
    (hlower : ∃ r ∈ requests, r.isLower = true)
    (hupper : ∃ r ∈ requests, r.isLower = false) :
    (∀ r ∈ requests, (CompareTy.ofTy r.endpoint).DefinedUnder Δ) ∨
      (∀ r ∈ requests, ¬(CompareTy.ofTy r.endpoint).DefinedUnder Δ) := by
  classical
  obtain ⟨lo, hlo, hloPol⟩ := hlower
  obtain ⟨hi, hhi, hhiPol⟩ := hupper
  have h := mixed_requests_defined_iff hΔ requests W haction hholds hlo hloPol hhi hhiPol
  by_cases hd : (CompareTy.ofTy lo.endpoint).DefinedUnder Δ
  · exact Or.inl fun r hr => (h r hr).mpr hd
  · exact Or.inr fun r hr he => hd ((h r hr).mp he)

/-- The executable classification is uniform on each satisfiable mixed
request family. A partial branch therefore has no defined endpoints to omit. -/
theorem mixed_requests_totality_dichotomy {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {fuel : Nat} {input known : List ModExpr}
    (hknown : ComparisonBody.knownTotal fuel Δ input = .success known)
    (requests : List Request) (W : CompareTy)
    (hcovered : ∀ r ∈ requests,
      ComparisonBody.typeResiduals r.endpoint ⊆ input.flatMap ComparisonBody.residuals)
    (haction : ∀ r ∈ requests, Entails Δ (.defined r.action))
    (hholds : ∀ r ∈ requests, r.AlgebraHolds Δ W)
    (hlower : ∃ r ∈ requests, r.isLower = true)
    (hupper : ∃ r ∈ requests, r.isLower = false) :
    (∀ r ∈ requests,
      ComparisonAnnotations.hasPartial (ComparisonBody.isTotal known) r.endpoint = false) ∨
    (∀ r ∈ requests,
      ComparisonAnnotations.hasPartial (ComparisonBody.isTotal known) r.endpoint = true) := by
  rcases mixed_requests_dichotomy hΔ requests W haction hholds hlower hupper with hd | hp
  · exact Or.inl fun r hr =>
      (ComparisonAnnotations.hasPartial_known_false_iff hknown r.endpoint (hcovered r hr)).mpr
        (hd r hr)
  · exact Or.inr fun r hr =>
      (ComparisonAnnotations.hasPartial_known_true_iff hknown r.endpoint (hcovered r hr)).mpr
        (hp r hr)

end ModalityInference.ComparisonCapsuleIntervals
