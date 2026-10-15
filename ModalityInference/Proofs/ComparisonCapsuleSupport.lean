import ModalityInference.Proofs.ComparisonCapsuleTotality
import ModalityInference.ComparisonInterpolation

namespace ModalityInference.ComparisonPartialCapsuleScalar

open ComparisonInterpolation ComparisonPartialCapsule

private theorem joinOption_support {Q : ModVar → Prop} {a b : Option ModExpr}
    (ha : ∀ q, a = some q → ∀ v ∈ q.vars, Q v)
    (hb : ∀ q, b = some q → ∀ v ∈ q.vars, Q v)
    {q : ModExpr} (h : joinOption a b = some q) : ∀ v ∈ q.vars, Q v := by
  cases a with
  | none =>
    cases b with
    | none => contradiction
    | some b => cases h; exact hb _ rfl
  | some a =>
    cases b with
    | none => cases h; exact ha _ rfl
    | some b =>
      cases h
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact ha a rfl v hv
      · exact hb b rfl v hv

private theorem meetOption_support {Q : ModVar → Prop} {a b : Option ModExpr}
    (ha : ∀ q, a = some q → ∀ v ∈ q.vars, Q v)
    (hb : ∀ q, b = some q → ∀ v ∈ q.vars, Q v)
    {q : ModExpr} (h : meetOption a b = some q) : ∀ v ∈ q.vars, Q v := by
  cases a with
  | none => cases b <;> contradiction
  | some a =>
    cases b with
    | none => contradiction
    | some b =>
      cases h
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact ha a rfl v hv
      · exact hb b rfl v hv

/-- Capsule projection introduces no modality identifiers. Its scalar witness
uses only identifiers already present in the internal type being projected. -/
theorem project_support (Δ : Bounds) (token : Token) (a : CompareTy)
    {P : TypeVar → Prop} {Q : ModVar → Prop} (hs : Supports P Q a)
    {q : ModExpr} (hp : project Δ token a = some q) : ∀ v ∈ q.vars, Q v := by
  match a with
  | .modal a m =>
    cases m
    case compose m n =>
      rw [project] at hp
      refine project_support Δ token (.modal (.modal a m) n) (P := P) (Q := Q) ?_ hp
      simp only [Supports, ModExpr.vars, Finset.mem_union, or_imp, forall_and] at hs ⊢
      exact ⟨⟨hs.1, hs.2.1⟩, hs.2.2⟩
    all_goals
      rw [project] at hp
      · split at hp
        · cases he : project Δ token a <;> simp only [he, Option.map] at hp
          · contradiction
          · cases hp
            intro v hv
            rcases Finset.mem_union.mp hv with hv | hv
            · exact project_support Δ token a hs.1 he v hv
            · exact hs.2 v hv
        · split at hp
          · cases hp
            intro v hv
            exact False.elim (Finset.notMem_empty v hv)
          · contradiction
      · simp
  | .join a b =>
    rw [project] at hp
    exact joinOption_support (fun _ he => project_support Δ token a hs.1 he)
      (fun _ he => project_support Δ token b hs.2 he) hp
  | .meet a b =>
    rw [project] at hp
    exact meetOption_support (fun _ he => project_support Δ token a hs.1 he)
      (fun _ he => project_support Δ token b hs.2 he) hp
  | .var _ | .unit | .credit | .prod _ _ | .sum _ _ | .fn _ _ =>
    simp [project] at hp
termination_by ComparisonPartialCapsule.size a
decreasing_by
  all_goals simp_wf
  all_goals simp_all only [ComparisonPartialCapsule.size, ComparisonPartialModes.expressionSize]
  all_goals omega

/-- The exact shared suffix for a mixed interval inherits the witness's finite
modality support. The projection equation makes this support explicit. -/
theorem mixed_normal_scalar_reconstruction_supported
    {P : TypeVar → Prop} {Q : ModVar → Prop} {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    {a b W : CompareTy} (sa : Normal Δ a) (sb : Normal Δ b)
    (ha : Atomic (a.shape.subst ρ)) {m n : ModExpr}
    (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n))
    (hl : AlgebraSubtype Δ a (.modal W m))
    (hu : AlgebraSubtype Δ (.modal W n) b)
    (hs : Supports P Q W) :
    ∃ q, project Δ sa.token W = some q ∧ (∀ v ∈ q.vars, Q v) ∧
      Entails Δ (.defined q) ∧
      (∀ c (sc : Normal Δ c) k, Entails Δ (.defined k) →
        AlgebraSubtype Δ c (.modal W k) →
        sc.token = sa.token ∧ Submode Δ sc.suffix (.compose q k)) ∧
      (∀ c (sc : Normal Δ c) k, Entails Δ (.defined k) →
        AlgebraSubtype Δ (.modal W k) c →
        sc.token = sa.token ∧ Submode Δ (.compose q k) sc.suffix) := by
  have hf : Frozen Δ sa.token := observe_frozen a (sa.observation ▸ Set.mem_singleton _)
  have hatom : Atomic (sa.token.1.shape.subst ρ) := by
    change Atomic ((.modal (.modal sa.token.1 sa.token.2) sa.suffix : CompareTy).shape.subst ρ)
    rw [←sa.forward.shape_equivalent ρ hρ]
    exact ha
  have hW : Atomic (W.shape.subst ρ) := by
    change Atomic ((.modal W m : CompareTy).shape.subst ρ)
    rw [←hl.shape_equivalent ρ hρ]
    exact ha
  have hab := opposite_tokens_eq hΔ hρ sa sb ha hm hn hl hu
  have hlow := (AlgebraSubtype.shaped sa.backward).trans hl
  obtain ⟨q, hq⟩ := project_from_lower hΔ hρ hf hatom hm sa.total hlow
  refine ⟨q, hq, project_support Δ sa.token W hs hq, project_total hq, ?_, ?_⟩
  · intro c sc k hk hc
    have hcatom : Atomic (c.shape.subst ρ) := by
      rw [hc.shape_equivalent ρ hρ]
      exact hW
    have he := (opposite_tokens_eq hΔ hρ sc sb hcatom hk hn hc hu).trans hab.symm
    refine ⟨he, ?_⟩
    have h := (AlgebraSubtype.shaped sc.backward).trans hc
    rw [he] at h
    exact project_lower hΔ hρ hf hatom hq hk sc.total h
  · intro c sc k hk hc
    have he := opposite_tokens_eq hΔ hρ sa sc ha hm hk hl hc
    refine ⟨he.symm, ?_⟩
    have h := hc.trans (.shaped sc.forward)
    rw [←he] at h
    exact project_upper hΔ hρ hf hatom hq hk sc.total h


end ModalityInference.ComparisonPartialCapsuleScalar

namespace ModalityInference.ComparisonCapsuleIntervals

open ComparisonInterpolation ComparisonBody ComparisonPartialCapsule
open ComparisonPartialCapsuleScalar

/-- The production plan reconstructs a shared scalar solution within the
original internal witness's modality support. -/
theorem plan_complete_known_supported {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    {fuel : Nat} {expressions known : List ModExpr}
    (hknown : knownTotal fuel Δ expressions = .success known)
    (name fresh : Nat) (requests : List Request) (W : CompareTy)
    {P : TypeVar → Prop} {Q : ModVar → Prop} (hs : Supports P Q W)
    (hatomic : ∀ r ∈ requests.filter (fun r => r.name == name),
      Atomic ((CompareTy.ofTy r.endpoint).shape.subst ρ))
    (hpartial : ∀ r ∈ requests.filter (fun r => r.name == name),
      ¬(CompareTy.ofTy r.endpoint).DefinedUnder Δ)
    (hcovered : ∀ r ∈ requests.filter (fun r => r.name == name),
      typeResiduals r.endpoint ⊆ expressions.flatMap residuals)
    (haction : ∀ r ∈ requests.filter (fun r => r.name == name),
      Entails Δ (.defined r.action))
    (hholds : ∀ r ∈ requests.filter (fun r => r.name == name), r.AlgebraHolds Δ W)
    (hlower : ∃ r ∈ requests.filter (fun r => r.name == name), r.isLower = true)
    (hupper : ∃ r ∈ requests.filter (fun r => r.name == name), r.isLower = false) :
    ∃ b q, plan (isTotal known) name fresh requests = some b ∧
      Entails Δ (.defined q) ∧ (∀ v ∈ q.vars, Q v) ∧
      ∀ r ∈ b.requests, Entails Δ (r.bound (isTotal known) q) := by
  obtain ⟨b, _, hb, _⟩ := (mixed_requests_iff_known hΔ hρ hknown name fresh requests
    hatomic hpartial hcovered haction hlower hupper).mp ⟨W, hholds⟩
  have hparsed : ∀ r ∈ requests.filter (fun r => r.name == name),
      Nonempty (ParsedNormal Δ (isTotal known) r.endpoint) :=
    fun r hr => peel_normal_known hΔ hρ hknown r.endpoint (hatomic r hr)
      (hpartial r hr) (hcovered r hr)
  obtain ⟨lo, hlo, hloPol⟩ := hlower
  obtain ⟨hi, hhi, hhiPol⟩ := hupper
  obtain ⟨sl⟩ := hparsed lo hlo
  obtain ⟨su⟩ := hparsed hi hhi
  have hl := hholds lo hlo
  have hu := hholds hi hhi
  simp only [Request.AlgebraHolds, hloPol, ↓reduceIte] at hl
  simp only [Request.AlgebraHolds, hhiPol, Bool.false_eq_true, ↓reduceIte] at hu
  obtain ⟨q, _, hsupport, hq, hlow, hupp⟩ := mixed_normal_scalar_reconstruction_supported
    hΔ hρ sl.normal su.normal (hatomic lo hlo) (haction lo hlo) (haction hi hhi) hl hu hs
  refine ⟨b, q, hb, hq, hsupport, ?_⟩
  intro r hr
  have hmem : r ∈ requests.filter (fun r => r.name == name) := (plan_spec hb).2.2.1 ▸ hr
  obtain ⟨sr⟩ := hparsed r hmem
  have hh := hholds r hmem
  cases hp : r.isLower
  · simp only [Request.AlgebraHolds, hp, Bool.false_eq_true, ↓reduceIte] at hh
    have hc := (hupp _ sr.normal _ (haction r hmem) hh).2
    simpa only [Request.bound, hp, Bool.false_eq_true, ↓reduceIte, Entails,
      Request.suffix, ←sr.suffix_eq] using hc
  · simp only [Request.AlgebraHolds, hp, ↓reduceIte] at hh
    have hc := (hlow _ sr.normal _ (haction r hmem) hh).2
    simpa only [Request.bound, hp, ↓reduceIte, Entails, Request.suffix,
      ←sr.suffix_eq] using hc

end ModalityInference.ComparisonCapsuleIntervals
