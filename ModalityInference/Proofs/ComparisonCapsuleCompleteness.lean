import ModalityInference.Proofs.ComparisonCapsulePeeling

namespace ModalityInference.ComparisonCapsuleIntervals

open ComparisonBody ComparisonPartialModes ComparisonPartialCapsule
open ComparisonPartialCapsuleScalar

/-- An internal image meets a request before its shared suffix is reconstructed. -/
def Request.AlgebraHolds (Δ : Bounds) (r : Request) (image : CompareTy) : Prop :=
  if r.isLower then AlgebraSubtype Δ (.ofTy r.endpoint) (.modal image r.action)
  else AlgebraSubtype Δ (.modal image r.action) (.ofTy r.endpoint)

private theorem ofTy_eq_iff (a b : Ty) : CompareTy.ofTy a = CompareTy.ofTy b ↔ a = b := by
  induction a generalizing b <;> cases b <;> simp_all [CompareTy.ofTy]

private theorem ofTy_injective : Function.Injective CompareTy.ofTy :=
  fun _ _ h => (ofTy_eq_iff _ _).mp h

theorem plan_of_equal_bases (total : ModExpr → Bool) (name fresh : Nat)
    (requests : List Request) (base : Ty)
    (hne : requests.filter (fun r => r.name == name) ≠ [])
    (hb : ∀ r ∈ requests.filter (fun r => r.name == name), r.base total = base) :
    ∃ b, plan total name fresh requests = some b := by
  unfold plan
  dsimp only
  split
  · contradiction
  · next r rs he =>
    have h : rs.all (fun s => s.base total == r.base total) = true := by
      simp only [List.all_eq_true, beq_iff_eq]
      intro s hs
      exact (hb s (he ▸ List.mem_cons_of_mem r hs)).trans
        (hb r (he ▸ List.mem_cons_self)).symm
    simp only [h, ↓reduceIte]
    exact ⟨_, rfl⟩

/-- Mixed requests with partial atomic endpoints share one executable capsule
base and one scalar witness, even when the original image has internal lattice
nodes or partial annotations. -/
theorem plan_complete_of_normals {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    (total : ModExpr → Bool) (name fresh : Nat) (requests : List Request)
    (W : CompareTy)
    (hparsed : ∀ r ∈ requests.filter (fun r => r.name == name),
      Nonempty (ParsedNormal Δ total r.endpoint))
    (hatomic : ∀ r ∈ requests.filter (fun r => r.name == name),
      Atomic ((CompareTy.ofTy r.endpoint).shape.subst ρ))
    (haction : ∀ r ∈ requests.filter (fun r => r.name == name),
      Entails Δ (.defined r.action))
    (hholds : ∀ r ∈ requests.filter (fun r => r.name == name), r.AlgebraHolds Δ W)
    (hlower : ∃ r ∈ requests.filter (fun r => r.name == name), r.isLower = true)
    (hupper : ∃ r ∈ requests.filter (fun r => r.name == name), r.isLower = false) :
    ∃ b q, plan total name fresh requests = some b ∧ Entails Δ (.defined q) ∧
      ∀ r ∈ b.requests, Entails Δ (r.bound total q) := by
  obtain ⟨lo, hlo, hloPol⟩ := hlower
  obtain ⟨hi, hhi, hhiPol⟩ := hupper
  obtain ⟨sl⟩ := hparsed lo hlo
  obtain ⟨su⟩ := hparsed hi hhi
  have hl := hholds lo hlo
  have hu := hholds hi hhi
  simp only [Request.AlgebraHolds, hloPol, ↓reduceIte] at hl
  simp only [Request.AlgebraHolds, hhiPol, Bool.false_eq_true, ↓reduceIte] at hu
  obtain ⟨q, hq, hlow, hupp⟩ := mixed_normal_scalar_reconstruction hΔ hρ
    sl.normal su.normal (hatomic lo hlo) (haction lo hlo) (haction hi hhi) hl hu
  have hr : ∀ r ∈ requests.filter (fun r => r.name == name),
      r.base total = lo.base total ∧ Entails Δ (r.bound total q) := by
    intro r hr
    obtain ⟨s⟩ := hparsed r hr
    have hh := hholds r hr
    have hm := haction r hr
    cases hp : r.isLower
    · simp only [Request.AlgebraHolds, hp, Bool.false_eq_true, ↓reduceIte] at hh
      obtain ⟨ht, hb⟩ := hupp _ s.normal _ hm hh
      constructor
      · apply ofTy_injective
        exact s.base_eq.trans ((congrArg (fun t : CompareTy × ModExpr =>
          CompareTy.modal t.1 t.2) ht).trans sl.base_eq.symm)
      · simpa only [Request.bound, hp, Bool.false_eq_true, ↓reduceIte, Entails,
          Request.suffix, ←s.suffix_eq] using hb
    · simp only [Request.AlgebraHolds, hp, ↓reduceIte] at hh
      obtain ⟨ht, hb⟩ := hlow _ s.normal _ hm hh
      constructor
      · apply ofTy_injective
        exact s.base_eq.trans ((congrArg (fun t : CompareTy × ModExpr =>
          CompareTy.modal t.1 t.2) ht).trans sl.base_eq.symm)
      · simpa only [Request.bound, hp, ↓reduceIte, Entails,
          Request.suffix, ←s.suffix_eq] using hb
  obtain ⟨b, hb⟩ := plan_of_equal_bases total name fresh requests (lo.base total)
    (fun he => List.not_mem_nil (he ▸ hlo)) (fun r hmem => (hr r hmem).1)
  refine ⟨b, q, hb, hq, ?_⟩
  intro r hmem
  exact (hr r ((plan_spec hb).2.2.1 ▸ hmem)).2

/-- The executable peel and plan preserve every valid mixed atomic interval.
Only the totality decision at each stopped input label must be complete. -/
theorem plan_complete_mixed {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    (total : ModExpr → Bool)
    (hsound : ∀ m, total m = true → Entails Δ (.defined m))
    (name fresh : Nat) (requests : List Request) (W : CompareTy)
    (hatomic : ∀ r ∈ requests.filter (fun r => r.name == name),
      Atomic ((CompareTy.ofTy r.endpoint).shape.subst ρ))
    (hpartial : ∀ r ∈ requests.filter (fun r => r.name == name),
      ¬(CompareTy.ofTy r.endpoint).DefinedUnder Δ)
    (hcomplete : ∀ r ∈ requests.filter (fun r => r.name == name),
      ∀ a m, r.base total = .modal a m → Entails Δ (.defined m) → total m = true)
    (haction : ∀ r ∈ requests.filter (fun r => r.name == name),
      Entails Δ (.defined r.action))
    (hholds : ∀ r ∈ requests.filter (fun r => r.name == name), r.AlgebraHolds Δ W)
    (hlower : ∃ r ∈ requests.filter (fun r => r.name == name), r.isLower = true)
    (hupper : ∃ r ∈ requests.filter (fun r => r.name == name), r.isLower = false) :
    ∃ b q, plan total name fresh requests = some b ∧ Entails Δ (.defined q) ∧
      ∀ r ∈ b.requests, Entails Δ (r.bound total q) :=
  plan_complete_of_normals hΔ hρ total name fresh requests W
    (fun r hr => peel_normal hΔ hρ total hsound r.endpoint (hatomic r hr)
      (hpartial r hr) (hcomplete r hr)) hatomic haction hholds hlower hupper

/-- A plan and its scalar solution reconstruct one public, join-free image. -/
theorem plan_public_solution {Δ : Bounds} (total : ModExpr → Bool)
    (hsound : ∀ m, total m = true → Entails Δ (.defined m))
    {name fresh : Nat} {requests : List Request} {b : Binding} {q : ModExpr}
    (hplan : plan total name fresh requests = some b)
    (hb : ∀ r ∈ b.requests, Entails Δ (r.bound total q)) :
    ∀ r ∈ requests.filter (fun r => r.name == name), r.Holds Δ (.modal b.base q) := by
  intro r hr
  have hm : r ∈ b.requests := (plan_spec hplan).2.2.1.symm ▸ hr
  exact request_correct total (fun m hm => Submode.refl (hsound m hm))
    ((plan_spec hplan).2.2.2.2 r hm) (hb r hm)

/-- For mixed partial atomic endpoints, the executable capsule plan and its
shared scalar inequalities are an exact criterion for an arbitrary internal
type witness. A successful scalar solution always gives a public type image. -/
theorem mixed_requests_iff_scalar {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    (total : ModExpr → Bool)
    (hsound : ∀ m, total m = true → Entails Δ (.defined m))
    (name fresh : Nat) (requests : List Request)
    (hatomic : ∀ r ∈ requests.filter (fun r => r.name == name),
      Atomic ((CompareTy.ofTy r.endpoint).shape.subst ρ))
    (hpartial : ∀ r ∈ requests.filter (fun r => r.name == name),
      ¬(CompareTy.ofTy r.endpoint).DefinedUnder Δ)
    (hcomplete : ∀ r ∈ requests.filter (fun r => r.name == name),
      ∀ a m, r.base total = .modal a m → Entails Δ (.defined m) → total m = true)
    (haction : ∀ r ∈ requests.filter (fun r => r.name == name),
      Entails Δ (.defined r.action))
    (hlower : ∃ r ∈ requests.filter (fun r => r.name == name), r.isLower = true)
    (hupper : ∃ r ∈ requests.filter (fun r => r.name == name), r.isLower = false) :
    (∃ W, ∀ r ∈ requests.filter (fun r => r.name == name), r.AlgebraHolds Δ W) ↔
      ∃ b q, plan total name fresh requests = some b ∧ Entails Δ (.defined q) ∧
        ∀ r ∈ b.requests, Entails Δ (r.bound total q) := by
  constructor
  · rintro ⟨W, hW⟩
    exact plan_complete_mixed hΔ hρ total hsound name fresh requests W
      hatomic hpartial hcomplete haction hW hlower hupper
  · rintro ⟨b, q, hb, _, hbounds⟩
    refine ⟨.ofTy (.modal b.base q), ?_⟩
    intro r hr
    have h := plan_public_solution total hsound hb hbounds r hr
    cases hp : r.isLower <;> simp only [Request.Holds, Request.AlgebraHolds, hp,
      Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> exact .shaped h.to_shaped

end ModalityInference.ComparisonCapsuleIntervals
