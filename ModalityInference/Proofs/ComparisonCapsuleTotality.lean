import ModalityInference.Proofs.ComparisonCapsuleCompleteness
import ModalityInference.ComparisonAnnotations

namespace ModalityInference.ComparisonBody

/-- A successful totality pass retains every semantically total queried expression. -/
theorem checkTotal_complete {fuel : Nat} {Δ : Bounds} {expressions known : List ModExpr}
    (h : checkTotal fuel Δ expressions = .success known)
    {m : ModExpr} (hm : m ∈ expressions) (hd : Entails Δ (.defined m)) : m ∈ known := by
  induction expressions generalizing known with
  | nil => simp at hm
  | cons e es ih =>
    cases he : ConcreteBackend.entails fuel Δ [.defined e] <;>
      simp only [checkTotal, he, bind, pure, RunResult.bind] at h <;> try contradiction
    cases hr : checkTotal fuel Δ es <;> simp only [hr] at h <;> try contradiction
    cases h
    rcases List.mem_cons.mp hm with rfl | hm
    · have hv := (ConcreteBackend.entails_correct he).mpr
        (fun η hη c hc => by
          rcases List.mem_singleton.mp hc with rfl
          exact hd η hη)
      simp only [hv, ↓reduceIte, List.mem_cons, true_or]
    · split
      · exact List.mem_cons_of_mem _ (ih hr hm)
      · exact ih hr hm

private theorem eraseDups_mem (m : ModExpr) (ms : List ModExpr) :
    m ∈ ms.eraseDups ↔ m ∈ ms := by
  have aux : ∀ xs acc : List ModExpr,
      m ∈ List.eraseDupsBy.loop (· == ·) xs acc ↔ m ∈ xs ∨ m ∈ acc := by
    intro xs
    induction xs with
    | nil => intro acc; simp [List.eraseDupsBy.loop]
    | cons x xs ih =>
      intro acc
      simp only [List.eraseDupsBy.loop]
      split
      · next h =>
        have hx : x ∈ acc := by
          obtain ⟨a, ha, he⟩ := List.any_eq_true.mp h
          simpa only [←beq_iff_eq.mp he] using ha
        rw [ih]
        simp only [List.mem_cons]
        constructor
        · tauto
        · rintro ((rfl | h) | h)
          · exact Or.inr hx
          · exact Or.inl h
          · exact Or.inr h
      · rw [ih]
        simp only [List.mem_cons]
        tauto
  simpa only [List.eraseDups, List.eraseDupsBy, List.not_mem_nil, or_false] using aux ms []

theorem knownTotal_complete {fuel : Nat} {Δ : Bounds} {expressions known : List ModExpr}
    (h : knownTotal fuel Δ expressions = .success known)
    {m : ModExpr} (hm : m ∈ expressions.flatMap residuals)
    (hd : Entails Δ (.defined m)) : m ∈ known :=
  checkTotal_complete h ((eraseDups_mem _ _).mpr hm) hd

/-- Structural totality recognition is complete once every residual in the
expression has been submitted to the semantic totality pass. -/
theorem isTotal_complete {Δ : Bounds} {known : List ModExpr} (m : ModExpr)
    (hknown : ∀ r ∈ residuals m, Entails Δ (.defined r) → r ∈ known)
    (hd : Entails Δ (.defined m)) : isTotal known m = true := by
  induction m with
  | const | var => rfl
  | leftResidual a b _ _ | rightResidual a b _ _ =>
    exact List.contains_iff_mem.mpr (hknown _ List.mem_cons_self hd)
  | compose a b iha ihb | meet a b iha ihb | join a b iha ihb =>
    simp only [isTotal, Bool.and_eq_true]
    have ha : Entails Δ (.defined a) := by
      intro η hη
      have h := hd η hη
      cases he : a.eval (some ∘ η) <;> cases hf : b.eval (some ∘ η) <;>
        simp_all [ModExpr.WellFormed, ModExpr.eval]
    have hb : Entails Δ (.defined b) := by
      intro η hη
      have h := hd η hη
      cases he : a.eval (some ∘ η) <;> cases hf : b.eval (some ∘ η) <;>
        simp_all [ModExpr.WellFormed, ModExpr.eval]
    exact ⟨iha (fun r hr => hknown r (List.mem_append_left _ hr)) ha,
      ihb (fun r hr => hknown r (List.mem_append_right _ hr)) hb⟩
  | close a ih | closeInv a ih | future a ih | capture a ih =>
    apply ih hknown
    intro η hη
    have h := hd η hη
    cases he : a.eval (some ∘ η) <;> simp_all [ModExpr.WellFormed, ModExpr.eval]

theorem knownTotal_isTotal_complete {fuel : Nat} {Δ : Bounds}
    {expressions known : List ModExpr}
    (h : knownTotal fuel Δ expressions = .success known)
    (m : ModExpr) (hm : residuals m ⊆ expressions.flatMap residuals)
    (hd : Entails Δ (.defined m)) : isTotal known m = true :=
  isTotal_complete m (fun _ hr => knownTotal_complete h (hm hr)) hd

/-- Residual operations appearing anywhere in a public type's annotations. -/
def typeResiduals (t : Ty) : List ModExpr :=
  (ComparisonAnnotations.expressions t).flatMap residuals

private theorem residuals_body_subset (a : Ty) (m : ModExpr) :
    typeResiduals a ⊆ typeResiduals (.modal a m) := by
  exact List.subset_append_right _ _

theorem normalizeOuterFuel_residuals (fuel : Nat) (t : Ty) :
    typeResiduals (ComparisonPartialModes.normalizeOuterFuel fuel t) ⊆ typeResiduals t := by
  induction fuel generalizing t with
  | zero => exact List.Subset.refl _
  | succ fuel ih =>
    cases t with
    | modal a m =>
      cases m
      case compose m n =>
        intro r hr
        have hx := ih (.modal (.modal a m) n) hr
        simpa only [typeResiduals, ComparisonAnnotations.expressions,
          List.flatMap_cons, residuals, List.mem_append, or_assoc, or_left_comm] using hx
      all_goals
        simp only [ComparisonPartialModes.normalizeOuterFuel]
        split
        · exact (ih a).trans (residuals_body_subset _ _)
        · exact List.Subset.refl _
    | _ => exact List.Subset.refl _

theorem peelFuel_residuals (total : ModExpr → Bool) (fuel : Nat) (t : Ty) :
    typeResiduals (peelFuel total fuel t).base ⊆ typeResiduals t := by
  induction fuel generalizing t with
  | zero => exact List.Subset.refl _
  | succ fuel ih =>
    have hs := normalizeOuterFuel_residuals (ComparisonPartialModes.modalitySize t) t
    change typeResiduals (ComparisonPartialModes.normalizeOuter t) ⊆ typeResiduals t at hs
    cases hn : ComparisonPartialModes.normalizeOuter t <;> simp only [peelFuel, hn]
    all_goals try exact hn ▸ hs
    case modal a m =>
      split
      · exact (ih a).trans ((residuals_body_subset a m).trans (hn ▸ hs))
      · exact hn ▸ hs

theorem peel_residuals (total : ModExpr → Bool) (t : Ty) :
    typeResiduals (peel total t).base ⊆ typeResiduals t := peelFuel_residuals total _ t

/-- The actual residual pass decides the label at which executable peeling
stops, provided the queried expressions include the input's residuals. -/
theorem peel_stopped_complete {fuel : Nat} {Δ : Bounds}
    {expressions known : List ModExpr}
    (h : knownTotal fuel Δ expressions = .success known)
    (t : Ty) (hcovered : typeResiduals t ⊆ expressions.flatMap residuals)
    {a : Ty} {m : ModExpr}
    (hbase : (peel (isTotal known) t).base = .modal a m)
    (hd : Entails Δ (.defined m)) : isTotal known m = true := by
  apply knownTotal_isTotal_complete h m _ hd
  intro r hr
  apply hcovered
  apply peel_residuals (isTotal known) t
  rw [hbase]
  exact List.mem_append_left _ hr

end ModalityInference.ComparisonBody


namespace ModalityInference.ComparisonCapsuleIntervals

open ComparisonBody ComparisonPartialCapsule

/-- The production residual pass supplies the executable capsule normal form. -/
theorem peel_normal_known {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    {fuel : Nat} {expressions known : List ModExpr}
    (hknown : knownTotal fuel Δ expressions = .success known)
    (t : Ty) (hatom : Atomic ((CompareTy.ofTy t).shape.subst ρ))
    (hpartial : ¬(CompareTy.ofTy t).DefinedUnder Δ)
    (hcovered : typeResiduals t ⊆ expressions.flatMap residuals) :
    Nonempty (ParsedNormal Δ (isTotal known) t) :=
  peel_normal hΔ hρ (isTotal known)
    (fun _ h => isTotal_defined (knownTotal_sound hknown) h) t hatom hpartial
    (fun _ _ h => peel_stopped_complete hknown t hcovered h)

/-- Production totality recognition and the capsule planner exactly reduce a
mixed partial atomic interval to one shared symbolic suffix. -/
theorem mixed_requests_iff_known {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    {fuel : Nat} {expressions known : List ModExpr}
    (hknown : knownTotal fuel Δ expressions = .success known)
    (name fresh : Nat) (requests : List Request)
    (hatomic : ∀ r ∈ requests.filter (fun r => r.name == name),
      Atomic ((CompareTy.ofTy r.endpoint).shape.subst ρ))
    (hpartial : ∀ r ∈ requests.filter (fun r => r.name == name),
      ¬(CompareTy.ofTy r.endpoint).DefinedUnder Δ)
    (hcovered : ∀ r ∈ requests.filter (fun r => r.name == name),
      typeResiduals r.endpoint ⊆ expressions.flatMap residuals)
    (haction : ∀ r ∈ requests.filter (fun r => r.name == name),
      Entails Δ (.defined r.action))
    (hlower : ∃ r ∈ requests.filter (fun r => r.name == name), r.isLower = true)
    (hupper : ∃ r ∈ requests.filter (fun r => r.name == name), r.isLower = false) :
    (∃ W, ∀ r ∈ requests.filter (fun r => r.name == name), r.AlgebraHolds Δ W) ↔
      ∃ b q, plan (isTotal known) name fresh requests = some b ∧
        Entails Δ (.defined q) ∧
        ∀ r ∈ b.requests, Entails Δ (r.bound (isTotal known) q) :=
  mixed_requests_iff_scalar hΔ hρ (isTotal known)
    (fun _ h => isTotal_defined (knownTotal_sound hknown) h) name fresh requests
    hatomic hpartial
    (fun r hr _ _ h => peel_stopped_complete hknown r.endpoint (hcovered r hr) h)
    haction hlower hupper

end ModalityInference.ComparisonCapsuleIntervals
