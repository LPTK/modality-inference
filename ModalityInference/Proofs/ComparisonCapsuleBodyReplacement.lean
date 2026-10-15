import ModalityInference.Proofs.ComparisonCapsuleCarrierReplacement
import ModalityInference.Proofs.ComparisonBoundDefinedness

namespace ModalityInference.ComparisonPartialCarrier

open ComparisonDefinedCovers

/-- A replacement retains every comparison with a carrier boundary. -/
def PreservesBounds (Δ : Bounds) (original replacement : CompareTy) : Prop :=
  ∀ lower endpoint, Carrier Δ endpoint → Refines Δ lower endpoint original →
    Refines Δ lower endpoint replacement

theorem PreservesBounds.refl (Δ : Bounds) (a : CompareTy) : PreservesBounds Δ a a :=
  fun _ _ _ h => h

theorem PreservesBounds.trans {Δ : Bounds} {a b c : CompareTy}
    (hab : PreservesBounds Δ a b) (hbc : PreservesBounds Δ b c) : PreservesBounds Δ a c :=
  fun lower endpoint hc h => hbc lower endpoint hc (hab lower endpoint hc h)

/-- Type parameters below an annotation for which the supplied totality
predicate does not justify congruence retain their literal images. -/
abbrev frozenTypes := ComparisonCapsuleContext.frozenTypeSupport

theorem frozenTypes_subset (total : ModExpr → Bool) (body : Ty) :
    frozenTypes total body ⊆ body.typeVars := by
  induction body <;> simp only [frozenTypes, ComparisonCapsuleContext.frozenTypeSupport, TypeExpr.typeVars]
  case var | unit | credit => exact Finset.empty_subset _
  case prod a b ia ib | sum a b ia ib | fn a b ia ib => exact Finset.union_subset_union ia ib
  case modal a m ih => split <;> first | exact ih | exact Finset.Subset.refl _

/-- Carrier-bound preserving images can replace all unfrozen parameters in a
public type context, in either comparison polarity. -/
theorem InDirection.replace {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (types replacement : TypeVar → CompareTy) (modes : ModVar → ModExpr)
    (total : ModExpr → Bool)
    (htotal : ∀ m, total m = true → Entails Δ (.defined (m.subst modes)))
    (body : Ty) :
    ∀ lower endpoint, (publicImage types modes body).WellShaped Δ →
      InDirection Δ lower (publicImage types modes body) endpoint →
      (∀ v ∈ body.typeVars, PreservesBounds Δ (types v) (replacement v)) →
      (∀ v ∈ frozenTypes total body, replacement v = types v) →
      Refines Δ lower endpoint (publicImage replacement modes body) := by
  induction body with
  | var v =>
    intro lower endpoint hs h hp _
    exact hp v (Finset.mem_singleton_self _) lower endpoint h.carrier (h.sound hs)
  | unit | credit =>
    intro lower endpoint hs h _ _
    exact h.sound hs
  | prod a b ia ib =>
    intro lower endpoint hs h hp hf
    obtain ⟨c, d, hc, hd, hcd⟩ := h.prod_factor hΔ
    exact refine_trans hcd ((ia lower c hs.1 hc
      (fun v hv => hp v (Finset.mem_union_left _ hv))
      (fun v hv => hf v (Finset.mem_union_left _ hv))).prod
        (ib lower d hs.2 hd
          (fun v hv => hp v (Finset.mem_union_right _ hv))
          (fun v hv => hf v (Finset.mem_union_right _ hv))))
  | sum a b ia ib =>
    intro lower endpoint hs h hp hf
    obtain ⟨c, d, hc, hd, hcd⟩ := h.sum_factor hΔ
    exact refine_trans hcd ((ia lower c hs.1 hc
      (fun v hv => hp v (Finset.mem_union_left _ hv))
      (fun v hv => hf v (Finset.mem_union_left _ hv))).sum
        (ib lower d hs.2 hd
          (fun v hv => hp v (Finset.mem_union_right _ hv))
          (fun v hv => hf v (Finset.mem_union_right _ hv))))
  | fn a b ia ib =>
    intro lower endpoint hs h hp hf
    obtain ⟨c, d, hc, hd, hcd⟩ := h.fn_factor hΔ
    exact refine_trans hcd ((ia (!lower) c hs.1 hc
      (fun v hv => hp v (Finset.mem_union_left _ hv))
      (fun v hv => hf v (Finset.mem_union_left _ hv))).fn
        (ib lower d hs.2 hd
          (fun v hv => hp v (Finset.mem_union_right _ hv))
          (fun v hv => hf v (Finset.mem_union_right _ hv))))
  | modal a m ia =>
    intro lower endpoint hs h hp hf
    by_cases hm : total m = true
    · have ht := htotal m hm
      obtain ⟨c, hc, he⟩ := h.modal_factor hΔ ht
      have hf' : ∀ v ∈ frozenTypes total a, replacement v = types v := by
        simpa only [frozenTypes, ComparisonCapsuleContext.frozenTypeSupport, hm, ↓reduceIte] using hf
      exact refine_trans he (refine_modal ht (ia lower c hs hc hp hf'))
    · have he : publicImage replacement modes (.modal a m) = publicImage types modes (.modal a m) :=
        ComparisonAbsorption.instantiate_congr (.modal a m)
          (by simpa only [frozenTypes, ComparisonCapsuleContext.frozenTypeSupport, hm, ↓reduceIte, TypeExpr.typeVars] using hf)
          (fun _ _ => rfl)
      rw [he]
      exact h.sound hs

/-- Whole-body reconstruction keeps exactly the source-derived frozen support;
all other internal images need only preserve their carrier bounds. -/
theorem body_replacement {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {types replacement : TypeVar → CompareTy} {modes : ModVar → ModExpr}
    (total : ModExpr → Bool)
    (htotal : ∀ m, total m = true → Entails Δ (.defined (m.subst modes)))
    {body : Ty} {endpoint : CompareTy} (hc : Carrier Δ endpoint)
    (h : AlgebraSubtype Δ (publicImage types modes body) endpoint)
    (hp : ∀ v ∈ body.typeVars, PreservesBounds Δ (types v) (replacement v))
    (hf : ∀ v ∈ frozenTypes total body, replacement v = types v) :
    AlgebraSubtype Δ (publicImage replacement modes body) endpoint :=
  InDirection.replace hΔ types replacement modes total htotal body false endpoint h.wellShaped_left
    ((algebra_related hΔ h).2 _ (denote_self hc h.wellShaped_right).2) hp hf

/-- Guarded source bounds depend only on defined images. Replacing partial
images preserves every original bound when the modality action is retained. -/
theorem bounds_replacement {Δ bounds : Bounds} {original replacement : CompareSubstitution}
    (h : AlgebraEntailsAll Δ (original.bounds bounds))
    (ht : ∀ v, (original.type v).DefinedUnder Δ → replacement.type v = original.type v)
    (hm : ∀ v ∈ bounds.modVars, replacement.mode v = original.mode v) :
    AlgebraEntailsAll Δ (replacement.bounds bounds) := by
  apply (CompareSubstitution.algebra_bounds_congr replacement original bounds _ _).mpr h
  · intro c hc v hv
    have hmem := (bounds.mem_typeVars_iff v).mpr ⟨c, hc, hv⟩
    exact ht v (h.bounds_support_defined.1 v hmem)
  · intro c hc v hv
    exact hm v ((bounds.mem_modVars_iff v).mpr ⟨c, hc, hv⟩)

end ModalityInference.ComparisonPartialCarrier
