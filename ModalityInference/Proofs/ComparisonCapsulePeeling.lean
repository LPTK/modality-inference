import ModalityInference.Proofs.ComparisonPartialCapsuleProjection
import ModalityInference.Proofs.ComparisonCapsuleIntervals

namespace ModalityInference.ComparisonCapsuleIntervals

open ComparisonBody ComparisonPartialModes ComparisonPartialCapsule
open ComparisonPartialCapsuleScalar

/-- Root composition and identity steps have been exhausted. -/
def OuterNormal : Ty → Prop
  | .modal _ m => m ≠ .epsilon ∧ ∀ p q, m ≠ .compose p q
  | _ => True

theorem normalizeOuterFuel_normal (fuel : Nat) (t : Ty)
    (h : modalitySize t ≤ fuel) : OuterNormal (normalizeOuterFuel fuel t) := by
  induction fuel generalizing t with
  | zero =>
    cases t <;> simp only [modalitySize, normalizeOuterFuel, OuterNormal] at h ⊢
    case modal a m => have := mode_size_pos m; omega
  | succ fuel ih =>
    cases t with
    | modal a m =>
      cases m
      case compose m n =>
        apply ih
        simp only [modalitySize, expressionSize] at h ⊢
        omega
      all_goals
        simp only [normalizeOuterFuel]
        split_ifs with he
        · apply ih
          simp only [modalitySize, expressionSize] at h
          omega
        · exact ⟨by simpa only [beq_iff_eq] using he, by simp⟩
    | _ => trivial

theorem normalizeOuterFuel_size (fuel : Nat) (t : Ty) :
    traversalSize (normalizeOuterFuel fuel t) ≤ traversalSize t := by
  induction fuel generalizing t with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    cases t with
    | modal a m =>
      cases m
      case compose m n =>
        simpa only [normalizeOuterFuel, traversalSize, expressionSize, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using ih (.modal (.modal a m) n)
      all_goals
        simp only [normalizeOuterFuel]
        split_ifs
        · exact (ih a).trans (by simp only [traversalSize]; omega)
        · exact Nat.le_refl _
    | _ => exact Nat.le_refl _

def Stopped (total : ModExpr → Bool) (t : Ty) : Prop :=
  OuterNormal t ∧ match t with | .modal _ m => total m = false | _ => True

theorem peelFuel_stopped (total : ModExpr → Bool) (fuel : Nat) (t : Ty)
    (h : traversalSize t < fuel) : Stopped total (peelFuel total fuel t).base := by
  induction fuel generalizing t with
  | zero => omega
  | succ fuel ih =>
    have hn := normalizeOuterFuel_normal (modalitySize t) t (Nat.le_refl _)
    have hs := normalizeOuterFuel_size (modalitySize t) t
    change OuterNormal (normalizeOuter t) at hn
    change traversalSize (normalizeOuter t) ≤ traversalSize t at hs
    cases he : normalizeOuter t <;> simp only [peelFuel, he]
    all_goals try exact ⟨trivial, trivial⟩
    case modal a m =>
      split
      · apply ih
        rw [he] at hs
        simp only [traversalSize] at hs
        omega
      · next hm =>
        exact ⟨he ▸ hn, by simpa only [Bool.not_eq_true] using hm⟩

theorem peel_stopped (total : ModExpr → Bool) (t : Ty) : Stopped total (peel total t).base :=
  peelFuel_stopped total _ t (Nat.lt_succ_self _)

theorem peelFuel_labels_total (total : ModExpr → Bool) (fuel : Nat) (t : Ty) :
    ∀ m ∈ (peelFuel total fuel t).labels, total m = true := by
  induction fuel generalizing t with
  | zero => simp [peelFuel]
  | succ fuel ih =>
    cases he : normalizeOuter t <;> simp only [peelFuel, he]
    all_goals try simp
    split
    · next hm => simpa using And.intro hm (ih _)
    · simp


theorem recompose_total {Δ : Bounds} (ms : List ModExpr)
    (h : ∀ m ∈ ms, Entails Δ (.defined m)) : Entails Δ (.defined (recompose ms)) := by
  match ms with
  | [] => exact fun _ _ => rfl
  | [m] => exact h m List.mem_cons_self
  | m :: n :: rest =>
    apply recompose_total (.compose n m :: rest)
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Entails.defined_compose_iff.mpr
        ⟨h n (by simp), h m List.mem_cons_self⟩
    · exact h p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))
termination_by ms.length

structure ParsedNormal (Δ : Bounds) (total : ModExpr → Bool) (t : Ty) where
  normal : Normal Δ (.ofTy t)
  base_eq : CompareTy.ofTy (peel total t).base = .modal normal.token.1 normal.token.2
  suffix_eq : normal.suffix = recompose (peel total t).labels

theorem peel_normal {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    (total : ModExpr → Bool)
    (hsound : ∀ m, total m = true → Entails Δ (.defined m))
    (t : Ty) (ht : Atomic ((CompareTy.ofTy t).shape.subst ρ))
    (hpartial : ¬(CompareTy.ofTy t).DefinedUnder Δ)
    (hcomplete : ∀ a m, (peel total t).base = .modal a m →
      Entails Δ (.defined m) → total m = true) : Nonempty (ParsedNormal Δ total t) := by
  let p := peel total t
  have hlabels : Entails Δ (.defined (recompose p.labels)) :=
    recompose_total _ (fun m hm => hsound m (peelFuel_labels_total total _ t m hm))
  have hp := peel_correct total (fun m hm => Submode.refl (hsound m hm)) t
  change Subtype Δ t (.modal p.base (recompose p.labels)) ∧
    Subtype Δ (.modal p.base (recompose p.labels)) t at hp
  have hshape := hp.1.to_shaped.shape_equivalent ρ hρ
  change (CompareTy.ofTy t).shape.subst ρ = (CompareTy.ofTy p.base).shape.subst ρ at hshape
  have hbaseAtom : Atomic ((CompareTy.ofTy p.base).shape.subst ρ) := hshape ▸ ht
  have hbasePartial : ¬(CompareTy.ofTy p.base).DefinedUnder Δ := by
    intro hd
    apply hpartial
    exact (ComparisonPartialCarrier.Carrier.of_public t).defined_of_below hΔ
      (CompareTy.definedUnder_modal_iff.mpr ⟨hd, hlabels⟩) (.shaped hp.1.to_shaped)
  have hstop := peel_stopped total t
  change Stopped total p.base at hstop
  cases hb : p.base with
  | var | unit | credit =>
    rw [hb] at hbasePartial
    exact False.elim (hbasePartial (by
      simp [CompareTy.ofTy, CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels]))
  | prod | sum | fn => rw [hb] at hbaseAtom; exact False.elim hbaseAtom
  | modal a m =>
    rw [hb] at hstop
    have hf : Frozen Δ (CompareTy.ofTy a, m) :=
      ⟨fun hd => Bool.false_ne_true (hstop.2.symm.trans (hcomplete a m hb hd)), hstop.1.2⟩
    have hforward := hp.1.to_shaped
    have hback := hp.2.to_shaped
    rw [hb] at hforward hback
    have hlo := ComparisonPartialCapsule.algebra_sound hΔ hρ (.shaped hforward) ht
    have hhi := ComparisonPartialCapsule.algebra_sound hΔ hρ (.shaped hback)
      (show Atomic ((CompareTy.ofTy (.modal (.modal a m) (recompose p.labels))).shape.subst ρ)
        from hb ▸ hbaseAtom)
    change observe Δ (CompareTy.ofTy t) ⊆
      observe Δ (.modal (.modal (CompareTy.ofTy a) m) (recompose p.labels)) at hlo
    change observe Δ (.modal (.modal (CompareTy.ofTy a) m) (recompose p.labels)) ⊆
      observe Δ (CompareTy.ofTy t) at hhi
    rw [observe_modal_total hlabels, frozen_observation hf] at hlo hhi
    refine ⟨⟨⟨(CompareTy.ofTy a, m), recompose p.labels,
      Set.Subset.antisymm hlo hhi, hlabels, hforward, hback⟩, ?_, rfl⟩⟩
    change CompareTy.ofTy p.base = .modal (CompareTy.ofTy a) m
    rw [hb]
    rfl

end ModalityInference.ComparisonCapsuleIntervals
