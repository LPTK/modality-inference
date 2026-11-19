import ModalityInference.Proofs.ComparisonRawCarrierSuffix

/-! A finite control representation may project names absent from the boundary.
Only its preservation of the original guarded control rules is required here. -/
namespace ModalityInference.ComparisonRelativeCoordinates

structure ControlMap (Δ : Bounds) (M : Type*) [PartialOrder M] [CommMonoid M]
    (future : M → M → Prop) where
  toFun : (m : ModExpr) → Entails Δ (.defined m) → M
  epsilon : toFun .epsilon (fun _ _ => rfl) = 1
  compose : ∀ m n hm hn,
    toFun (.compose m n) (Entails.defined_compose_iff.mpr ⟨hm,hn⟩) =
      toFun m hm * toFun n hn
  submode : ∀ {m n} (h : Submode Δ m n), toFun m h.defined.1 ≤ toFun n h.defined.2
  fnorder : ∀ {m n} (h : Submode Δ m (.compose n .top)),
    future (toFun m h.defined.1) (toFun n ((Entails.defined_compose_iff.mp h.defined.2).1))

end ModalityInference.ComparisonRelativeCoordinates
