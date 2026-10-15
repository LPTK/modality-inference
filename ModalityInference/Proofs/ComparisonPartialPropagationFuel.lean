import ModalityInference.ComparisonPartialPropagation

namespace ModalityInference.ComparisonPartialPropagation

theorem saturate_monotone {mode : ModExpr → ModExpr → Bool} {left right : CompareTy}
    {small large : Nat} {g : Graph} {result : Option Certificate}
    (hle : small ≤ large) (h : saturate mode left right small g = .success result) :
    saturate mode left right large g = .success result := by
  induction small generalizing large g with
  | zero => cases h
  | succ small ih =>
    cases large with
    | zero => omega
    | succ large =>
      simp only [saturate] at h ⊢
      split at h
      · next found he => simpa only [he] using h
      · next he =>
        split at h
        · next hc => simpa only [hc, ↓reduceIte] using h
        · next hc =>
          simp only [hc]
          exact ih (by omega) h

end ModalityInference.ComparisonPartialPropagation
