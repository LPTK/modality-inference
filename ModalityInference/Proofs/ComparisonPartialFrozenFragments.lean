import ModalityInference.Proofs.ComparisonPartialPublicContext

namespace ModalityInference.ComparisonPartialStructuredCapsule

/-- Possible bases obtained by removing literal root modal prefixes. -/
def modalBases (a : CompareTy) : List CompareTy :=
  a :: match a with
  | .modal b _ => modalBases b
  | _ => []

 theorem ModalPrefix.mem_modalBases {a b : CompareTy} (h : ModalPrefix a b) :
    a ∈ modalBases b := by
  induction h with
  | refl => cases a <;> exact List.mem_cons_self
  | modal h ih => exact List.mem_cons_of_mem _ ih

/-- This list depends only on the public endpoint and its inherited context. -/
def frozenFragments (endpoint : CompareTy) (suffix : Suffix) : List CompareTy :=
  (candidates endpoint suffix).flatMap fun token => modalBases token.2.1

 theorem modalBases_public {a : CompareTy} (ha : Public a) {b : CompareTy}
    (h : b ∈ modalBases a) : Public b := by
  induction a with
  | modal a m ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ha
    · exact ih ha.modal_inv h
  | _ => exact (List.mem_singleton.mp h) ▸ ha

 theorem frozenFragments_public (endpoint : Ty) (suffix : Suffix) {a : CompareTy}
    (h : a ∈ frozenFragments (.ofTy endpoint) suffix) : Public a := by
  obtain ⟨token, ht, ha⟩ := List.mem_flatMap.mp h
  exact modalBases_public (candidates_public endpoint suffix ht) ha

/-- Products and sums propagate inherited actions; every other non-modal
constructor exposes a literal frozen base when the inherited action is partial. -/
def FrozenHead : CompareTy → Prop
  | .prod _ _ | .sum _ _ | .modal _ _ => False
  | _ => True

 theorem observe_frozen {Δ : Bounds} {a : CompareTy} (ha : FrozenHead a)
    {suffix : Suffix} (hm : ¬suffix.total Δ) :
    observe Δ a suffix = literal Δ a suffix := by
  cases a <;> first | contradiction | rfl | simp only [observe, if_neg hm]

/-- A frozen base at a structured observation leaf is an actual member of the
endpoint's finite list of root-modal fragments. -/
 theorem frozen_fragment_below {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a : CompareTy} {b : Ty} {m : ModExpr} (ha : FrozenHead a)
    (hm : ¬Entails Δ (.defined m))
    (h : AlgebraSubtype Δ (.modal a m) (.ofTy b)) :
    a ∈ frozenFragments (.ofTy b) none := by
  obtain ⟨token, ht, hp⟩ := partial_token_prefix hm a
  have hs : ([], token) ∈ (observe Δ (.modal a m) none).positive := by
    change ([], token) ∈ (observe Δ a (some m)).positive
    rw [observe_frozen (suffix := some m) ha hm]
    exact ⟨token, ht, rfl⟩
  have hc := (observe_supported Δ (.ofTy b) none).1 ([], token) ((algebra_sound hΔ h).1 hs)
  exact List.mem_flatMap.mpr ⟨([], token), hc, hp.mem_modalBases⟩

 theorem frozen_fragment_above {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a : Ty} {b : CompareTy} {m : ModExpr} (hb : FrozenHead b)
    (hm : ¬Entails Δ (.defined m))
    (h : AlgebraSubtype Δ (.ofTy a) (.modal b m)) :
    b ∈ frozenFragments (.ofTy a) none := by
  obtain ⟨token, ht, hp⟩ := partial_token_prefix hm b
  have hs : ([], token) ∈ (observe Δ (.modal b m) none).negative := by
    change ([], token) ∈ (observe Δ b (some m)).negative
    rw [observe_frozen (suffix := some m) hb hm]
    exact ⟨token, ht, rfl⟩
  have hc := (observe_supported Δ (.ofTy a) none).2 ([], token) ((algebra_sound hΔ h).2 hs)
  exact List.mem_flatMap.mpr ⟨([], token), hc, hp.mem_modalBases⟩

end ModalityInference.ComparisonPartialStructuredCapsule
