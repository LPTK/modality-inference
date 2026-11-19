import ModalityInference.Proofs.ComparisonRawHeadInterpretation

/-! Structural and lattice rules for the whole-head ideal interpretation. -/
namespace ModalityInference.ComparisonRawHeadRestriction

open ComparisonRawCarrierIdeals
open ComparisonRawCarrierRestriction (TotalIndex)

theorem Related.fn {Δ H a b c d m n}
    (hca : Related Δ H c a) (hbd : Related Δ H b d)
    (hmn : Submode Δ m (.compose n .top)) :
    Related Δ H (.modal (.fn a b) m) (.modal (.fn c d) n) := by
  intro r
  simp only [denote, Coordinate.prepend_total hmn.defined.1,
    Coordinate.prepend_total (Entails.defined_compose_iff.mp hmn.defined.2).1]
  exact ⟨fun _ hc => (indexedFnTable Δ H).lower_mono
      (m := ⟨.compose m r.val,Entails.defined_compose_iff.mpr ⟨hmn.defined.1,r.property⟩⟩)
      (n := ⟨.compose n r.val,Entails.defined_compose_iff.mpr
        ⟨(Entails.defined_compose_iff.mp hmn.defined.2).1,r.property⟩⟩)
      (FnIndexLe.postcompose hmn r.property)
      (hca ⟨.epsilon,fun _ _ => rfl⟩).2 (hbd ⟨.epsilon,fun _ _ => rfl⟩).1 hc,
    fun _ hc => (indexedFnTable Δ H).upper_mono
      (m := ⟨.compose m r.val,Entails.defined_compose_iff.mpr ⟨hmn.defined.1,r.property⟩⟩)
      (n := ⟨.compose n r.val,Entails.defined_compose_iff.mpr
        ⟨(Entails.defined_compose_iff.mp hmn.defined.2).1,r.property⟩⟩)
      (FnIndexLe.postcompose hmn r.property)
      (hca ⟨.epsilon,fun _ _ => rfl⟩).1 (hbd ⟨.epsilon,fun _ _ => rfl⟩).2 hc⟩

theorem Related.joinLeft {Δ H a b} : Related Δ H a (.join a b) :=
  fun r => ⟨fun _ h => .base ((denote Δ H a (totalCoordinate r)).lower.carrier h)
      ((denote Δ H a (totalCoordinate r)).lower.shaped h) (.inl h),
    fun _ h => h.1⟩

theorem Related.joinRight {Δ H a b} : Related Δ H b (.join a b) :=
  fun r => ⟨fun _ h => .base ((denote Δ H b (totalCoordinate r)).lower.carrier h)
      ((denote Δ H b (totalCoordinate r)).lower.shaped h) (.inr h),
    fun _ h => h.2⟩

theorem Related.meetLeft {Δ H a b} : Related Δ H (.meet a b) a :=
  fun r => ⟨fun _ h => h.1,
    fun _ h => .base ((denote Δ H a (totalCoordinate r)).upper.carrier h)
      ((denote Δ H a (totalCoordinate r)).upper.shaped h) (.inl h)⟩

theorem Related.meetRight {Δ H a b} : Related Δ H (.meet a b) b :=
  fun r => ⟨fun _ h => h.2,
    fun _ h => .base ((denote Δ H b (totalCoordinate r)).upper.carrier h)
      ((denote Δ H b (totalCoordinate r)).upper.shaped h) (.inr h)⟩

theorem Related.joinLeast {Δ H a b c} (ha : Related Δ H a c) (hb : Related Δ H b c) :
    Related Δ H (.join a b) c :=
  fun r => ⟨fun _ h => h.lift _ (denote Δ H c (totalCoordinate r)).lower
      (fun {t} ht _ _ => ht.elim ((ha r).1 t) ((hb r).1 t)),
    fun _ h => ⟨(ha r).2 _ h,(hb r).2 _ h⟩⟩

theorem Related.meetGreatest {Δ H a b c} (hb : Related Δ H a b) (hc : Related Δ H a c) :
    Related Δ H a (.meet b c) :=
  fun r => ⟨fun _ h => ⟨(hb r).1 _ h,(hc r).1 _ h⟩,
    fun _ h => h.lift _ (denote Δ H a (totalCoordinate r)).upper
      (fun {t} ht _ _ => ht.elim ((hb r).2 t) ((hc r).2 t))⟩

end ModalityInference.ComparisonRawHeadRestriction
