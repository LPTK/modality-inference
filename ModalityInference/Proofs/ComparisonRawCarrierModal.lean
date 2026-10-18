import ModalityInference.Proofs.ComparisonPartialCarrierInterpretationModalHelpers

namespace ModalityInference.ComparisonPartialCarrier

/-- Acting on a carrier closure retains its finite family of generators. It does
not choose a single preimage or infer definedness from a raw declared edge. -/
theorem LowerClosure.modal_lift {Δ : Bounds} {S : CompareTy → Prop}
    (T : LowerIdeal Δ) {m : ModExpr} (hm : Entails Δ (.defined m))
    (hS : ∀ a, S a → T.mem (.modal a m)) {a : CompareTy}
    (h : LowerClosure Δ S a) : T.mem (.modal a m) := by
  induction h with
  | base _ _ hs => exact hS _ hs
  | lower hc hab _ ih => exact T.lower _ _ hc (.congr hab (.refl hm)) ih
  | @join a b hc _ _ iha ihb =>
    have hc' : ComparisonAlgebra.Compatible Δ (.modal a m) (.modal b m) :=
      ⟨hc.1, CompareTy.definedUnder_modal_iff.mpr ⟨hc.2.1,hm⟩,
        CompareTy.definedUnder_modal_iff.mpr ⟨hc.2.2,hm⟩⟩
    exact T.lower _ _ hc.2 (.equation (.modal true hc hm))
      (T.join _ _ hc' iha ihb)

/-- The upper dual retains finite meet families through a total action. -/
theorem UpperClosure.modal_lift {Δ : Bounds} {S : CompareTy → Prop}
    (T : UpperIdeal Δ) {m : ModExpr} (hm : Entails Δ (.defined m))
    (hS : ∀ a, S a → T.mem (.modal a m)) {a : CompareTy}
    (h : UpperClosure Δ S a) : T.mem (.modal a m) := by
  induction h with
  | base _ _ hs => exact hS _ hs
  | upper hc hab _ ih => exact T.upper _ _ hc (.congr hab (.refl hm)) ih
  | @meet a b hc _ _ iha ihb =>
    have hc' : ComparisonAlgebra.Compatible Δ (.modal a m) (.modal b m) :=
      ⟨hc.1, CompareTy.definedUnder_modal_iff.mpr ⟨hc.2.1,hm⟩,
        CompareTy.definedUnder_modal_iff.mpr ⟨hc.2.2,hm⟩⟩
    exact T.upper _ _ hc.2 (.equationRev (.modal false hc hm))
      (T.meet _ _ hc' iha ihb)


def LowerIdeal.act {Δ : Bounds} (S : LowerIdeal Δ) (m : ModExpr) : LowerIdeal Δ :=
  .closure Δ (S.modalImage m)

def UpperIdeal.act {Δ : Bounds} (S : UpperIdeal Δ) (m : ModExpr) : UpperIdeal Δ :=
  .closure Δ (S.modalImage m)

theorem LowerIdeal.act_mem {Δ : Bounds} (S : LowerIdeal Δ) (m : ModExpr) {a : CompareTy}
    (ha : S.mem a) : (S.act m).mem (.modal a m) :=
  .base (S.carrier a ha) (S.shaped a ha) ⟨a,ha,rfl⟩

theorem UpperIdeal.act_mem {Δ : Bounds} (S : UpperIdeal Δ) (m : ModExpr) {a : CompareTy}
    (ha : S.mem a) : (S.act m).mem (.modal a m) :=
  .base (S.carrier a ha) (S.shaped a ha) ⟨a,ha,rfl⟩

theorem LowerIdeal.act_identity {Δ : Bounds} (S : LowerIdeal Δ) (a : CompareTy) :
    (S.act .epsilon).mem a ↔ S.mem a := by
  constructor
  · intro h
    exact h.lift S (by
      rintro _ ⟨b,hb,rfl⟩
      exact S.lower _ _ (S.carrier b hb) (.identity (S.shaped b hb)) hb)
  · intro ha
    exact (S.act .epsilon).lower _ _ (S.carrier a ha)
      (.identityRev (S.shaped a ha)) (S.act_mem .epsilon ha)

theorem UpperIdeal.act_identity {Δ : Bounds} (S : UpperIdeal Δ) (a : CompareTy) :
    (S.act .epsilon).mem a ↔ S.mem a := by
  constructor
  · intro h
    exact h.lift S (by
      rintro _ ⟨b,hb,rfl⟩
      exact S.upper _ _ (S.carrier b hb) (.identityRev (S.shaped b hb)) hb)
  · intro ha
    exact (S.act .epsilon).upper _ _ (S.carrier a ha)
      (.identity (S.shaped a ha)) (S.act_mem .epsilon ha)

theorem LowerIdeal.act_compose {Δ : Bounds} (S : LowerIdeal Δ) {m n : ModExpr}
    (hn : Entails Δ (.defined n)) (a : CompareTy) :
    ((S.act m).act n).mem a ↔ (S.act (.compose m n)).mem a := by
  constructor
  · intro h
    apply h.lift (S.act (.compose m n))
    rintro _ ⟨x,hx,rfl⟩
    apply LowerClosure.modal_lift (S.act (.compose m n)) hn ?_ hx
    rintro _ ⟨b,hb,rfl⟩
    exact (S.act (.compose m n)).lower _ _ (S.carrier b hb)
      (.compose (S.shaped b hb)) (S.act_mem (.compose m n) hb)
  · intro h
    apply h.lift ((S.act m).act n)
    rintro _ ⟨b,hb,rfl⟩
    exact ((S.act m).act n).lower _ _ (S.carrier b hb)
      (.composeRev (S.shaped b hb)) ((S.act m).act_mem n (S.act_mem m hb))

theorem UpperIdeal.act_compose {Δ : Bounds} (S : UpperIdeal Δ) {m n : ModExpr}
    (hn : Entails Δ (.defined n)) (a : CompareTy) :
    ((S.act m).act n).mem a ↔ (S.act (.compose m n)).mem a := by
  constructor
  · intro h
    apply h.lift (S.act (.compose m n))
    rintro _ ⟨x,hx,rfl⟩
    apply UpperClosure.modal_lift (S.act (.compose m n)) hn ?_ hx
    rintro _ ⟨b,hb,rfl⟩
    exact (S.act (.compose m n)).upper _ _ (S.carrier b hb)
      (.composeRev (S.shaped b hb)) (S.act_mem (.compose m n) hb)
  · intro h
    apply h.lift ((S.act m).act n)
    rintro _ ⟨b,hb,rfl⟩
    exact ((S.act m).act n).upper _ _ (S.carrier b hb)
      (.compose (S.shaped b hb)) ((S.act m).act_mem n (S.act_mem m hb))


noncomputable section
attribute [local instance] Classical.propDecidable

theorem Related.identity_general {Δ : Bounds} (a : CompareTy) :
    Related Δ (.modal a .epsilon) a ∧ Related Δ a (.modal a .epsilon) := by
  have he : Entails Δ (.defined .epsilon) := by intro _ _; rfl
  constructor <;> constructor
  · intro c hc
    exact ((denote Δ a).lower.act_identity c).mp (by simpa only [denote,if_pos he] using hc)
  · intro c hc
    simpa only [denote,if_pos he] using ((denote Δ a).upper.act_identity c).mpr hc
  · intro c hc
    simpa only [denote,if_pos he] using ((denote Δ a).lower.act_identity c).mpr hc
  · intro c hc
    exact ((denote Δ a).upper.act_identity c).mp (by simpa only [denote,if_pos he] using hc)

theorem Related.compose_total_general {Δ : Bounds} (a : CompareTy) {m n : ModExpr}
    (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n)) :
    Related Δ (.modal (.modal a m) n) (.modal a (.compose m n)) ∧
      Related Δ (.modal a (.compose m n)) (.modal (.modal a m) n) := by
  have hmn := Entails.defined_compose_iff.mpr ⟨hm,hn⟩
  have hlo (c : CompareTy) :
      (denote Δ (.modal (.modal a m) n)).lower.mem c ↔
        (denote Δ (.modal a (.compose m n))).lower.mem c := by
    simpa only [denote,if_pos hm,if_pos hn,if_pos hmn,LowerIdeal.act] using
      (denote Δ a).lower.act_compose (m := m) hn c
  have hhi (c : CompareTy) :
      (denote Δ (.modal (.modal a m) n)).upper.mem c ↔
        (denote Δ (.modal a (.compose m n))).upper.mem c := by
    simpa only [denote,if_pos hm,if_pos hn,if_pos hmn,UpperIdeal.act] using
      (denote Δ a).upper.act_compose (m := m) hn c
  exact ⟨⟨fun c => (hlo c).mp,fun c => (hhi c).mpr⟩,
    ⟨fun c => (hlo c).mpr,fun c => (hhi c).mp⟩⟩

/-- Literal composition is exact even when its factors are partial and declared
edges connect partial and defined endpoints. -/
theorem Related.compose_general {Δ : Bounds} {a : CompareTy}
    (hs : a.WellShaped Δ) (m n : ModExpr) :
    Related Δ (.modal (.modal a m) n) (.modal a (.compose m n)) ∧
      Related Δ (.modal a (.compose m n)) (.modal (.modal a m) n) := by
  by_cases ha : Carrier Δ a
  · exact ⟨Related.carriers ha ha (.compose hs),Related.carriers ha ha (.composeRev hs)⟩
  by_cases hmn : Entails Δ (.defined m) ∧ Entails Δ (.defined n)
  · exact Related.compose_total_general a hmn.1 hmn.2
  have hc : ¬Entails Δ (.defined (.compose m n)) := fun h =>
    hmn (Entails.defined_compose_iff.mp h)
  have hnlo : ∀ c, (denote Δ (.modal (.modal a m) n)).lower.mem c → False := by
    intro c h
    by_cases hn : Entails Δ (.defined n)
    · have hm : ¬Entails Δ (.defined m) := fun hm => hmn ⟨hm,hn⟩
      simp only [denote,if_pos hn] at h
      obtain ⟨_,b,hb,_⟩ := h.exists_base
      exact ha (denote_partial_lower_carrier hm hb)
    · exact ha (denote_partial_lower_carrier (a := .modal a m) hn h)
  have hnhi : ∀ c, (denote Δ (.modal (.modal a m) n)).upper.mem c → False := by
    intro c h
    by_cases hn : Entails Δ (.defined n)
    · have hm : ¬Entails Δ (.defined m) := fun hm => hmn ⟨hm,hn⟩
      simp only [denote,if_pos hn] at h
      obtain ⟨_,b,hb,_⟩ := h.exists_base
      exact ha (denote_partial_upper_carrier hm hb)
    · exact ha (denote_partial_upper_carrier (a := .modal a m) hn h)
  exact ⟨⟨fun c h => False.elim (hnlo c h),
      fun _ h => False.elim (ha (denote_partial_upper_carrier hc h))⟩,
    ⟨fun _ h => False.elim (ha (denote_partial_lower_carrier hc h)),
      fun c h => False.elim (hnhi c h)⟩⟩

end
end ModalityInference.ComparisonPartialCarrier
