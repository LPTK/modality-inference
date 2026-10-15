import ModalityInference.Proofs.ComparisonDefinedCoverOrder

/-!
# Defined boundary covers

Defined approximations preserve the comparison order. They consequently extract
defined lower and upper covers whenever a comparison reaches a defined boundary,
including through total modality actions.
-/

namespace ModalityInference.ComparisonDefinedCovers

noncomputable section

attribute [local instance] Classical.propDecidable

theorem CoverLe.modal_strict_mono {Δ lower a b c d m}
    {op : CompareTy → CompareTy → CompareTy}
    (h : ∀ {w x y z}, AlgebraSubtype Δ (.modal w m) (.modal y m) →
      AlgebraSubtype Δ (.modal x m) (.modal z m) →
      AlgebraSubtype Δ (.modal (op w x) m) (.modal (op y z) m))
    (ha : CoverLe Δ lower (a.map (CompareTy.modal · m)) (c.map (CompareTy.modal · m)))
    (hb : CoverLe Δ lower (b.map (CompareTy.modal · m)) (d.map (CompareTy.modal · m))) :
    CoverLe Δ lower ((strict op a b).map (CompareTy.modal · m))
      ((strict op c d).map (CompareTy.modal · m)) := by
  cases lower <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [CoverLe, strict]

theorem CoverLe.modal_fn {Δ lower a b c d m n}
    (ha : CoverLe Δ (!lower) c a) (hb : CoverLe Δ lower b d)
    (hm : Submode Δ m (.compose n .top)) :
    CoverLe Δ lower ((strict .fn a b).map (CompareTy.modal · m))
      ((strict .fn c d).map (CompareTy.modal · n)) := by
  cases lower <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [CoverLe, strict]
  all_goals exact AlgebraSubtype.fn ha hb hm

theorem normal_identity {Δ : Bounds} {a : CompareTy} (ha : a.WellShaped Δ) (lower : Bool) :
    CoverLe Δ lower (normal Δ lower (.modal a .epsilon)) (normal Δ lower a) ∧
      CoverLe Δ lower (normal Δ lower a) (normal Δ lower (.modal a .epsilon)) := by
  have he : Entails Δ (.defined .epsilon) := by intro η _; rfl
  simp only [normal, if_pos he]
  cases hx : normal Δ lower a with
  | none => exact ⟨trivial, trivial⟩
  | some x =>
    have hs := (normal_sound ha lower hx).2.shape.1
    exact ⟨AlgebraSubtype.identity hs, AlgebraSubtype.identityRev hs⟩

theorem normal_compose {Δ : Bounds} {a : CompareTy} (ha : a.WellShaped Δ)
    (lower : Bool) (m n : ModExpr) :
    CoverLe Δ lower (normal Δ lower (.modal (.modal a m) n))
        (normal Δ lower (.modal a (.compose m n))) ∧
      CoverLe Δ lower (normal Δ lower (.modal a (.compose m n)))
        (normal Δ lower (.modal (.modal a m) n)) := by
  by_cases hmn : Entails Δ (.defined (.compose m n))
  · obtain ⟨hm, hn⟩ := Entails.defined_compose_iff.mp hmn
    simp only [normal, if_pos hm, if_pos hn, if_pos hmn]
    cases hx : normal Δ lower a with
    | none => exact ⟨trivial, trivial⟩
    | some x =>
      have hs := (normal_sound ha lower hx).2.shape.1
      exact ⟨AlgebraSubtype.compose hs, AlgebraSubtype.composeRev hs⟩
  · by_cases hn : Entails Δ (.defined n)
    · have hm : ¬ Entails Δ (.defined m) := fun hm =>
        hmn (Entails.defined_compose_iff.mpr ⟨hm, hn⟩)
      simp [normal, hn, hm, hmn, CoverLe]
    · simp [normal, hn, hmn, CoverLe]

theorem shaped_normal_monotone {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) {a b : CompareTy}
    (h : ShapedSubtype Δ a b) : ∀ lower, CoverLe Δ lower (normal Δ lower a) (normal Δ lower b) := by
  induction h
  case fn a b c d m n hca hbd hm ihca ihbd =>
    intro lower
    have hn := (Entails.defined_compose_iff.mp hm.defined.2).1
    simpa only [normal, if_pos hm.defined.1, if_pos hn] using
      CoverLe.modal_fn (ihca (!lower)) (ihbd lower) hm
  case prod a b c d m hac hbd ihac ihbd =>
    intro lower
    by_cases hm : Entails Δ (.defined m)
    · have ha := ihac lower
      have hb := ihbd lower
      simp only [normal, if_pos hm] at ha hb ⊢
      exact CoverLe.modal_strict_mono AlgebraSubtype.prod ha hb
    · simp [normal, hm, CoverLe]
  case sum a b c d m hac hbd ihac ihbd =>
    intro lower
    by_cases hm : Entails Δ (.defined m)
    · have ha := ihac lower
      have hb := ihbd lower
      simp only [normal, if_pos hm] at ha hb ⊢
      exact CoverLe.modal_strict_mono AlgebraSubtype.sum ha hb
    · simp [normal, hm, CoverLe]
  case refl a ha => exact fun lower => CoverLe.refl lower (OfShape.normal ha lower)
  case trans hab hbc ihab ihbc => exact fun lower => (ihab lower).trans (ihbc lower)
  case bound a b hab =>
    intro lower
    rw [normal_defined ((CompareTy.definedUnder_ofTy _ _).mpr (hΔ a b hab).1),
      normal_defined ((CompareTy.definedUnder_ofTy _ _).mpr (hΔ a b hab).2)]
    exact AlgebraSubtype.shaped (.bound hab)
  case identity a ha => exact fun lower => (normal_identity ha lower).1
  case identityRev a ha => exact fun lower => (normal_identity ha lower).2
  case compose a m n ha => exact fun lower => (normal_compose ha lower m n).1
  case composeRev a m n ha => exact fun lower => (normal_compose ha lower m n).2
  case congr hab hm ih =>
    intro lower
    simpa only [normal, if_pos hm.defined.1, if_pos hm.defined.2] using (ih lower).modal hm
  case joinLeft a b hab =>
    intro lower
    exact CoverLe.join_left (OfShape.normal hab.1 lower)
      ((OfShape.normal hab.2.1 lower).rebase hab.2.2.symm)
  case joinRight a b hab =>
    intro lower
    exact CoverLe.join_right (OfShape.normal hab.1 lower)
      ((OfShape.normal hab.2.1 lower).rebase hab.2.2.symm)
  case joinLeast hac hbc ihac ihbc =>
    exact fun lower => (ihac lower).join_least (ihbc lower)
  case meetLeft a b hab =>
    intro lower
    exact CoverLe.meet_left (OfShape.normal hab.1 lower)
      ((OfShape.normal hab.2.1 lower).rebase hab.2.2.symm)
  case meetRight a b hab =>
    intro lower
    exact CoverLe.meet_right (OfShape.normal hab.1 lower)
      ((OfShape.normal hab.2.1 lower).rebase hab.2.2.symm)
  case meetGreatest hab hac ihab ihac =>
    exact fun lower => (ihab lower).meet_greatest (ihac lower)

theorem normal_defined_mono {Δ : Bounds} {a b : CompareTy}
    (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) (h : AlgebraSubtype Δ a b)
    (lower : Bool) : CoverLe Δ lower (normal Δ lower a) (normal Δ lower b) := by
  rw [normal_defined ha, normal_defined hb]
  exact h

theorem clamp_endpoints_defined {Δ : Bounds} {b a t : CompareTy} {m : ModExpr}
    (hba : ComparisonAlgebra.Compatible Δ b a) (hat : ComparisonAlgebra.Compatible Δ a t)
    (hm : Entails Δ (.defined m)) :
    (.modal a m : CompareTy).DefinedUnder Δ ∧
      (.meet (.join a (.modal b m)) (.modal t m) : CompareTy).DefinedUnder Δ := by
  simp only [CompareTy.definedUnder_modal_iff, CompareTy.definedUnder_meet_iff,
    CompareTy.definedUnder_join_iff]
  exact ⟨⟨hba.2.2, hm⟩, ⟨hba.2.2, hba.2.1, hm⟩, hat.2.2, hm⟩

theorem normal_monotone {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) {a b : CompareTy}
    (h : AlgebraSubtype Δ a b) : ∀ lower, CoverLe Δ lower (normal Δ lower a) (normal Δ lower b) := by
  induction h
  case shaped h => exact shaped_normal_monotone hΔ h
  case trans hab hbc ihab ihbc => exact fun lower => (ihab lower).trans (ihbc lower)
  case equation h => exact normal_defined_mono (equation_defined h).1 (equation_defined h).2 (.equation h)
  case equationRev h => exact normal_defined_mono (equation_defined h).2 (equation_defined h).1 (.equationRev h)
  case congr hab hm ih =>
    intro lower
    simpa only [normal, if_pos hm.defined.1, if_pos hm.defined.2] using (ih lower).modal hm
  case prod a b c d m hac hbd ihac ihbd =>
    intro lower
    by_cases hm : Entails Δ (.defined m)
    · have ha := ihac lower
      have hb := ihbd lower
      simp only [normal, if_pos hm] at ha hb ⊢
      exact CoverLe.modal_strict_mono AlgebraSubtype.prod ha hb
    · simp [normal, hm, CoverLe]
  case sum a b c d m hac hbd ihac ihbd =>
    intro lower
    by_cases hm : Entails Δ (.defined m)
    · have ha := ihac lower
      have hb := ihbd lower
      simp only [normal, if_pos hm] at ha hb ⊢
      exact CoverLe.modal_strict_mono AlgebraSubtype.sum ha hb
    · simp [normal, hm, CoverLe]
  case fn a b c d m n hca hbd hm ihca ihbd =>
    intro lower
    have hn := (Entails.defined_compose_iff.mp hm.defined.2).1
    simpa only [normal, if_pos hm.defined.1, if_pos hn] using
      CoverLe.modal_fn (ihca (!lower)) (ihbd lower) hm
  case joinLeast hac hbc ihac ihbc =>
    exact fun lower => (ihac lower).join_least (ihbc lower)
  case meetGreatest hab hac ihab ihac =>
    exact fun lower => (ihab lower).meet_greatest (ihac lower)
  case clamp b a t m hba hat hm h₁ h₂ ih₁ ih₂ =>
    have hd := clamp_endpoints_defined hba hat hm
    exact normal_defined_mono hd.1 hd.2 (.clamp hba hat hm h₁ h₂)
  case clampRev b a t m hba hat hm h₁ h₂ ih₁ ih₂ =>
    have hd := clamp_endpoints_defined hba hat hm
    exact normal_defined_mono hd.2 hd.1 (.clampRev hba hat hm h₁ h₂)

theorem defined_lower_cover {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) {a b : CompareTy}
    (ha : a.DefinedUnder Δ) (h : AlgebraSubtype Δ a b) :
    ∃ c, normal Δ true b = some c ∧ c.DefinedUnder Δ ∧
      AlgebraSubtype Δ a c ∧ AlgebraSubtype Δ c b := by
  have hm := normal_monotone hΔ h true
  rw [normal_defined ha] at hm
  cases hc : normal Δ true b with
  | none => simp [hc, CoverLe] at hm
  | some c =>
    have hs := normal_sound h.wellShaped_right true hc
    exact ⟨c, rfl, hs.1, by simpa only [hc, CoverLe] using hm, hs.2⟩

theorem defined_upper_cover {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) {a b : CompareTy}
    (hb : b.DefinedUnder Δ) (h : AlgebraSubtype Δ a b) :
    ∃ c, normal Δ false a = some c ∧ c.DefinedUnder Δ ∧
      AlgebraSubtype Δ a c ∧ AlgebraSubtype Δ c b := by
  have hm := normal_monotone hΔ h false
  rw [normal_defined hb] at hm
  cases hc : normal Δ false a with
  | none => simp [hc, CoverLe] at hm
  | some c =>
    have hs := normal_sound h.wellShaped_left false hc
    exact ⟨c, rfl, hs.1, hs.2, by simpa only [hc, CoverLe] using hm⟩

theorem defined_lower_modal_cover {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a b : CompareTy} {m : ModExpr} (ha : a.DefinedUnder Δ)
    (h : AlgebraSubtype Δ a (.modal b m)) :
    Entails Δ (.defined m) ∧ ∃ c, normal Δ true b = some c ∧ c.DefinedUnder Δ ∧
      AlgebraSubtype Δ c b ∧ AlgebraSubtype Δ a (.modal c m) := by
  have hp := normal_monotone hΔ h true
  rw [normal_defined ha] at hp
  by_cases hm : Entails Δ (.defined m)
  · refine ⟨hm, ?_⟩
    cases hc : normal Δ true b with
    | none => simp [normal, hm, hc, CoverLe] at hp
    | some c =>
      have hs := normal_sound (a := b) h.wellShaped_right true hc
      exact ⟨c, rfl, hs.1, hs.2, by simpa only [normal, if_pos hm, hc, Option.map_some, CoverLe] using hp⟩
  · simp [normal, hm, CoverLe] at hp

theorem defined_upper_modal_cover {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a b : CompareTy} {m : ModExpr} (hb : b.DefinedUnder Δ)
    (h : AlgebraSubtype Δ (.modal a m) b) :
    Entails Δ (.defined m) ∧ ∃ c, normal Δ false a = some c ∧ c.DefinedUnder Δ ∧
      AlgebraSubtype Δ a c ∧ AlgebraSubtype Δ (.modal c m) b := by
  have hp := normal_monotone hΔ h false
  rw [normal_defined hb] at hp
  by_cases hm : Entails Δ (.defined m)
  · refine ⟨hm, ?_⟩
    cases hc : normal Δ false a with
    | none => simp [normal, hm, hc, CoverLe] at hp
    | some c =>
      have hs := normal_sound (a := a) h.wellShaped_left false hc
      exact ⟨c, rfl, hs.1, hs.2, by simpa only [normal, if_pos hm, hc, Option.map_some, CoverLe] using hp⟩
  · simp [normal, hm, CoverLe] at hp

end
end ModalityInference.ComparisonDefinedCovers
