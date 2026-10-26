import ModalityInference.ComparisonSuffixSyntax
import ModalityInference.Proofs.ComparisonRawHeadSupport

/-! A modal suffix consists of an exact literal partial prefix followed by a
total control. Only the trailing total part is combined; the tree below a
partial action is never flattened or reassociated. -/
namespace ModalityInference.ComparisonRawCarrierSuffix

open ComparisonRawCarrierRestriction

noncomputable section
attribute [local instance] Classical.propDecidable

def normalize (Δ : Bounds) (m : ModExpr) : Normalized :=
  if Entails Δ (.defined m) then ⟨none,m⟩ else
    match m with
    | .compose l r =>
        match (normalize Δ r).literal with
        | some p => ⟨some (.compose l p), (normalize Δ r).control⟩
        | none => ⟨(normalize Δ l).literal,
            .compose (normalize Δ l).control (normalize Δ r).control⟩
    | m => ⟨some m,.epsilon⟩

theorem normalize_total {Δ m} (hm : Entails Δ (.defined m)) :
    normalize Δ m = ⟨none,m⟩ := by
  cases m <;> simp only [normalize, if_pos hm]

theorem control_total (Δ : Bounds) (m : ModExpr) :
    Entails Δ (.defined (normalize Δ m).control) := by
  induction m with
  | compose l r hl hr =>
    by_cases h : Entails Δ (.defined (.compose l r))
    · simpa only [normalize_total h] using h
    · cases hp : (normalize Δ r).literal with
      | none => simpa only [normalize, if_neg h, hp] using
          Entails.defined_compose_iff.mpr ⟨hl,hr⟩
      | some p => simpa only [normalize, if_neg h, hp] using hr
  | _ =>
    simp only [normalize]
    split
    · assumption
    · exact fun _ _ => rfl

theorem normalize_append {Δ m n} (hn : Entails Δ (.defined n)) :
    normalize Δ (.compose m n) =
      ⟨(normalize Δ m).literal, .compose (normalize Δ m).control n⟩ := by
  by_cases hm : Entails Δ (.defined m)
  · rw [normalize_total (Entails.defined_compose_iff.mpr ⟨hm,hn⟩), normalize_total hm]
  · have hmn : ¬Entails Δ (.defined (.compose m n)) :=
      fun h => hm (Entails.defined_compose_iff.mp h).1
    rw [normalize, if_neg hmn, normalize_total hn]

theorem literal_none_iff (Δ : Bounds) (m : ModExpr) :
    (normalize Δ m).literal = none ↔ Entails Δ (.defined m) := by
  induction m with
  | compose l r hl hr =>
    by_cases h : Entails Δ (.defined (.compose l r))
    · simp only [normalize_total h, h]
    · cases hp : (normalize Δ r).literal with
      | none =>
        have hnl : ¬Entails Δ (.defined l) :=
          fun h₁ => h (Entails.defined_compose_iff.mpr ⟨h₁,hr.mp hp⟩)
        simp [normalize, h, hp, hl, hnl]
      | some p => simp [normalize, h, hp]
  | _ =>
    simp only [normalize]
    split <;> simp_all

theorem support_literal (Δ : Bounds) (m : ModExpr) (a : CompareTy) :
    support Δ (.modal a m) none = support Δ (prefixApply (normalize Δ m).literal a) none := by
  induction m generalizing a with
  | compose l r hl hr =>
    by_cases h : Entails Δ (.defined (.compose l r))
    · rw [normalize_total h]
      exact support_modal_total h a
    · cases hp : (normalize Δ r).literal with
      | none =>
        rw [support_compose, hr]
        simpa only [normalize, if_neg h, hp, prefixApply] using hl a
      | some p =>
        rw [support_compose, hr]
        simp only [normalize, if_neg h, hp, prefixApply]
        exact (support_compose Δ a l p).symm
  | _ =>
    simp only [normalize]
    split
    · exact support_modal_total ‹_› a
    · rfl

theorem literal_partial {Δ m p} (hp : (normalize Δ m).literal = some p) :
    ¬Entails Δ (.defined p) := by
  induction m generalizing p with
  | compose l r hl hr =>
    by_cases h : Entails Δ (.defined (.compose l r))
    · simp only [normalize_total h] at hp
      cases hp
    · cases hpr : (normalize Δ r).literal with
      | none =>
        simp only [normalize, if_neg h, hpr] at hp
        exact hl hp
      | some q =>
        simp only [normalize, if_neg h, hpr, Option.some.injEq] at hp
        subst p
        exact fun he => hr hpr (Entails.defined_compose_iff.mp he).2
  | _ =>
    simp only [normalize] at hp
    split at hp
    · cases hp
    · cases Option.some.inj hp
      assumption

def Normalized.prepend (Δ : Bounds) (m : ModExpr) (s : Normalized) : Normalized :=
  match s.literal with
  | some p => ⟨some (.compose m p), s.control⟩
  | none => ⟨(normalize Δ m).literal, .compose (normalize Δ m).control s.control⟩

theorem normalize_compose (Δ : Bounds) (m n : ModExpr) :
    normalize Δ (.compose m n) = (normalize Δ n).prepend Δ m := by
  by_cases h : Entails Δ (.defined (.compose m n))
  · obtain ⟨hm,hn⟩ := Entails.defined_compose_iff.mp h
    simp only [normalize_total h, normalize_total hm, normalize_total hn, Normalized.prepend]
  · rw [normalize, if_neg h]
    rfl

theorem Normalized.prepend_control_total {Δ} {s : Normalized} (hs : Entails Δ (.defined s.control))
    (m : ModExpr) : Entails Δ (.defined (s.prepend Δ m).control) := by
  cases hp : s.literal with
  | none => exact Entails.defined_compose_iff.mpr ⟨control_total Δ m,hs⟩
      |> (by simpa only [Normalized.prepend, hp] using ·)
  | some p => simpa only [Normalized.prepend, hp] using hs

theorem Normalized.prepend_literal_partial {Δ} {s : Normalized}
    (hs : ∀ p, s.literal = some p → ¬Entails Δ (.defined p)) (m : ModExpr) :
    ∀ p, (s.prepend Δ m).literal = some p → ¬Entails Δ (.defined p) := by
  intro p hp
  cases hsp : s.literal with
  | none => exact literal_partial (by simpa only [Normalized.prepend, hsp] using hp)
  | some q =>
    simp only [Normalized.prepend, hsp, Option.some.injEq] at hp
    subst p
    exact fun h => hs q hsp (Entails.defined_compose_iff.mp h).2

def Normalized.Below (Δ : Bounds) (s t : Normalized) : Prop :=
  s.literal = t.literal ∧ Submode Δ s.control t.control

theorem Normalized.Below.prepend {Δ s t} (h : Normalized.Below Δ s t) (m : ModExpr) :
    Normalized.Below Δ (s.prepend Δ m) (t.prepend Δ m) := by
  cases hp : t.literal with
  | some p => simpa only [Normalized.Below, Normalized.prepend, h.1, hp, true_and] using h.2
  | none =>
    simp only [Normalized.Below, Normalized.prepend, h.1, hp, true_and]
    apply Submode.valid
    intro η hη
    obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp (control_total Δ m η hη)
    obtain ⟨y,z,hy,hz,hyz⟩ := h.2.denote hη
    exact ⟨x.compose y,x.compose z,by simp [ModExpr.eval,hx,hy],
      by simp [ModExpr.eval,hx,hz], Mode.compose_le_left x hyz⟩

theorem append_below {Δ p m n} (h : Submode Δ m n) :
    Normalized.Below Δ (normalize Δ (.compose p m)) (normalize Δ (.compose p n)) := by
  rw [normalize_compose, normalize_compose, normalize_total h.defined.1,
    normalize_total h.defined.2]
  exact Normalized.Below.prepend (s := ⟨none,m⟩) (t := ⟨none,n⟩) ⟨rfl,h⟩ p

def HeadEquivalent (Δ : Bounds) (H : Set CompareTy) (a b : CompareTy) : Prop :=
  ComparisonRawHeadRestriction.Derivation Δ H a b ∧
    ComparisonRawHeadRestriction.Derivation Δ H b a

theorem HeadEquivalent.refl {Δ H a} (hc : ComparisonRawHeadRestriction.Carrier Δ H a)
    (hs : a.WellShaped Δ) : HeadEquivalent Δ H a a :=
  ⟨.atom hc hc (.refl hs),.atom hc hc (.refl hs)⟩

theorem HeadEquivalent.symm {Δ H a b} (h : HeadEquivalent Δ H a b) :
    HeadEquivalent Δ H b a := ⟨h.2,h.1⟩

theorem HeadEquivalent.trans {Δ H a b c} (h : HeadEquivalent Δ H a b)
    (g : HeadEquivalent Δ H b c) : HeadEquivalent Δ H a c :=
  ⟨h.1.trans g.1,g.2.trans h.2⟩

theorem HeadEquivalent.modal {Δ H a b p q m}
    (h : HeadEquivalent Δ H (.modal a p) (.modal b q))
    (hm : Entails Δ (.defined m)) :
    HeadEquivalent Δ H (.modal (.modal a p) m) (.modal (.modal b q) m) :=
  let ha := (ComparisonRawHeadRestriction.carrier_modal_outer_total hm).mpr h.1.carriers.1
  let hb := (ComparisonRawHeadRestriction.carrier_modal_outer_total hm).mpr h.1.carriers.2
  ⟨h.1.congr (.refl hm) ha hb,h.2.congr (.refl hm) hb ha⟩

theorem HeadEquivalent.identity {Δ H a} (hc : ComparisonRawHeadRestriction.Generator Δ H a)
    (hs : a.WellShaped Δ) : HeadEquivalent Δ H a (.modal a .epsilon) :=
  let hc' := (ComparisonRawHeadRestriction.carrier_modal_total
    (m := .epsilon) (fun _ _ => rfl)).mpr hc
  ⟨.atom hc.carrier hc' (.identityRev hs),.atom hc' hc.carrier (.identity hs)⟩

theorem HeadEquivalent.compose {Δ H a m n}
    (hc : ComparisonRawHeadRestriction.Carrier Δ H (.modal (.modal a m) n))
    (hs : a.WellShaped Δ) :
    HeadEquivalent Δ H (.modal (.modal a m) n) (.modal a (.compose m n)) :=
  let hc' := ComparisonRawHeadRestriction.carrier_compose.mpr hc
  ⟨.atom hc hc' (.compose hs),.atom hc' hc (.composeRev hs)⟩

/-- Normalization is an equivalence in the independent whole-head restriction.
It requires only the source carrier and its shape, with no payload guard. -/
theorem normalize_head_equivalent {Δ H m a}
    (hc : ComparisonRawHeadRestriction.Carrier Δ H (.modal a m))
    (hs : a.WellShaped Δ) : HeadEquivalent Δ H (.modal a m) ((normalize Δ m).apply a) := by
  induction m generalizing a with
  | compose l r hl hr =>
    by_cases h : Entails Δ (.defined (.compose l r))
    · rw [normalize_total h]
      exact HeadEquivalent.refl hc hs
    · have hc' := ComparisonRawHeadRestriction.carrier_compose.mp hc
      have he := (HeadEquivalent.compose hc' hs).symm.trans (hr hc' hs)
      cases hp : (normalize Δ r).literal with
      | none =>
        simp only [Normalized.apply, hp, prefixApply] at he
        have hcl := (ComparisonRawHeadRestriction.carrier_modal_total
          (control_total Δ r)).mp he.1.carriers.2
        have hg := he.trans ((hl hcl hs).modal (control_total Δ r))
        have ht := hg.trans (HeadEquivalent.compose
          (a := prefixApply (normalize Δ l).literal a) hg.1.carriers.2 hg.1.shaped.2)
        simpa only [normalize, if_neg h, hp, Normalized.apply] using ht
      | some p =>
        simp only [Normalized.apply, hp, prefixApply] at he
        have hcp := (ComparisonRawHeadRestriction.carrier_modal_total
          (control_total Δ r)).mp he.1.carriers.2
        have ht := he.trans ((HeadEquivalent.compose hcp hs).modal (control_total Δ r))
        simpa only [normalize, if_neg h, hp, Normalized.apply, prefixApply] using ht
  | _ =>
    simp only [normalize]
    split
    · exact HeadEquivalent.refl hc hs
    · exact HeadEquivalent.identity hc hs

private def AlgebraEquivalent (Δ : Bounds) (a b : CompareTy) : Prop :=
  AlgebraSubtype Δ a b ∧ AlgebraSubtype Δ b a

private theorem AlgebraEquivalent.refl {Δ a} (hs : a.WellShaped Δ) :
    AlgebraEquivalent Δ a a := ⟨.refl hs,.refl hs⟩

private theorem AlgebraEquivalent.trans {Δ a b c} (h : AlgebraEquivalent Δ a b)
    (g : AlgebraEquivalent Δ b c) : AlgebraEquivalent Δ a c :=
  ⟨h.1.trans g.1,g.2.trans h.2⟩

private theorem AlgebraEquivalent.modal {Δ a b m} (h : AlgebraEquivalent Δ a b)
    (hm : Entails Δ (.defined m)) : AlgebraEquivalent Δ (.modal a m) (.modal b m) :=
  ⟨h.1.congr (.refl hm),h.2.congr (.refl hm)⟩

private theorem AlgebraEquivalent.compose {Δ a m n} (hs : a.WellShaped Δ) :
    AlgebraEquivalent Δ (.modal (.modal a m) n) (.modal a (.compose m n)) :=
  ⟨.shaped (.compose hs),.shaped (.composeRev hs)⟩

private theorem AlgebraEquivalent.expand {Δ a m n} (hs : a.WellShaped Δ) :
    AlgebraEquivalent Δ (.modal a (.compose m n)) (.modal (.modal a m) n) :=
  ⟨.shaped (.composeRev hs),.shaped (.compose hs)⟩

theorem normalize_algebra {Δ m a} (hs : a.WellShaped Δ) :
    AlgebraSubtype Δ (.modal a m) ((normalize Δ m).apply a) ∧
      AlgebraSubtype Δ ((normalize Δ m).apply a) (.modal a m) := by
  change AlgebraEquivalent Δ (.modal a m) ((normalize Δ m).apply a)
  induction m generalizing a with
  | compose l r hl hr =>
    by_cases h : Entails Δ (.defined (.compose l r))
    · rw [normalize_total h]
      exact AlgebraEquivalent.refl hs
    · have he := (AlgebraEquivalent.expand (m := l) (n := r) hs).trans (hr hs)
      cases hp : (normalize Δ r).literal with
      | none =>
        simp only [Normalized.apply, hp, prefixApply] at he
        have hg := he.trans ((hl hs).modal (control_total Δ r))
        have ht := hg.trans (AlgebraEquivalent.compose
          (a := prefixApply (normalize Δ l).literal a) hg.1.wellShaped_right)
        simpa only [normalize, if_neg h, hp, Normalized.apply] using ht
      | some p =>
        simp only [Normalized.apply, hp, prefixApply] at he
        have ht := he.trans ((AlgebraEquivalent.compose (m := l) (n := p) hs).modal
          (control_total Δ r))
        simpa only [normalize, if_neg h, hp, Normalized.apply, prefixApply] using ht
  | _ =>
    simp only [normalize]
    split
    · exact AlgebraEquivalent.refl hs
    · exact ⟨.shaped (.identityRev hs),.shaped (.identity hs)⟩


theorem heads_literal (Δ : Bounds) (m : ModExpr) (a : CompareTy) :
    ComparisonRawHeadRestriction.heads Δ (.modal a m) =
      ComparisonRawHeadRestriction.heads Δ (prefixApply (normalize Δ m).literal a) := by
  induction m generalizing a with
  | compose l r hl hr =>
    by_cases h : Entails Δ (.defined (.compose l r))
    · rw [normalize_total h]
      exact ComparisonRawHeadRestriction.heads_modal_total h a
    · cases hp : (normalize Δ r).literal with
      | none =>
        rw [ComparisonRawHeadRestriction.heads_compose, hr]
        simpa only [normalize, if_neg h, hp, prefixApply] using hl a
      | some p =>
        rw [ComparisonRawHeadRestriction.heads_compose, hr]
        simp only [normalize, if_neg h, hp, prefixApply]
        exact (ComparisonRawHeadRestriction.heads_compose Δ a l p).symm
  | _ =>
    simp only [normalize]
    split
    · exact ComparisonRawHeadRestriction.heads_modal_total ‹_› a
    · rfl

theorem heads_normalize (Δ : Bounds) (m : ModExpr) (a : CompareTy) :
    ComparisonRawHeadRestriction.heads Δ ((normalize Δ m).apply a) =
      ComparisonRawHeadRestriction.heads Δ (.modal a m) := by
  rw [Normalized.apply, ComparisonRawHeadRestriction.heads_modal_total (control_total Δ m),
    ← heads_literal]

theorem oneHead_compose (Δ : Bounds) (a : CompareTy) (m n : ModExpr) :
    ComparisonRawHeadRestriction.oneHead Δ (.modal a (.compose m n)) =
      ComparisonRawHeadRestriction.oneHead Δ (.modal (.modal a m) n) := by
  rw [ComparisonRawHeadRestriction.oneHead]

theorem oneHead_literal (Δ : Bounds) (m : ModExpr) (a : CompareTy) :
    ComparisonRawHeadRestriction.oneHead Δ (.modal a m) =
      ComparisonRawHeadRestriction.oneHead Δ (prefixApply (normalize Δ m).literal a) := by
  induction m generalizing a with
  | compose l r hl hr =>
    by_cases h : Entails Δ (.defined (.compose l r))
    · rw [normalize_total h]
      exact ComparisonRawHeadRestriction.oneHead_modal_total h a
    · cases hp : (normalize Δ r).literal with
      | none =>
        rw [oneHead_compose, hr]
        simpa only [normalize, if_neg h, hp, prefixApply] using hl a
      | some p =>
        rw [oneHead_compose, hr]
        simp only [normalize, if_neg h, hp, prefixApply]
        exact (oneHead_compose Δ a l p).symm
  | _ =>
    simp only [normalize]
    split
    · exact ComparisonRawHeadRestriction.oneHead_modal_total ‹_› a
    · rfl

theorem oneHead_normalize (Δ : Bounds) (m : ModExpr) (a : CompareTy) :
    ComparisonRawHeadRestriction.oneHead Δ ((normalize Δ m).apply a) =
      ComparisonRawHeadRestriction.oneHead Δ (.modal a m) := by
  rw [Normalized.apply, ComparisonRawHeadRestriction.oneHead_modal_total (control_total Δ m),
    ← oneHead_literal]

theorem carrier_normalize_iff {Δ H m a} :
    ComparisonRawHeadRestriction.Carrier Δ H ((normalize Δ m).apply a) ↔
      ComparisonRawHeadRestriction.Carrier Δ H (.modal a m) := by
  simp only [Normalized.apply, ComparisonRawHeadRestriction.Carrier,
    ComparisonRawHeadRestriction.Generator,
    ComparisonRawHeadRestriction.oneHead_modal_total (control_total Δ m), ← oneHead_literal]

theorem Normalized.apply_wellShaped_iff {Δ a} (s : Normalized) :
    (s.apply a).WellShaped Δ ↔ a.WellShaped Δ := by
  cases hp : s.literal <;> simp only [Normalized.apply, prefixApply, hp, CompareTy.WellShaped]

/-- Root composition is coherent under a total outer suffix. A partial outer
prefix is deliberately excluded: reassociating beneath it is not a rule. -/
theorem Normalized.prepend_compose {Δ} {s : Normalized}
    (hp : s.literal = none) (hs : Entails Δ (.defined s.control)) (m n : ModExpr) :
    Normalized.Below Δ (s.prepend Δ (.compose m n)) ((s.prepend Δ n).prepend Δ m) ∧
      Normalized.Below Δ ((s.prepend Δ n).prepend Δ m) (s.prepend Δ (.compose m n)) := by
  rw [Normalized.prepend, hp, normalize_compose]
  cases hn : (normalize Δ n).literal with
  | some p =>
    simp only [Normalized.prepend, hp, hn, Normalized.Below, true_and]
    have ht := Entails.defined_compose_iff.mpr ⟨control_total Δ n,hs⟩
    exact ⟨Submode.refl ht,Submode.refl ht⟩
  | none =>
    simp only [Normalized.prepend, hp, hn, Normalized.Below, true_and]
    constructor <;> apply Submode.valid <;> intro η hη
    all_goals
      obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp (control_total Δ m η hη)
      obtain ⟨y,hy⟩ := Option.isSome_iff_exists.mp (control_total Δ n η hη)
      obtain ⟨z,hz⟩ := Option.isSome_iff_exists.mp (hs η hη)
      simp [ModExpr.Below, ModExpr.eval, hx, hy, hz, Mode.compose_assoc]

theorem literal_headEquivalent (Δ : Bounds) (m : ModExpr) :
    ComparisonRawHeadRestriction.Suffix.HeadEquivalent Δ
      (normalize Δ m).literal (some m) := by
  constructor
  · cases hp : (normalize Δ m).literal with
    | none =>
      exact ⟨fun _ => (literal_none_iff Δ m).mp hp, fun _ => trivial⟩
    | some p =>
      exact ⟨fun h => False.elim (literal_partial hp h), fun h =>
        False.elim (Option.noConfusion (hp.symm.trans ((literal_none_iff Δ m).mpr h)))⟩
  · intro a
    exact (heads_literal Δ m a).symm

theorem support_prepend (Δ : Bounds) (s : Normalized) (m : ModExpr) (a : CompareTy) :
    ComparisonRawHeadRestriction.support Δ a (s.prepend Δ m).literal =
      ComparisonRawHeadRestriction.support Δ (.modal a m) s.literal := by
  cases hp : s.literal with
  | none =>
    simpa only [Normalized.prepend, hp, ComparisonRawHeadRestriction.support,
      ComparisonPartialStructuredCapsule.Suffix.prepend] using
      (ComparisonRawHeadRestriction.support_suffix_congr (literal_headEquivalent Δ m) a)
  | some p => simp only [Normalized.prepend, hp, ComparisonRawHeadRestriction.support,
      ComparisonPartialStructuredCapsule.Suffix.prepend]

theorem Normalized.prepend_head_equivalent {Δ H} (s : Normalized) (m : ModExpr)
    (ht : Entails Δ (.defined s.control)) {a : CompareTy}
    (hc : ComparisonRawHeadRestriction.Carrier Δ H (s.apply (.modal a m)))
    (hs : a.WellShaped Δ) :
    HeadEquivalent Δ H (s.apply (.modal a m)) ((s.prepend Δ m).apply a) := by
  cases hp : s.literal with
  | none =>
    simp only [Normalized.apply, hp, prefixApply] at hc
    have hc' : ComparisonRawHeadRestriction.Carrier Δ H (.modal a m) :=
      (ComparisonRawHeadRestriction.carrier_modal_total ht).mp hc
    have h := (normalize_head_equivalent hc' hs).modal ht
    have g := h.trans (HeadEquivalent.compose
      (a := prefixApply (normalize Δ m).literal a) h.1.carriers.2 h.1.shaped.2)
    simpa only [Normalized.apply, Normalized.prepend, hp, prefixApply] using g
  | some p =>
    simp only [Normalized.apply, hp, prefixApply] at hc
    have hc' : ComparisonRawHeadRestriction.Carrier Δ H (.modal (.modal a m) p) :=
      (ComparisonRawHeadRestriction.carrier_modal_total ht).mp hc
    simpa only [Normalized.apply, Normalized.prepend, hp, prefixApply] using
      (HeadEquivalent.compose hc' hs).modal ht

end
end ModalityInference.ComparisonRawCarrierSuffix
