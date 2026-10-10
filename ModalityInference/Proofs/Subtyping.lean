import ModalityInference.Proofs.Mode
import ModalityInference.Proofs.Interpretation

/-! Semantic soundness of every declarative subtyping rule, including symbolic
bounds and partial modality expressions. No deferred metatheory is imported. -/
namespace ModalityInference

theorem Submode.denote {Δ a b σ} (h : Submode Δ a b) (hΔ : ModeModels Δ σ) :
    ModExpr.Below σ a b := by
  induction h with
  | valid h => exact h σ hΔ
  | lowerBound h => exact hΔ _ h
  | upperBound h => exact hΔ _ h
  | trans _ _ iha ihb =>
    obtain ⟨a, b, ha, hb, hab⟩ := iha
    obtain ⟨b', c, hb', hc, hbc⟩ := ihb
    cases Option.some.inj (hb.symm.trans hb')
    exact ⟨a, c, ha, hc, Mode.le_trans hab hbc⟩

theorem GroundModels.modeModels {ρ Δ} (h : GroundModels ρ Δ) : ModeModels Δ ρ.modes := by
  intro c hc
  cases c <;> first | exact h _ hc | trivial

@[simp] theorem GroundTy.modal_compose (t : GroundTy) (m n : Mode) :
    (t.modal m).modal n = t.modal (m.compose n) := by
  cases t <;> simp [GroundTy.modal, Mode.compose_assoc]

theorem ValueInterpretation.modal_iff {ρ w t m n v} :
    ValueInterpretation ρ w (t.modal m) n v ↔
      ValueInterpretation ρ w t (m.compose n) v := by
  cases t <;> cases v <;>
    simp only [GroundTy.modal, ValueInterpretation, GroundTy.mode, Mode.compose_assoc]

theorem Owns.mode_mono {ρ v l} {t : GroundTy} {m n : Mode} (h : m.le n = true)
    (ho : Owns ρ v (t.modal n) l) : Owns ρ v (t.modal m) l := by
  induction t generalizing m n v
  all_goals cases ho
  case credit.credit =>
    exact .credit (((Mode.le_iff _ _).mp (Mode.compose_le_left _ h)).2.2 ‹_›)
  case prod.pairCell =>
    exact .pairCell (((Mode.le_iff _ _).mp (Mode.compose_le_left _ h)).2.2 ‹_›)
  case prod.pairFirst => apply Owns.pairFirst; solve_by_elim [Mode.compose_le_left]
  case prod.pairSecond => apply Owns.pairSecond; solve_by_elim [Mode.compose_le_left]
  case sum.inl => apply Owns.inl; solve_by_elim [Mode.compose_le_left]
  case sum.inr => apply Owns.inr; solve_by_elim [Mode.compose_le_left]
  case fn.closure => exact .closure ‹_› ‹_› ‹_› ‹_› ‹_›

theorem Separated.mode_mono {ρ v w} {a b : GroundTy} {m n : Mode} (h : m.le n = true)
    (hs : Separated ρ v (a.modal m) w (b.modal m)) :
    Separated ρ v (a.modal n) w (b.modal n) := by
  intro l hl
  exact hs l ⟨Owns.mode_mono h hl.1, Owns.mode_mono h hl.2⟩

theorem ValueInterpretation.mode_mono {ρ w t v} {m n : Mode} (h : m.le n = true)
    (hv : ValueInterpretation ρ w t m v) : ValueInterpretation ρ w t n v := by
  induction t generalizing m n v with
  | prod a b p iha ihb =>
    cases v <;> simp only [ValueInterpretation, GroundTy.mode, and_false] at hv ⊢
    have hp := Mode.compose_le_left p h
    refine ⟨hv.1, hv.2.1.imp ((Mode.le_iff _ _).mp hp).1 id,
      iha hp hv.2.2.1, ihb hp hv.2.2.2.1, ?_, ?_,
      Separated.mode_mono hp hv.2.2.2.2.2.2⟩
    · simpa only [GroundTy.modal, Mode.identity_compose] using
        (Separated.mode_mono (a := .credit Mode.identity) hp
          (by simpa only [GroundTy.modal, Mode.identity_compose] using hv.2.2.2.2.1))
    · simpa only [GroundTy.modal, Mode.identity_compose] using
        (Separated.mode_mono (a := .credit Mode.identity) hp
          (by simpa only [GroundTy.modal, Mode.identity_compose] using hv.2.2.2.2.2.1))
  | unit p => cases v <;> simpa only [ValueInterpretation] using hv
  | credit p =>
    cases v <;> simp only [ValueInterpretation, GroundTy.mode, and_false] at hv ⊢
    exact ⟨hv.1, hv.2.imp ((Mode.le_iff _ _).mp (Mode.compose_le_left p h)).1 id⟩
  | sum a b p iha ihb =>
    cases v <;> simp only [ValueInterpretation, GroundTy.mode, and_false] at hv ⊢
    · exact ⟨hv.1, iha (Mode.compose_le_left p h) hv.2⟩
    · exact ⟨hv.1, ihb (Mode.compose_le_left p h) hv.2⟩
  | fn a b p _ _ =>
    cases v <;> simp only [ValueInterpretation, GroundTy.mode, and_false] at hv ⊢
    have hp := (Mode.le_iff _ _).mp (Mode.compose_le_left p h)
    exact ⟨hv.1,
      fun hn => hv.2.1 (Bool.eq_false_iff.mpr (mt hp.1 (Bool.eq_false_iff.mp hn))),
      fun hn => hv.2.2.1 (Bool.eq_false_iff.mpr (mt hp.2.1 (Bool.eq_false_iff.mp hn))),
      hv.2.2.2⟩

private def SemLe (ρ : GroundAssignment) (a b : GroundTy) : Prop :=
  ∀ w ambient v, ValueInterpretation ρ w a ambient v →
    ValueInterpretation ρ w b ambient v ∧
      ∀ l, Owns ρ v (b.modal ambient) l → Owns ρ v (a.modal ambient) l

private theorem SemLe.refl (ρ : GroundAssignment) (a : GroundTy) : SemLe ρ a a :=
  fun _ _ _ hv => ⟨hv, fun _ ho => ho⟩

private theorem SemLe.trans {ρ a b c} (hab : SemLe ρ a b) (hbc : SemLe ρ b c) :
    SemLe ρ a c := by
  intro w ambient v hv
  obtain ⟨hb, hob⟩ := hab w ambient v hv
  obtain ⟨hc, hoc⟩ := hbc w ambient v hb
  exact ⟨hc, fun l ho => hob l (hoc l ho)⟩

private theorem SemLe.modal {ρ a b} {m n : Mode} (hab : SemLe ρ a b)
    (hmn : m.le n = true) : SemLe ρ (a.modal m) (b.modal n) := by
  intro w ambient v hv
  obtain ⟨hb, ho⟩ := hab w (m.compose ambient) v (ValueInterpretation.modal_iff.mp hv)
  have h := Mode.compose_le_right ambient hmn
  refine ⟨ValueInterpretation.modal_iff.mpr (hb.mode_mono h), ?_⟩
  simp only [GroundTy.modal_compose]
  exact fun l hl => ho l (Owns.mode_mono h hl)

private theorem SemLe.prod {ρ a b c d m}
    (hac : SemLe ρ (a.modal m) (c.modal m))
    (hbd : SemLe ρ (b.modal m) (d.modal m)) :
    SemLe ρ (.prod a b m) (.prod c d m) := by
  intro w ambient v hv
  cases v <;> simp only [ValueInterpretation, GroundTy.mode, and_false] at hv ⊢
  rename_i l x y
  obtain ⟨hx, hox⟩ := hac w ambient x (ValueInterpretation.modal_iff.mpr hv.2.2.1)
  obtain ⟨hy, hoy⟩ := hbd w ambient y (ValueInterpretation.modal_iff.mpr hv.2.2.2.1)
  simp only [GroundTy.modal_compose] at hox hoy
  refine ⟨⟨hv.1, hv.2.1, ValueInterpretation.modal_iff.mp hx,
    ValueInterpretation.modal_iff.mp hy, ?_, ?_, ?_⟩, ?_⟩
  · exact fun k ⟨hc, hx⟩ => hv.2.2.2.2.1 k ⟨hc, hox k hx⟩
  · exact fun k ⟨hc, hy⟩ => hv.2.2.2.2.2.1 k ⟨hc, hoy k hy⟩
  · exact fun k ⟨hx, hy⟩ => hv.2.2.2.2.2.2 k ⟨hox k hx, hoy k hy⟩
  · intro k ho
    cases ho with
    | pairCell h => exact .pairCell h
    | pairFirst h => exact .pairFirst (hox k h)
    | pairSecond h => exact .pairSecond (hoy k h)

private theorem SemLe.sum {ρ a b c d m}
    (hac : SemLe ρ (a.modal m) (c.modal m))
    (hbd : SemLe ρ (b.modal m) (d.modal m)) :
    SemLe ρ (.sum a b m) (.sum c d m) := by
  intro w ambient v hv
  cases v <;> simp only [ValueInterpretation, GroundTy.mode, and_false] at hv ⊢
  · rename_i x
    obtain ⟨hx, hox⟩ := hac w ambient x (ValueInterpretation.modal_iff.mpr hv.2)
    simp only [GroundTy.modal_compose] at hox
    refine ⟨⟨hv.1, ValueInterpretation.modal_iff.mp hx⟩, ?_⟩
    intro l ho
    cases ho with | inl ho => exact .inl (hox l ho)
  · rename_i x
    obtain ⟨hx, hox⟩ := hbd w ambient x (ValueInterpretation.modal_iff.mpr hv.2)
    simp only [GroundTy.modal_compose] at hox
    refine ⟨⟨hv.1, ValueInterpretation.modal_iff.mp hx⟩, ?_⟩
    intro l ho
    cases ho with | inr ho => exact .inr (hox l ho)

private theorem SemLe.credit {ρ} {m n : Mode}
    (hl : m.isLocal = true → n.isLocal = true)
    (hu : n.unique = true → m.unique = true) : SemLe ρ (.credit m) (.credit n) := by
  intro w ambient v hv
  cases v <;> simp only [ValueInterpretation, GroundTy.mode, and_false] at hv ⊢
  have hl' : (m.compose ambient).isLocal = true → (n.compose ambient).isLocal = true :=
    fun h => Bool.and_eq_true_iff.mpr ⟨hl (Bool.and_eq_true_iff.mp h).1, (Bool.and_eq_true_iff.mp h).2⟩
  refine ⟨⟨hv.1, hv.2.imp hl' id⟩, ?_⟩
  intro l ho
  cases ho with
  | credit h =>
    exact .credit
      (Bool.and_eq_true_iff.mpr ⟨hu (Bool.and_eq_true_iff.mp h).1, (Bool.and_eq_true_iff.mp h).2⟩)

private theorem SemLe.fn {ρ a b c d m n}
    (hac : SemLe ρ c a) (hbd : SemLe ρ b d)
    (hl : m.isLocal = true → n.isLocal = true)
    (hf : m.once = true → n.once = true) :
    SemLe ρ (.fn a b m) (.fn c d n) := by
  intro w ambient v hv
  cases v <;> simp only [ValueInterpretation, GroundTy.mode, and_false] at hv ⊢
  have hl' : (m.compose ambient).isLocal = true → (n.compose ambient).isLocal = true :=
    fun h => Bool.and_eq_true_iff.mpr ⟨hl (Bool.and_eq_true_iff.mp h).1, (Bool.and_eq_true_iff.mp h).2⟩
  have hf' : (m.compose ambient).once = true → (n.compose ambient).once = true :=
    fun h => Bool.and_eq_true_iff.mpr ⟨hf (Bool.and_eq_true_iff.mp h).1, (Bool.and_eq_true_iff.mp h).2⟩
  refine ⟨⟨hv.1,
    fun hn => hv.2.1 (Bool.eq_false_iff.mpr (mt hl' (Bool.eq_false_iff.mp hn))),
    fun hn => hv.2.2.1 (Bool.eq_false_iff.mpr (mt hf' (Bool.eq_false_iff.mp hn))), ?_⟩, ?_⟩
  · intro w' x hγ hx hs supplies hc
    obtain ⟨hxa, hoa⟩ := hac w' Mode.identity x hx
    simp only [GroundTy.modal_identity] at hoa
    obtain ⟨r, he, hr, ho⟩ := hv.2.2.2 w' x hγ hxa
      (fun l ⟨hγ, hx⟩ => hs l ⟨hγ, hoa l hx⟩) supplies hc
    obtain ⟨hrd, hod⟩ := hbd w' Mode.identity r hr
    simp only [GroundTy.modal_identity] at hod
    refine ⟨r, he, hrd, ?_⟩
    exact fun l hl => (ho l (hod l hl)).imp id (Or.imp (hoa l) id)
  · intro l ho
    cases ho
    exact .closure ‹_› ‹_› ‹_› ‹_› ‹_›

private def OptLe (ρ : GroundAssignment) : Option GroundTy → Option GroundTy → Prop
  | none, none => True
  | some a, some b => SemLe ρ a b
  | _, _ => False

private theorem OptLe.refl (ρ : GroundAssignment) (a : Option GroundTy) : OptLe ρ a a := by
  cases a with
  | none => trivial
  | some a => exact SemLe.refl ρ a

private theorem OptLe.trans {ρ a b c} (hab : OptLe ρ a b) (hbc : OptLe ρ b c) :
    OptLe ρ a c := by
  cases a <;> cases b <;> cases c <;> simp only [OptLe] at *
  all_goals first | trivial | exact SemLe.trans hab hbc

@[simp] theorem TypeExpr.realize_identity (ρ : GroundAssignment) (t : Ty) :
    (t.modal .epsilon).realize ρ = t.realize ρ := by
  cases ht : t.realize ρ <;> simp [TypeExpr.realize, ht, ModExpr.epsilon, ModExpr.eval]

theorem TypeExpr.realize_compose (ρ : GroundAssignment) (t : Ty) (m n : ModExpr) :
    ((t.modal m).modal n).realize ρ = (t.modal (.compose m n)).realize ρ := by
  cases ht : t.realize ρ <;> cases hm : m.eval (some ∘ ρ.modes) <;>
    cases hn : n.eval (some ∘ ρ.modes) <;> simp [TypeExpr.realize, ModExpr.eval, ht, hm, hn]

@[simp] theorem GroundTy.realize_reify (ρ : GroundAssignment) (t : GroundTy) :
    t.reify.realize ρ = some t := by
  induction t <;> simp_all [GroundTy.reify, TypeExpr.realize, ModExpr.eval,
    GroundTy.modal, Mode.identity_compose]

private theorem Subtype.optLe_of_bounds {ρ Δ a b} (h : Subtype Δ a b)
    (hmodes : ModeModels Δ ρ.modes)
    (hbounds : ∀ a b, Constraint.sub a b ∈ Δ → OptLe ρ (a.realize ρ) (b.realize ρ)) :
    OptLe ρ (a.realize ρ) (b.realize ρ) := by
  induction h
  case prod a b c d m _ _ iha ihb =>
    cases ha : a.realize ρ <;> cases hb : b.realize ρ <;>
      cases hc : c.realize ρ <;> cases hd : d.realize ρ <;>
      cases hm : m.eval (some ∘ ρ.modes) <;>
      simp_all [OptLe, TypeExpr.realize, GroundTy.modal, Mode.identity_compose]
    exact SemLe.prod iha ihb
  case fn a b c d m n _ _ hmode iha ihb =>
    have hmn := hmode.denote hmodes
    cases hm : m.eval (some ∘ ρ.modes) <;> cases hn : n.eval (some ∘ ρ.modes) <;>
      simp [ModExpr.Below, ModExpr.eval, ModExpr.top, hm, hn, Mode.le_iff, Mode.compose, Mode.top] at hmn
    cases ha : a.realize ρ <;> cases hb : b.realize ρ <;>
      cases hc : c.realize ρ <;> cases hd : d.realize ρ <;>
      simp_all [OptLe, TypeExpr.realize, GroundTy.modal, Mode.identity_compose]
    exact SemLe.fn iha ihb hmn.1 hmn.2
  case sum a b c d m _ _ iha ihb =>
    cases ha : a.realize ρ <;> cases hb : b.realize ρ <;>
      cases hc : c.realize ρ <;> cases hd : d.realize ρ <;>
      cases hm : m.eval (some ∘ ρ.modes) <;>
      simp_all [OptLe, TypeExpr.realize, GroundTy.modal, Mode.identity_compose]
    exact SemLe.sum iha ihb
  case congr a b m n _ hmode ih =>
    obtain ⟨u, v, hm, hn, huv⟩ := hmode.denote hmodes
    cases ha : a.realize ρ <;> cases hb : b.realize ρ <;>
      simp_all [OptLe, TypeExpr.realize]
    exact SemLe.modal ih huv
  case credit m n hmode =>
    have hmn := hmode.denote hmodes
    cases hm : m.eval (some ∘ ρ.modes) <;> cases hn : n.eval (some ∘ ρ.modes) <;>
      simp [ModExpr.Below, ModExpr.eval, hm, hn, Mode.le_iff, Mode.compose, Mode.many] at hmn
    simpa [TypeExpr.realize, hm, hn, GroundTy.modal, OptLe] using SemLe.credit hmn.1 hmn.2
  case refl a => exact OptLe.refl ρ (a.realize ρ)
  case trans _ _ iha ihb => exact OptLe.trans iha ihb
  case bound a b h => exact hbounds a b h
  case identity => simpa only [TypeExpr.realize_identity] using OptLe.refl ρ _
  case identityRev => simpa only [TypeExpr.realize_identity] using OptLe.refl ρ _
  case compose => simp only [TypeExpr.realize_compose]; exact OptLe.refl ρ _
  case composeRev => simp only [TypeExpr.realize_compose]; exact OptLe.refl ρ _

private theorem Subtype.optLe_empty {ρ a b} (h : Subtype [] a b) :
    OptLe ρ (a.realize ρ) (b.realize ρ) :=
  h.optLe_of_bounds (by simp [ModeModels]) (by simp)

private theorem Subtype.optLe {ρ Δ a b} (h : Subtype Δ a b) (hΔ : GroundModels ρ Δ) :
    OptLe ρ (a.realize ρ) (b.realize ρ) := by
  apply h.optLe_of_bounds hΔ.modeModels
  intro a b hab
  obtain ⟨x, y, hx, hy, hxy⟩ := hΔ _ hab
  have hs := hxy.optLe_empty (ρ := ρ)
  simpa only [hx, hy, GroundTy.realize_reify] using hs

/-- Subtyping preserves the interpretation under every inherited modality and
can only decrease ownership, with field modalities and capture schemes retained. -/
theorem Subtype.semantic {ρ w Δ a b x y v ambient} (h : Subtype Δ a b)
    (hΔ : GroundModels ρ Δ) (ha : a.realize ρ = some x) (hb : b.realize ρ = some y)
    (hv : ValueInterpretation ρ w x ambient v) :
    ValueInterpretation ρ w y ambient v ∧
      ∀ l, Owns ρ v (y.modal ambient) l → Owns ρ v (x.modal ambient) l := by
  have hs := h.optLe hΔ
  rw [ha, hb] at hs
  exact hs w ambient v hv

/-- Partial modalities cannot become defined or undefined merely by subtyping. -/
theorem Subtype.realize_defined {ρ Δ a b} (h : Subtype Δ a b) (hΔ : GroundModels ρ Δ) :
    (a.realize ρ).isSome = (b.realize ρ).isSome := by
  have hs := h.optLe hΔ
  cases ha : a.realize ρ <;> cases hb : b.realize ρ <;> simp_all [OptLe]

end ModalityInference
