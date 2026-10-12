import ModalityInference.Constraints
import ModalityInference.Rewriting
import ModalityInference.Proofs.GroundInstantiation
import ModalityInference.Proofs.GroundOrder
import ModalityInference.Proofs.GenerationTypes

/-! Executable normalization preserves partial modality evaluation and ground
type realization. Undefined residuals remain undefined. -/
namespace ModalityInference

deriving instance ReflBEq for Mode, ModVar, ModExpr, TypeVar, TypeExpr
deriving instance LawfulBEq for Mode, ModVar, ModExpr, TypeVar, TypeExpr

private theorem option_idempotent (a : Option Mode) (f : Mode → Mode → Mode)
    (h : ∀ m, f m m = m) : a = (a.bind fun m => a.bind fun n => some (f m n)) := by
  cases a <;> simp [h]

theorem ModExpr.foldConstants_eval (m : ModExpr) (ρ : ModVar → Option Mode) :
    m.foldConstants.eval ρ = m.eval ρ := by
  unfold ModExpr.foldConstants
  split
  · next k hk => exact (m.eval_refinement (by simp) hk).symm
  · split
    all_goals first | rfl | (split <;> simp_all [beq_iff_eq, ModExpr.eval])
    all_goals
      apply option_idempotent
      intro m
      cases m
      simp [Mode.compose, Mode.meet, Mode.join]

@[simp] theorem ModExpr.normalize_eval (m : ModExpr) (ρ : ModVar → Option Mode) :
    m.normalize.eval ρ = m.eval ρ := by
  induction m <;> simp_all [ModExpr.normalize, ModExpr.foldConstants_eval, ModExpr.eval]

theorem TypeExpr.normalize_realize (a : Ty) (ρ : GroundAssignment) :
    a.normalize.realize ρ = a.realize ρ := by
  induction a
  case modal a m ih =>
    simp only [TypeExpr.normalize]
    split
    · next b k hk =>
      simp only [TypeExpr.realize, ← ih, hk, ModExpr.normalize_eval, ModExpr.eval, bind, pure,
        Option.bind_assoc, Option.bind_some, GroundTy.modal_compose]
    · split
      · next hmode =>
        have hm := congrArg (fun r : ModExpr => r.eval (some ∘ ρ.modes)) (beq_iff_eq.mp hmode)
        simp only [ModExpr.normalize_eval, ModExpr.epsilon, ModExpr.eval] at hm
        simp [TypeExpr.realize, hm, ih]
      · simp [TypeExpr.realize, ih]
  all_goals simp_all [TypeExpr.normalize, TypeExpr.realize]

@[simp] theorem Constraint.normalize_ground (c : Constraint) (ρ : GroundAssignment) :
    GroundSatisfies ρ c.normalize ↔ GroundSatisfies ρ c := by
  cases c <;> simp [Constraint.normalize, GroundSatisfies, TypeExpr.normalize_realize,
    ModExpr.WellFormed, ModExpr.Below]

theorem GroundModels.normalize (cs : Bounds) (ρ : GroundAssignment) :
    GroundModels ρ (cs.map Constraint.normalize) ↔ GroundModels ρ cs := by
  simp [GroundModels]

theorem TypeExpr.normalize_definedUnder (a : Ty) (Δ : Bounds) :
    a.normalize.DefinedUnder Δ ↔ a.DefinedUnder Δ := by
  constructor
  · intro h σ hσ
    let ρ : GroundAssignment := ⟨fun _ => .unit Mode.identity, σ⟩
    exact (a.wellFormedBounds_spec ρ).mpr (by
      simpa only [TypeExpr.normalize_realize] using (a.normalize.wellFormedBounds_spec ρ).mp (h σ hσ))
  · intro h σ hσ
    let ρ : GroundAssignment := ⟨fun _ => .unit Mode.identity, σ⟩
    exact (a.normalize.wellFormedBounds_spec ρ).mpr (by
      simpa only [TypeExpr.normalize_realize] using (a.wellFormedBounds_spec ρ).mp (h σ hσ))

theorem Submode.normalize {Δ a b} :
    Submode Δ a.normalize b.normalize ↔ Submode Δ a b := by
  constructor <;> intro h <;> apply Submode.valid <;> intro σ hσ
  all_goals simpa only [ModExpr.Below, ModExpr.normalize_eval] using h.denote hσ

theorem ModExpr.normalize_submode {Δ} (m : ModExpr)
    (hm : ∀ σ, ModeModels Δ σ → m.WellFormed σ) :
    Submode Δ m.normalize m ∧ Submode Δ m m.normalize := by
  constructor <;> apply Submode.valid <;> intro σ hσ
  all_goals
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hm σ hσ)
    exact ⟨n, n, by simpa using hn, by simpa using hn, Mode.le_refl n⟩

theorem Subtype.prod_congr {Δ a b c d} (ha : Subtype Δ a c) (hb : Subtype Δ b d) :
    Subtype Δ (.prod a b) (.prod c d) :=
  Subtype.identityRev.trans ((Subtype.prod (Subtype.identity.trans (ha.trans .identityRev))
    (Subtype.identity.trans (hb.trans .identityRev))).trans .identity)

theorem Subtype.sum_congr {Δ a b c d} (ha : Subtype Δ a c) (hb : Subtype Δ b d) :
    Subtype Δ (.sum a b) (.sum c d) :=
  Subtype.identityRev.trans ((Subtype.sum (Subtype.identity.trans (ha.trans .identityRev))
    (Subtype.identity.trans (hb.trans .identityRev))).trans .identity)

theorem Subtype.fn_congr {Δ a b c d} (ha : Subtype Δ c a) (hb : Subtype Δ b d) :
    Subtype Δ (.fn a b) (.fn c d) :=
  Subtype.identityRev.trans ((Subtype.fn ha hb (.valid fun _ _ =>
    ⟨Mode.identity, Mode.identity.compose Mode.top, rfl, rfl, by decide⟩)).trans .identity)

theorem TypeExpr.normalize_subtype {Δ} (a : Ty) (ha : a.DefinedUnder Δ) :
    Subtype Δ a.normalize a ∧ Subtype Δ a a.normalize := by
  induction a
  case modal a m ih =>
    obtain ⟨ha, hm⟩ := TypeExpr.definedUnder_modal.mp ha
    suffices hh : Subtype Δ (a.modal m).normalize (a.normalize.modal m.normalize) ∧
        Subtype Δ (a.normalize.modal m.normalize) (a.modal m).normalize from
      ⟨hh.1.trans (.congr (ih ha).1 (m.normalize_submode hm).1),
        (Subtype.congr (ih ha).2 (m.normalize_submode hm).2).trans hh.2⟩
    simp only [TypeExpr.normalize]
    split
    · next b k hk =>
      have hkdef := (definedUnder_modal.mp (hk ▸ (normalize_definedUnder a Δ).mpr ha)).2
      have hc : ∀ η, ModeModels Δ η → (k.compose m.normalize).WellFormed η := by
        intro η hη
        obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := And.intro
          (Option.isSome_iff_exists.mp (hkdef η hη))
          (Option.isSome_iff_exists.mp (hm η hη))
        simp [ModExpr.WellFormed, ModExpr.eval, hx, hy]
      simpa only [hk] using And.intro
        ((Subtype.congr (.refl (a := b)) ((k.compose m.normalize).normalize_submode hc).1).trans
          .composeRev)
        (Subtype.compose.trans
          (.congr (.refl (a := b)) ((k.compose m.normalize).normalize_submode hc).2))
    · split
      · next hm =>
        simpa only [beq_iff_eq.mp hm] using And.intro
          (Subtype.identityRev (Δ := Δ) (a := a.normalize)) Subtype.identity
      · exact ⟨.refl, .refl⟩
  case prod a b iha ihb =>
    exact ⟨.prod_congr (iha (definedUnder_prod.mp ha).1).1 (ihb (definedUnder_prod.mp ha).2).1,
      .prod_congr (iha (definedUnder_prod.mp ha).1).2 (ihb (definedUnder_prod.mp ha).2).2⟩
  case sum a b iha ihb =>
    exact ⟨.sum_congr (iha (definedUnder_sum.mp ha).1).1 (ihb (definedUnder_sum.mp ha).2).1,
      .sum_congr (iha (definedUnder_sum.mp ha).1).2 (ihb (definedUnder_sum.mp ha).2).2⟩
  case fn a b iha ihb =>
    exact ⟨.fn_congr (iha (definedUnder_fn.mp ha).1).2 (ihb (definedUnder_fn.mp ha).2).1,
      .fn_congr (iha (definedUnder_fn.mp ha).1).1 (ihb (definedUnder_fn.mp ha).2).2⟩
  all_goals exact ⟨.refl, .refl⟩

theorem Subtype.normalize_iff {Δ a b} (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) :
    Subtype Δ a.normalize b.normalize ↔ Subtype Δ a b :=
  ⟨fun h => (a.normalize_subtype ha).2.trans (h.trans (b.normalize_subtype hb).1),
    fun h => (a.normalize_subtype ha).1.trans (h.trans (b.normalize_subtype hb).2)⟩

@[simp] theorem Constraint.normalize_entails (c : Constraint) (Δ : Bounds) :
    Entails Δ c.normalize ↔ Entails Δ c := by
  cases c <;> simp only [Constraint.normalize, Entails, TypeExpr.normalize_definedUnder,
    Submode.normalize, ModExpr.WellFormed, ModExpr.normalize_eval]
  case sub a b =>
    exact ⟨fun ⟨h, ha, hb⟩ => ⟨(Subtype.normalize_iff ha hb).mp h, ha, hb⟩,
      fun ⟨h, ha, hb⟩ => ⟨(Subtype.normalize_iff ha hb).mpr h, ha, hb⟩⟩
  case equal v a =>
    exact ⟨fun ⟨h₁, h₂, ha⟩ => ⟨h₁.trans (a.normalize_subtype ha).1,
        (a.normalize_subtype ha).2.trans h₂, ha⟩,
      fun ⟨h₁, h₂, ha⟩ => ⟨h₁.trans (a.normalize_subtype ha).2,
        (a.normalize_subtype ha).1.trans h₂, ha⟩⟩
  case equiv a b =>
    exact ⟨fun ⟨h₁, h₂, ha, hb⟩ => ⟨(Subtype.normalize_iff ha hb).mp h₁,
        (Subtype.normalize_iff hb ha).mp h₂, ha, hb⟩,
      fun ⟨h₁, h₂, ha, hb⟩ => ⟨(Subtype.normalize_iff ha hb).mpr h₁,
        (Subtype.normalize_iff hb ha).mpr h₂, ha, hb⟩⟩

@[simp] theorem EntailsAll.normalize (cs : Bounds) (Δ : Bounds) :
    EntailsAll Δ (cs.map Constraint.normalize) ↔ EntailsAll Δ cs := by
  simp [EntailsAll]

theorem Rewrites.normalize_pending (s : RewriteConfig) :
    Rewrites s {s with pending := s.pending.map Constraint.normalize} := by
  simpa using (Rewrites.equivalence (s := {s with pending := []})
    (cs := s.pending) (ds := s.pending.map Constraint.normalize)
    fun Δ => (EntailsAll.normalize s.pending Δ).symm)

@[simp] theorem TypeExpr.normalize_typeVars (a : Ty) : a.normalize.typeVars = a.typeVars := by
  induction a <;> simp_all [TypeExpr.normalize, TypeExpr.typeVars]
  split <;> simp_all [TypeExpr.typeVars]
  split <;> simp_all [TypeExpr.typeVars]

end ModalityInference
