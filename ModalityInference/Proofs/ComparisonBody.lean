import ModalityInference.ComparisonBody
import ModalityInference.Proofs.ComparisonPartial
import ModalityInference.Proofs.ComparisonPartialModes
import ModalityInference.Proofs.Projection

namespace ModalityInference.ComparisonBody

private def act : List ModExpr → Ty → Ty
  | [], a => a
  | m :: ms, a => .modal (act ms a) m

private theorem peelFuel_correct {Δ : Bounds} (total : ModExpr → Bool)
    (htotal : ∀ m, total m = true → Submode Δ m m) (fuel : Nat) (t : Ty) :
    let result := peelFuel total fuel t
    Subtype Δ t (act result.labels result.base) ∧
      Subtype Δ (act result.labels result.base) t := by
  induction fuel generalizing t with
  | zero => exact ⟨.refl, .refl⟩
  | succ fuel ih =>
    have hn := ComparisonPartialModes.normalizeOuter_correct Δ t
    cases he : ComparisonPartialModes.normalizeOuter t <;> simp only [peelFuel, he]
    all_goals try simpa only [he, act] using hn
    split
    · next hm =>
      exact ⟨(he ▸ hn.1).trans (.congr (ih _).1 (htotal _ hm)),
        (Subtype.congr (ih _).2 (htotal _ hm)).trans (he ▸ hn.2)⟩
    · simpa only [he, act] using hn

private theorem recompose_correct (Δ : Bounds) (ms : List ModExpr) (a : Ty) :
    Subtype Δ (act ms a) (.modal a (ComparisonPartialModes.recompose ms)) ∧
      Subtype Δ (.modal a (ComparisonPartialModes.recompose ms)) (act ms a) := by
  match ms with
  | [] => exact ⟨.identityRev, .identity⟩
  | [m] => exact ⟨.refl, .refl⟩
  | m :: n :: ms =>
    have ih := recompose_correct Δ (.compose n m :: ms) a
    exact ⟨Subtype.compose.trans ih.1, ih.2.trans .composeRev⟩
termination_by ms.length

theorem peelFuel_recompose_correct {Δ : Bounds} (total : ModExpr → Bool)
    (htotal : ∀ m, total m = true → Submode Δ m m) (fuel : Nat) (t : Ty) :
    let result := peelFuel total fuel t
    Subtype Δ t (.modal result.base (ComparisonPartialModes.recompose result.labels)) ∧
      Subtype Δ (.modal result.base (ComparisonPartialModes.recompose result.labels)) t :=
  ⟨(peelFuel_correct total htotal _ t).1.trans (recompose_correct Δ _ _).1,
    (recompose_correct Δ _ _).2.trans (peelFuel_correct total htotal _ t).2⟩

theorem peel_correct {Δ : Bounds} (total : ModExpr → Bool)
    (htotal : ∀ m, total m = true → Submode Δ m m) (t : Ty) :
    let result := peel total t
    Subtype Δ t (.modal result.base (ComparisonPartialModes.recompose result.labels)) ∧
      Subtype Δ (.modal result.base (ComparisonPartialModes.recompose result.labels)) t :=
  peelFuel_recompose_correct total htotal _ t

theorem stripTotal_spec {total : ModExpr → Bool} {left right : Ty} {step : TotalStep}
    (h : stripTotal total left right = some step) :
    step.bases = ((peelFuel total 1 left).base, (peelFuel total 1 right).base) ∧
      step.labels = (ComparisonPartialModes.recompose (peelFuel total 1 left).labels,
        ComparisonPartialModes.recompose (peelFuel total 1 right).labels) := by
  unfold stripTotal at h
  dsimp only at h
  split at h
  · contradiction
  · cases h
    exact ⟨rfl, rfl⟩

/-- Scalar suffix inequalities transport a bare base comparison without
requiring either opaque base to be defined. -/
theorem stripTotal_correct {Δ : Bounds} (total : ModExpr → Bool)
    (htotal : ∀ m, total m = true → Submode Δ m m)
    {left right : Ty} {step : TotalStep} (h : stripTotal total left right = some step)
    (hab : Subtype Δ step.bases.1 step.bases.2)
    (hmn : Submode Δ step.labels.1 step.labels.2) : Subtype Δ left right := by
  obtain ⟨hb, hm⟩ := stripTotal_spec h
  rw [hb] at hab
  rw [hm] at hmn
  exact (peelFuel_recompose_correct total htotal 1 left).1.trans
    ((Subtype.congr hab hmn).trans (peelFuel_recompose_correct total htotal 1 right).2)

theorem suffixGoal_correct {Δ : Bounds} (total : ModExpr → Bool)
    (htotal : ∀ m, total m = true → Submode Δ m m)
    {left right : Ty} {m n : ModExpr} (h : suffixGoal total left right = some (m, n))
    (hmn : Submode Δ m n) : Subtype Δ left right := by
  simp only [suffixGoal] at h
  split at h
  · next he =>
    cases Option.some.inj h
    exact (peel_correct total htotal left).1.trans
      ((Subtype.congr (beq_iff_eq.mp he ▸ Subtype.refl) hmn).trans
        (peel_correct total htotal right).2)
  · contradiction

theorem isTotal_defined {Δ : Bounds} {known : List ModExpr}
    (hknown : ∀ m ∈ known, Entails Δ (.defined m)) {m : ModExpr}
    (h : isTotal known m = true) : Entails Δ (.defined m) := by
  induction m with
  | leftResidual a b _ _ | rightResidual a b _ _ =>
    exact hknown _ (List.contains_iff_mem.mp h)
  | const | var => intro η hη; rfl
  | compose a b iha ihb | meet a b iha ihb | join a b iha ihb =>
    simp only [isTotal, Bool.and_eq_true] at h
    intro η hη
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (iha h.1 η hη)
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (ihb h.2 η hη)
    simp [ModExpr.WellFormed, ModExpr.eval, hx, hy]
  | close a ih | closeInv a ih | future a ih | capture a ih =>
    intro η hη
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (ih h η hη)
    simp [ModExpr.WellFormed, ModExpr.eval, hx]

theorem isTotal_submode {Δ : Bounds} {known : List ModExpr}
    (hknown : ∀ m ∈ known, Entails Δ (.defined m)) {m : ModExpr}
    (h : isTotal known m = true) : Submode Δ m m :=
  .refl (isTotal_defined hknown h)

theorem checkTotal_sound {fuel : Nat} {Δ : Bounds} {expressions known : List ModExpr}
    (h : checkTotal fuel Δ expressions = .success known) :
    ∀ m ∈ known, Entails Δ (.defined m) := by
  induction expressions generalizing known with
  | nil => cases h; simp
  | cons e es ih =>
    cases he : ConcreteBackend.entails fuel Δ [.defined e] <;>
      simp only [checkTotal, he, bind, pure, RunResult.bind] at h <;> try contradiction
    cases hr : checkTotal fuel Δ es <;> simp only [hr] at h <;> try contradiction
    cases h
    split
    · next hv =>
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨fun η hη => ((ConcreteBackend.entails_correct he).mp hv η hη)
        (.defined e) (by simp), ih hr⟩
    · exact ih hr

theorem knownTotal_sound {fuel : Nat} {Δ : Bounds} {expressions known : List ModExpr}
    (h : knownTotal fuel Δ expressions = .success known) :
    ∀ m ∈ known, Entails Δ (.defined m) :=
  checkTotal_sound h

theorem knownTotal_submode {fuel : Nat} {Δ : Bounds} {expressions known : List ModExpr}
    (h : knownTotal fuel Δ expressions = .success known) {m : ModExpr}
    (hm : isTotal known m = true) : Submode Δ m m :=
  isTotal_submode (knownTotal_sound h) hm

private theorem dropIdentity_correct (Δ : Bounds) {t a : Ty} (h : dropIdentity t = some a) :
    Subtype Δ t a ∧ Subtype Δ a t := by
  cases t <;> simp [dropIdentity] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨.identity, .identityRev⟩

private theorem stripSharedDirect_correct {Δ : Bounds} (total : ModExpr → Bool)
    (htotal : ∀ m, total m = true → Submode Δ m m)
    {left right a b : Ty} (h : stripSharedDirect total left right = some (a, b))
    (hab : Subtype Δ a b) : Subtype Δ left right := by
  cases hl : dropIdentity left with
  | some t =>
    simp only [stripSharedDirect, hl] at h
    cases Option.some.inj h
    exact (dropIdentity_correct Δ hl).1.trans hab
  | none =>
    cases hr : dropIdentity right with
    | some t =>
      simp only [stripSharedDirect, hl, hr] at h
      cases Option.some.inj h
      exact hab.trans (dropIdentity_correct Δ hr).2
    | none =>
      cases left <;> cases right <;>
        simp only [stripSharedDirect, hl, hr] at h <;> try contradiction
      split at h
      · next hm =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hm
        cases Option.some.inj h
        exact .congr hab (hm.1 ▸ htotal _ hm.2)
      · contradiction

theorem stripShared_correct {Δ : Bounds} (total : ModExpr → Bool)
    (htotal : ∀ m, total m = true → Submode Δ m m)
    {left right a b : Ty} (h : stripShared total left right = some (a, b))
    (hab : Subtype Δ a b) : Subtype Δ left right := by
  cases hd : stripSharedDirect total left right with
  | some pair =>
    simp only [stripShared, hd] at h
    exact stripSharedDirect_correct total htotal (hd.trans h) hab
  | none =>
    simp only [stripShared, hd] at h
    cases hn : stripSharedDirect total (ComparisonPartialModes.normalizeOuter left)
        (ComparisonPartialModes.normalizeOuter right) <;> simp only [hn] at h
    · split at h
      · contradiction
      · cases Option.some.inj h
        exact (ComparisonPartialModes.normalizeOuter_correct Δ left).1.trans
          (hab.trans (ComparisonPartialModes.normalizeOuter_correct Δ right).2)
    · exact (ComparisonPartialModes.normalizeOuter_correct Δ left).1.trans
        ((stripSharedDirect_correct total htotal (hn.trans h) hab).trans
          (ComparisonPartialModes.normalizeOuter_correct Δ right).2)

end ModalityInference.ComparisonBody
