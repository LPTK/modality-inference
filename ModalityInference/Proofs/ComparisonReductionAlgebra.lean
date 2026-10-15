import ModalityInference.ComparisonReduction
import ModalityInference.Proofs.ComparisonAlgebra
import ModalityInference.Proofs.ComparisonBody
import ModalityInference.Proofs.SolverLocalSoundness
import ModalityInference.Proofs.TypingAdmissibility

namespace ModalityInference

theorem CompareSubstitution.type_wellShaped {Δ : Bounds} {σ : CompareSubstitution}
    (hσ : σ.WellShaped Δ) (v : TypeVar) : (σ.type v).WellShaped Δ := by
  cases v with
  | rigid n => trivial
  | flex n =>
    cases h : σ.types.lookup n with
    | none => simp [CompareSubstitution.type, h, CompareTy.WellShaped]
    | some t =>
      obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp h
      simpa [CompareSubstitution.type, h] using hσ (n, t) (by simp [he])

theorem CompareSubstitution.ty_wellShaped {Δ : Bounds} {σ : CompareSubstitution}
    (hσ : σ.WellShaped Δ) (t : Ty) : (σ.ty t).WellShaped Δ := by
  induction t <;> simp_all [CompareSubstitution.ty, CompareTy.ofTy, CompareTy.subst,
    CompareTy.WellShaped, CompareSubstitution.type_wellShaped hσ]

namespace AlgebraSubtype

theorem identity {Δ a} (ha : a.WellShaped Δ) :
    AlgebraSubtype Δ (.modal a .epsilon) a := .shaped (.identity ha)

theorem identityRev {Δ a} (ha : a.WellShaped Δ) :
    AlgebraSubtype Δ a (.modal a .epsilon) := .shaped (.identityRev ha)

theorem compose {Δ a m n} (ha : a.WellShaped Δ) :
    AlgebraSubtype Δ (.modal (.modal a m) n) (.modal a (.compose m n)) :=
  .shaped (.compose ha)

theorem composeRev {Δ a m n} (ha : a.WellShaped Δ) :
    AlgebraSubtype Δ (.modal a (.compose m n)) (.modal (.modal a m) n) :=
  .shaped (.composeRev ha)

theorem modal_intersection {Δ a b m n}
    (h : AlgebraSubtype Δ (.modal a m) (.modal b n)) (hmn : Submode Δ m n) :
    AlgebraSubtype Δ (.modal a (.compose m n)) (.modal b (.compose m n)) := by
  refine (AlgebraSubtype.congr (.refl (a := a) h.shape_invariant.1)
    (n := .compose m (.compose m n)) ?_).trans
    ((AlgebraSubtype.composeRev (a := a) h.shape_invariant.1).trans
      ((AlgebraSubtype.congr h (m := .compose m n) (n := .compose m n) ?_).trans
        ((AlgebraSubtype.compose (a := b) h.shape_invariant.2.1).trans
          (.congr (.refl (a := b) h.shape_invariant.2.1) ?_))))
  all_goals apply Submode.valid
  all_goals intro η hη
  all_goals obtain ⟨x, y, hx, hy, _⟩ := hmn.denote hη
  all_goals simp [ModExpr.Below, ModExpr.eval, hx, hy]

theorem prod_cross {Δ a b c d m n}
    (ha : AlgebraSubtype Δ (.modal a m) (.modal c n))
    (hb : AlgebraSubtype Δ (.modal b m) (.modal d n)) (hmn : Submode Δ m n) :
    AlgebraSubtype Δ (.modal (.prod a b) m) (.modal (.prod c d) n) :=
  (AlgebraSubtype.congr (.refl (a := .prod a b) ⟨ha.shape_invariant.1, hb.shape_invariant.1⟩)
    hmn.compose_between.1).trans
    ((AlgebraSubtype.prod (ha.modal_intersection hmn) (hb.modal_intersection hmn)).trans
      (.congr (.refl (a := .prod c d) ⟨ha.shape_invariant.2.1, hb.shape_invariant.2.1⟩)
        hmn.compose_between.2))

theorem sum_cross {Δ a b c d m n}
    (ha : AlgebraSubtype Δ (.modal a m) (.modal c n))
    (hb : AlgebraSubtype Δ (.modal b m) (.modal d n)) (hmn : Submode Δ m n) :
    AlgebraSubtype Δ (.modal (.sum a b) m) (.modal (.sum c d) n) :=
  (AlgebraSubtype.congr (.refl (a := .sum a b) ⟨ha.shape_invariant.1, hb.shape_invariant.1⟩)
    hmn.compose_between.1).trans
    ((AlgebraSubtype.sum (ha.modal_intersection hmn) (hb.modal_intersection hmn)).trans
      (.congr (.refl (a := .sum c d) ⟨ha.shape_invariant.2.1, hb.shape_invariant.2.1⟩)
        hmn.compose_between.2))

end AlgebraSubtype

namespace ComparisonInterpolation

theorem algebra_join_subtype_iff {Δ : Bounds} (head : CompareTy) (rest : List CompareTy)
    (t : CompareTy) : AlgebraSubtype Δ (join head rest) t ↔
      ∀ a ∈ head :: rest, AlgebraSubtype Δ a t := by
  induction rest generalizing head
  case nil => simp [join]
  case cons next rest ih =>
    constructor
    · intro h a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact .trans (.shaped (.joinLeft h.wellShaped_left)) h
      · exact (ih next).mp (.trans (.shaped (.joinRight h.wellShaped_left)) h) a ha
    · intro h
      exact .joinLeast (h head (by simp))
        ((ih next).mpr (fun a ha => h a (List.mem_cons_of_mem _ ha)))

theorem algebra_subtype_meet_iff {Δ : Bounds} (head : CompareTy) (rest : List CompareTy)
    (t : CompareTy) : AlgebraSubtype Δ t (meet head rest) ↔
      ∀ a ∈ head :: rest, AlgebraSubtype Δ t a := by
  induction rest generalizing head
  case nil => simp [meet]
  case cons next rest ih =>
    constructor
    · intro h a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact .trans h (.shaped (.meetLeft h.wellShaped_right))
      · exact (ih next).mp (.trans h (.shaped (.meetRight h.wellShaped_right))) a ha
    · intro h
      exact .meetGreatest (h head (by simp))
        ((ih next).mpr (fun a ha => h a (List.mem_cons_of_mem _ ha)))

theorem witness_algebra_interval {Δ : Bounds} {lower upper : List CompareTy}
    (hw : (witness lower upper).WellShaped Δ)
    (h : ∀ a ∈ lower, ∀ b ∈ upper, AlgebraSubtype Δ a b) :
    (∀ a ∈ lower, AlgebraSubtype Δ a (witness lower upper)) ∧
      ∀ b ∈ upper, AlgebraSubtype Δ (witness lower upper) b := by
  cases lower
  case nil =>
    cases upper
    case nil => simp
    case cons head rest =>
      exact ⟨by simp, (algebra_subtype_meet_iff head rest (meet head rest)).mp (.refl hw)⟩
  case cons head rest =>
    exact ⟨(algebra_join_subtype_iff head rest (join head rest)).mp (.refl hw),
      fun t ht => (algebra_join_subtype_iff head rest t).mpr (fun a ha => h a ha t ht)⟩

theorem join_subst (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    (head : CompareTy) (rest : List CompareTy) :
    (join head rest).subst ts ms = join (head.subst ts ms) (rest.map (CompareTy.subst ts ms)) := by
  induction rest generalizing head <;> simp_all [join, CompareTy.subst]

theorem meet_subst (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    (head : CompareTy) (rest : List CompareTy) :
    (meet head rest).subst ts ms = meet (head.subst ts ms) (rest.map (CompareTy.subst ts ms)) := by
  induction rest generalizing head <;> simp_all [meet, CompareTy.subst]

theorem witness_subst (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    (lower upper : List CompareTy) :
    (witness lower upper).subst ts ms =
      witness (lower.map (CompareTy.subst ts ms)) (upper.map (CompareTy.subst ts ms)) := by
  cases lower <;> cases upper <;> simp [witness, join_subst, meet_subst, CompareTy.subst]

end ComparisonInterpolation

namespace ComparisonReduction

variable {Δ : Bounds} {σ : CompareSubstitution}

theorem normalizeOuterFuel_algebra (hσ : σ.WellShaped Δ) (fuel : Nat) (t : Ty) :
    AlgebraSubtype Δ (σ.ty t) (σ.ty (ComparisonPartialModes.normalizeOuterFuel fuel t)) ∧
      AlgebraSubtype Δ (σ.ty (ComparisonPartialModes.normalizeOuterFuel fuel t)) (σ.ty t) := by
  induction fuel generalizing t with
  | zero => exact ⟨.refl (σ.ty_wellShaped hσ _), .refl (σ.ty_wellShaped hσ _)⟩
  | succ fuel ih =>
    cases t with
    | var | unit | credit | prod | sum | fn =>
      exact ⟨.refl (σ.ty_wellShaped hσ _), .refl (σ.ty_wellShaped hσ _)⟩
    | modal a m =>
      cases m <;> simp only [ComparisonPartialModes.normalizeOuterFuel]
      case compose m n =>
        exact ⟨(AlgebraSubtype.composeRev (σ.ty_wellShaped hσ a)).trans
            (ih (.modal (.modal a m) n)).1,
          (ih (.modal (.modal a m) n)).2.trans (.compose (σ.ty_wellShaped hσ a))⟩
      all_goals
        split
        · next h =>
          have he := beq_iff_eq.mp h
          rw [he]
          exact ⟨(AlgebraSubtype.identity (σ.ty_wellShaped hσ a)).trans (ih _).1,
            (ih _).2.trans (.identityRev (σ.ty_wellShaped hσ a))⟩
        · exact ⟨.refl (σ.ty_wellShaped hσ _), .refl (σ.ty_wellShaped hσ _)⟩

theorem normalizeOuter_algebra (hσ : σ.WellShaped Δ) (t : Ty) :
    AlgebraSubtype Δ (σ.ty t) (σ.ty (ComparisonPartialModes.normalizeOuter t)) ∧
      AlgebraSubtype Δ (σ.ty (ComparisonPartialModes.normalizeOuter t)) (σ.ty t) :=
  normalizeOuterFuel_algebra hσ _ t

theorem outer_algebra (hσ : σ.WellShaped Δ) (t : Ty)
    (hm : Submode Δ (t.outer.2.subst σ.mode) (t.outer.2.subst σ.mode)) :
    AlgebraSubtype Δ (σ.ty t) (.modal (σ.ty t.outer.1) (t.outer.2.subst σ.mode)) ∧
      AlgebraSubtype Δ (.modal (σ.ty t.outer.1) (t.outer.2.subst σ.mode)) (σ.ty t) := by
  induction t with
  | var | unit | credit | prod | sum | fn =>
    exact ⟨.identityRev (σ.ty_wellShaped hσ _), .identity (σ.ty_wellShaped hσ _)⟩
  | modal a m ih =>
    have hd := hm.defined.1
    change Entails Δ (.defined (.compose (a.outer.2.subst σ.mode) (m.subst σ.mode))) at hd
    have ha : Entails Δ (.defined (a.outer.2.subst σ.mode)) :=
      fun η hη => (ModExpr.wellFormed_compose.mp (hd η hη)).1
    have hmode : Entails Δ (.defined (m.subst σ.mode)) :=
      fun η hη => (ModExpr.wellFormed_compose.mp (hd η hη)).2
    exact ⟨(AlgebraSubtype.congr (ih (.refl ha)).1 (.refl hmode)).trans
        (.compose (σ.ty_wellShaped hσ _)),
      (AlgebraSubtype.composeRev (σ.ty_wellShaped hσ _)).trans
        (.congr (ih (.refl ha)).2 (.refl hmode))⟩

private theorem dropIdentity_algebra (hσ : σ.WellShaped Δ) {t a : Ty}
    (h : ComparisonBody.dropIdentity t = some a) :
    AlgebraSubtype Δ (σ.ty t) (σ.ty a) ∧ AlgebraSubtype Δ (σ.ty a) (σ.ty t) := by
  cases t <;> simp [ComparisonBody.dropIdentity] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨.identity (σ.ty_wellShaped hσ _), .identityRev (σ.ty_wellShaped hσ _)⟩

private theorem stripSharedDirect_algebra (hσ : σ.WellShaped Δ) (total : ModExpr → Bool)
    (htotal : ∀ m, total m = true → Submode Δ (m.subst σ.mode) (m.subst σ.mode))
    {left right a b : Ty} (h : ComparisonBody.stripSharedDirect total left right = some (a, b))
    (hab : AlgebraSubtype Δ (σ.ty a) (σ.ty b)) :
    AlgebraSubtype Δ (σ.ty left) (σ.ty right) := by
  cases hl : ComparisonBody.dropIdentity left with
  | some t =>
    simp only [ComparisonBody.stripSharedDirect, hl] at h
    cases Option.some.inj h
    exact (dropIdentity_algebra hσ hl).1.trans hab
  | none =>
    cases hr : ComparisonBody.dropIdentity right with
    | some t =>
      simp only [ComparisonBody.stripSharedDirect, hl, hr] at h
      cases Option.some.inj h
      exact hab.trans (dropIdentity_algebra hσ hr).2
    | none =>
      cases left <;> cases right <;>
        simp only [ComparisonBody.stripSharedDirect, hl, hr] at h <;> try contradiction
      split at h
      · next hm =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hm
        cases Option.some.inj h
        exact .congr hab (hm.1 ▸ htotal _ hm.2)
      · contradiction

theorem stripShared_algebra (hσ : σ.WellShaped Δ) (total : ModExpr → Bool)
    (htotal : ∀ m, total m = true → Submode Δ (m.subst σ.mode) (m.subst σ.mode))
    {left right a b : Ty} (h : ComparisonBody.stripShared total left right = some (a, b))
    (hab : AlgebraSubtype Δ (σ.ty a) (σ.ty b)) :
    AlgebraSubtype Δ (σ.ty left) (σ.ty right) := by
  cases hd : ComparisonBody.stripSharedDirect total left right with
  | some pair =>
    simp only [ComparisonBody.stripShared, hd] at h
    exact stripSharedDirect_algebra hσ total htotal (hd.trans h) hab
  | none =>
    simp only [ComparisonBody.stripShared, hd] at h
    cases hn : ComparisonBody.stripSharedDirect total (ComparisonPartialModes.normalizeOuter left)
        (ComparisonPartialModes.normalizeOuter right) <;> simp only [hn] at h
    · split at h
      · contradiction
      · cases Option.some.inj h
        exact (normalizeOuter_algebra hσ left).1.trans
          (hab.trans (normalizeOuter_algebra hσ right).2)
    · exact (normalizeOuter_algebra hσ left).1.trans
        ((stripSharedDirect_algebra hσ total htotal (hn.trans h) hab).trans
          (normalizeOuter_algebra hσ right).2)

private def act (σ : CompareSubstitution) : List ModExpr → CompareTy → CompareTy
  | [], a => a
  | m :: ms, a => .modal (act σ ms a) (m.subst σ.mode)

private theorem act_wellShaped {a : CompareTy} (ha : a.WellShaped Δ) (ms : List ModExpr) :
    (act σ ms a).WellShaped Δ := by
  induction ms with
  | nil => exact ha
  | cons m ms ih => exact ih

private theorem peelFuel_algebra (hσ : σ.WellShaped Δ) (total : ModExpr → Bool)
    (htotal : ∀ m, total m = true → Submode Δ (m.subst σ.mode) (m.subst σ.mode))
    (fuel : Nat) (t : Ty) :
    let result := ComparisonBody.peelFuel total fuel t
    AlgebraSubtype Δ (σ.ty t) (act σ result.labels (σ.ty result.base)) ∧
      AlgebraSubtype Δ (act σ result.labels (σ.ty result.base)) (σ.ty t) := by
  induction fuel generalizing t with
  | zero => exact ⟨.refl (σ.ty_wellShaped hσ _), .refl (σ.ty_wellShaped hσ _)⟩
  | succ fuel ih =>
    have hn := normalizeOuter_algebra hσ t
    cases he : ComparisonPartialModes.normalizeOuter t <;> simp only [ComparisonBody.peelFuel, he]
    all_goals try simpa only [he, act] using hn
    split
    · next hm =>
      exact ⟨(he ▸ hn.1).trans (.congr (ih _).1 (htotal _ hm)),
        (AlgebraSubtype.congr (ih _).2 (htotal _ hm)).trans (by simpa only [he] using hn.2)⟩
    · simpa only [he, act] using hn

private theorem recompose_algebra (ms : List ModExpr) (a : CompareTy)
    (ha : a.WellShaped Δ) :
    AlgebraSubtype Δ (act σ ms a)
        (.modal a ((ComparisonPartialModes.recompose ms).subst σ.mode)) ∧
      AlgebraSubtype Δ (.modal a ((ComparisonPartialModes.recompose ms).subst σ.mode))
        (act σ ms a) := by
  match ms with
  | [] => exact ⟨.identityRev ha, .identity ha⟩
  | [m] => exact ⟨.refl ha, .refl ha⟩
  | m :: n :: ms =>
    have ih := recompose_algebra (.compose n m :: ms) a ha
    exact ⟨(AlgebraSubtype.compose (act_wellShaped ha ms)).trans ih.1,
      ih.2.trans (.composeRev (act_wellShaped ha ms))⟩
termination_by ms.length

theorem peelFuel_recompose_algebra (hσ : σ.WellShaped Δ) (total : ModExpr → Bool)
    (htotal : ∀ m, total m = true → Submode Δ (m.subst σ.mode) (m.subst σ.mode))
    (fuel : Nat) (t : Ty) :
    let result := ComparisonBody.peelFuel total fuel t
    AlgebraSubtype Δ (σ.ty t) (.modal (σ.ty result.base)
        ((ComparisonPartialModes.recompose result.labels).subst σ.mode)) ∧
      AlgebraSubtype Δ (.modal (σ.ty result.base)
        ((ComparisonPartialModes.recompose result.labels).subst σ.mode)) (σ.ty t) :=
  ⟨(peelFuel_algebra hσ total htotal fuel t).1.trans
      (recompose_algebra _ _ (σ.ty_wellShaped hσ _)).1,
    (recompose_algebra _ _ (σ.ty_wellShaped hσ _)).2.trans
      (peelFuel_algebra hσ total htotal fuel t).2⟩

theorem peel_algebra (hσ : σ.WellShaped Δ) (total : ModExpr → Bool)
    (htotal : ∀ m, total m = true → Submode Δ (m.subst σ.mode) (m.subst σ.mode)) (t : Ty) :
    let result := ComparisonBody.peel total t
    AlgebraSubtype Δ (σ.ty t) (.modal (σ.ty result.base)
        ((ComparisonPartialModes.recompose result.labels).subst σ.mode)) ∧
      AlgebraSubtype Δ (.modal (σ.ty result.base)
        ((ComparisonPartialModes.recompose result.labels).subst σ.mode)) (σ.ty t) :=
  ⟨(peelFuel_algebra hσ total htotal _ t).1.trans
      (recompose_algebra _ _ (σ.ty_wellShaped hσ _)).1,
    (recompose_algebra _ _ (σ.ty_wellShaped hσ _)).2.trans
      (peelFuel_algebra hσ total htotal _ t).2⟩

theorem stripTotal_algebra (hσ : σ.WellShaped Δ) (total : ModExpr → Bool)
    (htotal : ∀ m, total m = true → Submode Δ (m.subst σ.mode) (m.subst σ.mode))
    {left right : Ty} {step : ComparisonBody.TotalStep}
    (h : ComparisonBody.stripTotal total left right = some step)
    (hab : AlgebraSubtype Δ (σ.ty step.bases.1) (σ.ty step.bases.2))
    (hmn : Submode Δ (step.labels.1.subst σ.mode) (step.labels.2.subst σ.mode)) :
    AlgebraSubtype Δ (σ.ty left) (σ.ty right) := by
  obtain ⟨hb, hm⟩ := ComparisonBody.stripTotal_spec h
  rw [hb] at hab
  rw [hm] at hmn
  exact (peelFuel_recompose_algebra hσ total htotal 1 left).1.trans
    ((AlgebraSubtype.congr hab hmn).trans (peelFuel_recompose_algebra hσ total htotal 1 right).2)

theorem suffixGoal_algebra (hσ : σ.WellShaped Δ) (total : ModExpr → Bool)
    (htotal : ∀ m, total m = true → Submode Δ (m.subst σ.mode) (m.subst σ.mode))
    {left right : Ty} {m n : ModExpr}
    (h : ComparisonBody.suffixGoal total left right = some (m, n))
    (hmn : Submode Δ (m.subst σ.mode) (n.subst σ.mode)) :
    AlgebraSubtype Δ (σ.ty left) (σ.ty right) := by
  simp only [ComparisonBody.suffixGoal] at h
  split at h
  · next he =>
    cases Option.some.inj h
    exact (peel_algebra hσ total htotal left).1.trans
      ((AlgebraSubtype.congr (beq_iff_eq.mp he ▸ .refl (σ.ty_wellShaped hσ _)) hmn).trans
        (peel_algebra hσ total htotal right).2)
  · contradiction

end ComparisonReduction

end ModalityInference
