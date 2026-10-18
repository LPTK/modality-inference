import ModalityInference.Proofs.ComparisonDefinedCoverMonotonicity

/-! Defined comparisons admit root-level proof traces with no partial
intermediate terms. Structural premises remain full algebra comparisons, so an
observer may interpret a constructor through observers of its child algebras. -/

namespace ModalityInference.ComparisonDefinedRoot

/-- Root-level proof traces with defined terms throughout. Constructor children
may use the full comparison relation. -/
inductive Derivation (Δ : Bounds) : CompareTy → CompareTy → Prop where
  | refl {a} : a.WellShaped Δ → a.DefinedUnder Δ → Derivation Δ a a
  | bound {a b} : Constraint.sub a b ∈ Δ →
      (CompareTy.ofTy a).DefinedUnder Δ → (CompareTy.ofTy b).DefinedUnder Δ →
      Derivation Δ (.ofTy a) (.ofTy b)
  | identity {a} : a.WellShaped Δ → a.DefinedUnder Δ →
      Derivation Δ (.modal a .epsilon) a
  | identityRev {a} : a.WellShaped Δ → a.DefinedUnder Δ →
      Derivation Δ a (.modal a .epsilon)
  | compose {a m n} : a.WellShaped Δ → a.DefinedUnder Δ →
      Entails Δ (.defined m) → Entails Δ (.defined n) →
      Derivation Δ (.modal (.modal a m) n) (.modal a (.compose m n))
  | composeRev {a m n} : a.WellShaped Δ → a.DefinedUnder Δ →
      Entails Δ (.defined m) → Entails Δ (.defined n) →
      Derivation Δ (.modal a (.compose m n)) (.modal (.modal a m) n)
  | trans {a b c} : Derivation Δ a b → Derivation Δ b c → Derivation Δ a c
  | congr {a b m n} : Derivation Δ a b → Submode Δ m n →
      Derivation Δ (.modal a m) (.modal b n)
  | prod {a b c d m} : AlgebraSubtype Δ (.modal a m) (.modal c m) →
      AlgebraSubtype Δ (.modal b m) (.modal d m) →
      (.modal (.prod a b) m : CompareTy).DefinedUnder Δ →
      (.modal (.prod c d) m : CompareTy).DefinedUnder Δ →
      Derivation Δ (.modal (.prod a b) m) (.modal (.prod c d) m)
  | sum {a b c d m} : AlgebraSubtype Δ (.modal a m) (.modal c m) →
      AlgebraSubtype Δ (.modal b m) (.modal d m) →
      (.modal (.sum a b) m : CompareTy).DefinedUnder Δ →
      (.modal (.sum c d) m : CompareTy).DefinedUnder Δ →
      Derivation Δ (.modal (.sum a b) m) (.modal (.sum c d) m)
  | fn {a b c d m n} : AlgebraSubtype Δ c a → AlgebraSubtype Δ b d →
      Submode Δ m (.compose n .top) →
      (.modal (.fn a b) m : CompareTy).DefinedUnder Δ →
      (.modal (.fn c d) n : CompareTy).DefinedUnder Δ →
      Derivation Δ (.modal (.fn a b) m) (.modal (.fn c d) n)
  | joinLeft {a b} : ComparisonAlgebra.Compatible Δ a b → Derivation Δ a (.join a b)
  | joinRight {a b} : ComparisonAlgebra.Compatible Δ a b → Derivation Δ b (.join a b)
  | joinLeast {a b c} : Derivation Δ a c → Derivation Δ b c →
      Derivation Δ (.join a b) c
  | meetLeft {a b} : ComparisonAlgebra.Compatible Δ a b → Derivation Δ (.meet a b) a
  | meetRight {a b} : ComparisonAlgebra.Compatible Δ a b → Derivation Δ (.meet a b) b
  | meetGreatest {a b c} : Derivation Δ a b → Derivation Δ a c →
      Derivation Δ a (.meet b c)
  | equation {a b} : ComparisonAlgebra.Equation Δ a b → Derivation Δ a b
  | equationRev {a b} : ComparisonAlgebra.Equation Δ a b → Derivation Δ b a
  | clamp {b a t m} : ComparisonAlgebra.Compatible Δ b a →
      ComparisonAlgebra.Compatible Δ a t → Entails Δ (.defined m) →
      Derivation Δ b a → Derivation Δ a t →
      Derivation Δ (.modal a m) (.meet (.join a (.modal b m)) (.modal t m))
  | clampRev {b a t m} : ComparisonAlgebra.Compatible Δ b a →
      ComparisonAlgebra.Compatible Δ a t → Entails Δ (.defined m) →
      Derivation Δ b a → Derivation Δ a t →
      Derivation Δ (.meet (.join a (.modal b m)) (.modal t m)) (.modal a m)

theorem Derivation.subtype {Δ a b} (h : Derivation Δ a b) : AlgebraSubtype Δ a b := by
  induction h with
  | refl hs _ => exact .refl hs
  | bound h _ _ => exact .shaped (.bound h)
  | identity hs _ => exact .identity hs
  | identityRev hs _ => exact .identityRev hs
  | compose hs _ _ _ => exact .compose hs
  | composeRev hs _ _ _ => exact .composeRev hs
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congr _ hm ih => exact .congr ih hm
  | prod h₁ h₂ _ _ => exact .prod h₁ h₂
  | sum h₁ h₂ _ _ => exact .sum h₁ h₂
  | fn h₁ h₂ hm _ _ => exact .fn h₁ h₂ hm
  | joinLeft h => exact .shaped (.joinLeft h.1)
  | joinRight h => exact .shaped (.joinRight h.1)
  | joinLeast _ _ ih₁ ih₂ => exact .joinLeast ih₁ ih₂
  | meetLeft h => exact .shaped (.meetLeft h.1)
  | meetRight h => exact .shaped (.meetRight h.1)
  | meetGreatest _ _ ih₁ ih₂ => exact .meetGreatest ih₁ ih₂
  | equation h => exact .equation h
  | equationRev h => exact .equationRev h
  | clamp h₁ h₂ hm _ _ ih₁ ih₂ => exact .clamp h₁ h₂ hm ih₁ ih₂
  | clampRev h₁ h₂ hm _ _ ih₁ ih₂ => exact .clampRev h₁ h₂ hm ih₁ ih₂

theorem Derivation.defined {Δ a b} (h : Derivation Δ a b) :
    a.DefinedUnder Δ ∧ b.DefinedUnder Δ := by
  have he : Entails Δ (.defined .epsilon) := by intro η _; rfl
  induction h with
  | refl _ hd | bound _ hd hd' => first | exact ⟨hd, hd⟩ | exact ⟨hd, hd'⟩
  | identity _ hd => exact ⟨CompareTy.definedUnder_modal_iff.mpr ⟨hd, he⟩, hd⟩
  | identityRev _ hd => exact ⟨hd, CompareTy.definedUnder_modal_iff.mpr ⟨hd, he⟩⟩
  | compose _ hd hm hn =>
    exact ⟨CompareTy.definedUnder_modal_iff.mpr ⟨CompareTy.definedUnder_modal_iff.mpr ⟨hd, hm⟩, hn⟩,
      CompareTy.definedUnder_modal_iff.mpr ⟨hd, Entails.defined_compose_iff.mpr ⟨hm, hn⟩⟩⟩
  | composeRev _ hd hm hn =>
    exact ⟨CompareTy.definedUnder_modal_iff.mpr ⟨hd, Entails.defined_compose_iff.mpr ⟨hm, hn⟩⟩,
      CompareTy.definedUnder_modal_iff.mpr ⟨CompareTy.definedUnder_modal_iff.mpr ⟨hd, hm⟩, hn⟩⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | congr _ hm ih => exact ⟨CompareTy.definedUnder_modal_iff.mpr ⟨ih.1, hm.defined.1⟩,
      CompareTy.definedUnder_modal_iff.mpr ⟨ih.2, hm.defined.2⟩⟩
  | prod _ _ hd₁ hd₂ | sum _ _ hd₁ hd₂ | fn _ _ _ hd₁ hd₂ => exact ⟨hd₁, hd₂⟩
  | joinLeft h => exact ⟨h.2.1, CompareTy.definedUnder_join_iff.mpr h.2⟩
  | joinRight h => exact ⟨h.2.2, CompareTy.definedUnder_join_iff.mpr h.2⟩
  | joinLeast _ _ ih₁ ih₂ => exact ⟨CompareTy.definedUnder_join_iff.mpr ⟨ih₁.1, ih₂.1⟩, ih₁.2⟩
  | meetLeft h => exact ⟨CompareTy.definedUnder_meet_iff.mpr h.2, h.2.1⟩
  | meetRight h => exact ⟨CompareTy.definedUnder_meet_iff.mpr h.2, h.2.2⟩
  | meetGreatest _ _ ih₁ ih₂ => exact ⟨ih₁.1, CompareTy.definedUnder_meet_iff.mpr ⟨ih₁.2, ih₂.2⟩⟩
  | equation h => exact ComparisonDefinedCovers.equation_defined h
  | equationRev h => exact (ComparisonDefinedCovers.equation_defined h).symm
  | clamp h₁ h₂ hm _ _ _ _ => exact ComparisonDefinedCovers.clamp_endpoints_defined h₁ h₂ hm
  | clampRev h₁ h₂ hm _ _ _ _ => exact (ComparisonDefinedCovers.clamp_endpoints_defined h₁ h₂ hm).symm

open ComparisonDefinedCovers

/-- An absent lower approximation is the formal bottom used in this proof. -/
def Lift (Δ : Bounds) : Option CompareTy → Option CompareTy → Prop
  | none, _ => True
  | some _, none => False
  | some a, some b => Derivation Δ a b

def Ready (Δ : Bounds) (s : ComparisonShape) (x : Option CompareTy) : Prop :=
  OfShape Δ s x ∧ ∀ a, x = some a → a.DefinedUnder Δ

theorem Ready.normal {Δ a} (ha : CompareTy.WellShaped Δ a) (lower : Bool) :
    Ready Δ a.shape (normal Δ lower a) :=
  ⟨OfShape.normal ha lower, fun _ h => (normal_sound ha lower h).1⟩

theorem Ready.rebase {Δ s t x} (h : Ready Δ s x)
    (he : ComparisonShape.Equivalent Δ s t) : Ready Δ t x :=
  ⟨h.1.rebase he, h.2⟩

theorem Ready.compatible {Δ s a b} (ha : Ready Δ s (some a))
    (hb : Ready Δ s (some b)) : ComparisonAlgebra.Compatible Δ a b :=
  ⟨ha.1.compatible hb.1, ha.2 _ rfl, hb.2 _ rfl⟩

theorem Lift.refl {Δ s x} (hx : Ready Δ s x) : Lift Δ x x := by
  cases x with
  | none => trivial
  | some a => exact Derivation.refl (hx.1 _ rfl).1 (hx.2 _ rfl)

theorem Lift.trans {Δ x y z} (hxy : Lift Δ x y) (hyz : Lift Δ y z) : Lift Δ x z := by
  cases x <;> cases y <;> cases z <;> simp_all [Lift]
  exact hxy.trans hyz

theorem Lift.modal {Δ x y m n} (h : Lift Δ x y) (hm : Submode Δ m n) :
    Lift Δ (x.map (CompareTy.modal · m)) (y.map (CompareTy.modal · n)) := by
  cases x <;> cases y <;> simp_all [Lift]
  exact .congr h hm

theorem Lift.join_left {Δ s x y} (hx : Ready Δ s x) (hy : Ready Δ s y) :
    Lift Δ x (loose .join x y) := by
  cases x <;> cases y <;> simp_all [Lift, loose]
  · exact .refl (hx.1 _ rfl).1 (hx.2 _ rfl)
  · exact .joinLeft (hx.compatible hy)

theorem Lift.join_right {Δ s x y} (hx : Ready Δ s x) (hy : Ready Δ s y) :
    Lift Δ y (loose .join x y) := by
  cases x <;> cases y <;> simp_all [Lift, loose]
  · exact .refl (hy.1 _ rfl).1 (hy.2 _ rfl)
  · exact .joinRight (hx.compatible hy)

theorem Lift.meet_left {Δ s x y} (hx : Ready Δ s x) (hy : Ready Δ s y) :
    Lift Δ (strict .meet x y) x := by
  cases x <;> cases y <;> simp_all [Lift, strict]
  exact .meetLeft (hx.compatible hy)

theorem Lift.meet_right {Δ s x y} (hx : Ready Δ s x) (hy : Ready Δ s y) :
    Lift Δ (strict .meet x y) y := by
  cases x <;> cases y <;> simp_all [Lift, strict]
  exact .meetRight (hx.compatible hy)

theorem Lift.join_least {Δ x y z} (hx : Lift Δ x z) (hy : Lift Δ y z) :
    Lift Δ (loose .join x y) z := by
  cases x <;> cases y <;> cases z <;> simp_all [Lift, loose]
  exact .joinLeast hx hy

theorem Lift.meet_greatest {Δ x y z} (hx : Lift Δ x y) (hy : Lift Δ x z) :
    Lift Δ x (strict .meet y z) := by
  cases x <;> cases y <;> cases z <;> simp_all [Lift, strict]
  exact .meetGreatest hx hy

noncomputable section
attribute [local instance] Classical.propDecidable

theorem normal_identity {Δ a} (hs : CompareTy.WellShaped Δ a) :
    Lift Δ (normal Δ true (.modal a .epsilon)) (normal Δ true a) ∧
    Lift Δ (normal Δ true a) (normal Δ true (.modal a .epsilon)) := by
  have he : Entails Δ (.defined .epsilon) := by intro η _; rfl
  simp only [normal, if_pos he]
  cases hx : normal Δ true a with
  | none => exact ⟨trivial, trivial⟩
  | some x =>
    have hh := normal_sound hs true hx
    exact ⟨.identity hh.2.shape.1 hh.1, .identityRev hh.2.shape.1 hh.1⟩

theorem normal_compose {Δ a} (hs : CompareTy.WellShaped Δ a) (m n : ModExpr) :
    Lift Δ (normal Δ true (.modal (.modal a m) n))
      (normal Δ true (.modal a (.compose m n))) ∧
    Lift Δ (normal Δ true (.modal a (.compose m n)))
      (normal Δ true (.modal (.modal a m) n)) := by
  by_cases hmn : Entails Δ (.defined (.compose m n))
  · obtain ⟨hm, hn⟩ := Entails.defined_compose_iff.mp hmn
    simp only [normal, if_pos hm, if_pos hn, if_pos hmn]
    cases hx : normal Δ true a with
    | none => exact ⟨trivial, trivial⟩
    | some x =>
      have hh := normal_sound hs true hx
      exact ⟨.compose hh.2.shape.1 hh.1 hm hn, .composeRev hh.2.shape.1 hh.1 hm hn⟩
  · by_cases hn : Entails Δ (.defined n)
    · have hm : ¬ Entails Δ (.defined m) := fun hm =>
        hmn (Entails.defined_compose_iff.mpr ⟨hm, hn⟩)
      simp [normal, hn, hm, hmn, Lift]
    · simp [normal, hn, hmn, Lift]

private theorem modal_binary {Δ a b c d m} {op : CompareTy → CompareTy → CompareTy}
    (step : ∀ {w x y z}, AlgebraSubtype Δ (.modal w m) (.modal y m) →
      AlgebraSubtype Δ (.modal x m) (.modal z m) →
      (.modal (op w x) m : CompareTy).DefinedUnder Δ →
      (.modal (op y z) m : CompareTy).DefinedUnder Δ →
      Derivation Δ (.modal (op w x) m) (.modal (op y z) m))
    (ha : CoverLe Δ true (a.map (CompareTy.modal · m)) (c.map (CompareTy.modal · m)))
    (hb : CoverLe Δ true (b.map (CompareTy.modal · m)) (d.map (CompareTy.modal · m)))
    (hs : ∀ x, (strict op a b).map (CompareTy.modal · m) = some x → x.DefinedUnder Δ)
    (ht : ∀ x, (strict op c d).map (CompareTy.modal · m) = some x → x.DefinedUnder Δ) :
    Lift Δ ((strict op a b).map (CompareTy.modal · m))
      ((strict op c d).map (CompareTy.modal · m)) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [Lift, strict, CoverLe]

private theorem modal_function {Δ a b c d m n}
    (ha : CoverLe Δ false c a) (hb : CoverLe Δ true b d)
    (hm : Submode Δ m (.compose n .top))
    (hs : ∀ x, (strict .fn a b).map (CompareTy.modal · m) = some x → x.DefinedUnder Δ)
    (ht : ∀ x, (strict .fn c d).map (CompareTy.modal · n) = some x → x.DefinedUnder Δ) :
    Lift Δ ((strict .fn a b).map (CompareTy.modal · m))
      ((strict .fn c d).map (CompareTy.modal · n)) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [Lift, strict, CoverLe]
  exact .fn ha hb hm hs ht

theorem normal_prod {Δ a b c d m} (hΔ : Bounds.TypeBoundsDefined Δ)
    (ha : AlgebraSubtype Δ (.modal a m) (.modal c m))
    (hb : AlgebraSubtype Δ (.modal b m) (.modal d m)) :
    Lift Δ (normal Δ true (.modal (.prod a b) m))
      (normal Δ true (.modal (.prod c d) m)) := by
  by_cases hm : Entails Δ (.defined m)
  · have h₁ := ComparisonDefinedCovers.normal_monotone hΔ ha true
    have h₂ := ComparisonDefinedCovers.normal_monotone hΔ hb true
    have h₃ := (Ready.normal (AlgebraSubtype.prod ha hb).wellShaped_left true).2
    have h₄ := (Ready.normal (AlgebraSubtype.prod ha hb).wellShaped_right true).2
    simp only [normal, if_pos hm] at h₁ h₂ h₃ h₄ ⊢
    exact modal_binary Derivation.prod h₁ h₂ h₃ h₄
  · simp [normal, hm, Lift]

theorem normal_sum {Δ a b c d m} (hΔ : Bounds.TypeBoundsDefined Δ)
    (ha : AlgebraSubtype Δ (.modal a m) (.modal c m))
    (hb : AlgebraSubtype Δ (.modal b m) (.modal d m)) :
    Lift Δ (normal Δ true (.modal (.sum a b) m))
      (normal Δ true (.modal (.sum c d) m)) := by
  by_cases hm : Entails Δ (.defined m)
  · have h₁ := ComparisonDefinedCovers.normal_monotone hΔ ha true
    have h₂ := ComparisonDefinedCovers.normal_monotone hΔ hb true
    have h₃ := (Ready.normal (AlgebraSubtype.sum ha hb).wellShaped_left true).2
    have h₄ := (Ready.normal (AlgebraSubtype.sum ha hb).wellShaped_right true).2
    simp only [normal, if_pos hm] at h₁ h₂ h₃ h₄ ⊢
    exact modal_binary Derivation.sum h₁ h₂ h₃ h₄
  · simp [normal, hm, Lift]

theorem normal_fn {Δ a b c d m n} (hΔ : Bounds.TypeBoundsDefined Δ)
    (ha : AlgebraSubtype Δ c a) (hb : AlgebraSubtype Δ b d)
    (hm : Submode Δ m (.compose n .top)) :
    Lift Δ (normal Δ true (.modal (.fn a b) m))
      (normal Δ true (.modal (.fn c d) n)) := by
  have hn := (Entails.defined_compose_iff.mp hm.defined.2).1
  have h₁ := ComparisonDefinedCovers.normal_monotone hΔ ha false
  have h₂ := ComparisonDefinedCovers.normal_monotone hΔ hb true
  have h₃ := (Ready.normal (AlgebraSubtype.fn ha hb hm).wellShaped_left true).2
  have h₄ := (Ready.normal (AlgebraSubtype.fn ha hb hm).wellShaped_right true).2
  simp only [normal, if_pos hm.defined.1, if_pos hn, Bool.not_true] at h₃ h₄ ⊢
  exact modal_function h₁ h₂ hm h₃ h₄

theorem normal_shaped {Δ a b} (hΔ : Bounds.TypeBoundsDefined Δ)
    (h : ShapedSubtype Δ a b) : Lift Δ (normal Δ true a) (normal Δ true b) := by
  induction h with
  | refl hs => exact Lift.refl (Ready.normal hs true)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | bound h =>
    have h₁ := (CompareTy.definedUnder_ofTy _ _).mpr (hΔ _ _ h).1
    have h₂ := (CompareTy.definedUnder_ofTy _ _).mpr (hΔ _ _ h).2
    rw [normal_defined h₁, normal_defined h₂]
    exact Derivation.bound h h₁ h₂
  | identity hs => exact (normal_identity hs).1
  | identityRev hs => exact (normal_identity hs).2
  | compose hs => exact (normal_compose hs _ _).1
  | composeRev hs => exact (normal_compose hs _ _).2
  | congr _ hm ih =>
    simpa only [normal, if_pos hm.defined.1, if_pos hm.defined.2] using ih.modal hm
  | prod ha hb _ _ => exact normal_prod hΔ (.shaped ha) (.shaped hb)
  | sum ha hb _ _ => exact normal_sum hΔ (.shaped ha) (.shaped hb)
  | fn ha hb hm _ _ => exact normal_fn hΔ (.shaped ha) (.shaped hb) hm
  | joinLeft hs =>
    exact Lift.join_left (Ready.normal hs.1 true)
      ((Ready.normal hs.2.1 true).rebase hs.2.2.symm)
  | joinRight hs =>
    exact Lift.join_right (Ready.normal hs.1 true)
      ((Ready.normal hs.2.1 true).rebase hs.2.2.symm)
  | joinLeast _ _ ih₁ ih₂ => exact ih₁.join_least ih₂
  | meetLeft hs =>
    exact Lift.meet_left (Ready.normal hs.1 true)
      ((Ready.normal hs.2.1 true).rebase hs.2.2.symm)
  | meetRight hs =>
    exact Lift.meet_right (Ready.normal hs.1 true)
      ((Ready.normal hs.2.1 true).rebase hs.2.2.symm)
  | meetGreatest _ _ ih₁ ih₂ => exact ih₁.meet_greatest ih₂

theorem normal_derivation {Δ a b} (hΔ : Bounds.TypeBoundsDefined Δ)
    (h : AlgebraSubtype Δ a b) : Lift Δ (normal Δ true a) (normal Δ true b) := by
  induction h with
  | shaped h => exact normal_shaped hΔ h
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | equation h =>
    rw [normal_defined (equation_defined h).1, normal_defined (equation_defined h).2]
    exact Derivation.equation h
  | equationRev h =>
    rw [normal_defined (equation_defined h).1, normal_defined (equation_defined h).2]
    exact Derivation.equationRev h
  | congr _ hm ih =>
    simpa only [normal, if_pos hm.defined.1, if_pos hm.defined.2] using ih.modal hm
  | prod ha hb _ _ => exact normal_prod hΔ ha hb
  | sum ha hb _ _ => exact normal_sum hΔ ha hb
  | fn ha hb hm _ _ => exact normal_fn hΔ ha hb hm
  | joinLeast _ _ ih₁ ih₂ => exact ih₁.join_least ih₂
  | meetGreatest _ _ ih₁ ih₂ => exact ih₁.meet_greatest ih₂
  | clamp h₁ h₂ hm _ _ ih₁ ih₂ =>
    have hd := clamp_endpoints_defined h₁ h₂ hm
    rw [normal_defined hd.1, normal_defined hd.2]
    rw [normal_defined h₁.2.1, normal_defined h₁.2.2] at ih₁
    rw [normal_defined h₂.2.1, normal_defined h₂.2.2] at ih₂
    exact Derivation.clamp h₁ h₂ hm ih₁ ih₂
  | clampRev h₁ h₂ hm _ _ ih₁ ih₂ =>
    have hd := clamp_endpoints_defined h₁ h₂ hm
    rw [normal_defined hd.1, normal_defined hd.2]
    rw [normal_defined h₁.2.1, normal_defined h₁.2.2] at ih₁
    rw [normal_defined h₂.2.1, normal_defined h₂.2.2] at ih₂
    exact Derivation.clampRev h₁ h₂ hm ih₁ ih₂

/-- Partial intermediate branches can be pruned from the root proof trace.
The child premises of structural steps remain full algebra comparisons. -/
theorem derivation {Δ a b} (hΔ : Bounds.TypeBoundsDefined Δ)
    (ha : CompareTy.DefinedUnder a Δ) (hb : CompareTy.DefinedUnder b Δ)
    (h : AlgebraSubtype Δ a b) : Derivation Δ a b := by
  have hh := normal_derivation hΔ h
  simpa only [normal_defined ha, normal_defined hb, Lift] using hh

theorem derivation_iff {Δ a b} (hΔ : Bounds.TypeBoundsDefined Δ)
    (ha : CompareTy.DefinedUnder a Δ) (hb : CompareTy.DefinedUnder b Δ) :
    Derivation Δ a b ↔ AlgebraSubtype Δ a b :=
  ⟨Derivation.subtype, derivation hΔ ha hb⟩

end

end ModalityInference.ComparisonDefinedRoot
