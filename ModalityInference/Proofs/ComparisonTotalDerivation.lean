import ModalityInference.Proofs.ComparisonDefinedRoot

/-! Defined comparisons have derivations whose terms are defined at every
structural depth. This permits simultaneous interpretations in recursive
observer states without assuming the child interpretations are already models. -/
namespace ModalityInference.ComparisonTotalDerivation

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
  | prod {a b c d m} : Derivation Δ (.modal a m) (.modal c m) →
      Derivation Δ (.modal b m) (.modal d m) →
      (.modal (.prod a b) m : CompareTy).DefinedUnder Δ →
      (.modal (.prod c d) m : CompareTy).DefinedUnder Δ →
      Derivation Δ (.modal (.prod a b) m) (.modal (.prod c d) m)
  | sum {a b c d m} : Derivation Δ (.modal a m) (.modal c m) →
      Derivation Δ (.modal b m) (.modal d m) →
      (.modal (.sum a b) m : CompareTy).DefinedUnder Δ →
      (.modal (.sum c d) m : CompareTy).DefinedUnder Δ →
      Derivation Δ (.modal (.sum a b) m) (.modal (.sum c d) m)
  | fn {a b c d m n} : Derivation Δ c a → Derivation Δ b d →
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

theorem Derivation.root {Δ a b} (h : Derivation Δ a b) :
    ComparisonDefinedRoot.Derivation Δ a b := by
  induction h with
  | refl hs hd => exact .refl hs hd
  | bound h ha hb => exact .bound h ha hb
  | identity hs hd => exact .identity hs hd
  | identityRev hs hd => exact .identityRev hs hd
  | compose hs hd hm hn => exact .compose hs hd hm hn
  | composeRev hs hd hm hn => exact .composeRev hs hd hm hn
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congr _ hm ih => exact .congr ih hm
  | prod _ _ ha hb ih₁ ih₂ => exact .prod ih₁.subtype ih₂.subtype ha hb
  | sum _ _ ha hb ih₁ ih₂ => exact .sum ih₁.subtype ih₂.subtype ha hb
  | fn _ _ hm ha hb ih₁ ih₂ => exact .fn ih₁.subtype ih₂.subtype hm ha hb
  | joinLeft h => exact .joinLeft h
  | joinRight h => exact .joinRight h
  | joinLeast _ _ ih₁ ih₂ => exact .joinLeast ih₁ ih₂
  | meetLeft h => exact .meetLeft h
  | meetRight h => exact .meetRight h
  | meetGreatest _ _ ih₁ ih₂ => exact .meetGreatest ih₁ ih₂
  | equation h => exact .equation h
  | equationRev h => exact .equationRev h
  | clamp h₁ h₂ hm _ _ ih₁ ih₂ => exact .clamp h₁ h₂ hm ih₁ ih₂
  | clampRev h₁ h₂ hm _ _ ih₁ ih₂ => exact .clampRev h₁ h₂ hm ih₁ ih₂

theorem Derivation.subtype {Δ a b} (h : Derivation Δ a b) : AlgebraSubtype Δ a b :=
  h.root.subtype

theorem Derivation.defined {Δ a b} (h : Derivation Δ a b) :
    a.DefinedUnder Δ ∧ b.DefinedUnder Δ := h.root.defined

open ComparisonDefinedCovers
open ComparisonDefinedRoot (Ready)

/-- An absent lower approximation is bottom; an absent upper one is top.
The absent cases are proof markers, not returned type expressions. -/
def Lift (Δ : Bounds) (lower : Bool) : Option CompareTy → Option CompareTy → Prop
  | none, none => True
  | none, some _ => lower = true
  | some _, none => lower = false
  | some a, some b => Derivation Δ a b

theorem Lift.refl {Δ s x} (lower : Bool) (hx : Ready Δ s x) : Lift Δ lower x x := by
  cases x with
  | none => trivial
  | some a => exact Derivation.refl (hx.1 _ rfl).1 (hx.2 _ rfl)

theorem Lift.trans {Δ lower x y z} (hxy : Lift Δ lower x y)
    (hyz : Lift Δ lower y z) : Lift Δ lower x z := by
  cases lower <;> cases x <;> cases y <;> cases z <;> simp_all [Lift]
  all_goals exact hxy.trans hyz

theorem Lift.modal {Δ lower x y m n} (h : Lift Δ lower x y) (hm : Submode Δ m n) :
    Lift Δ lower (x.map (CompareTy.modal · m)) (y.map (CompareTy.modal · n)) := by
  cases x <;> cases y <;> simp_all [Lift]
  exact .congr h hm

theorem Lift.join_left {Δ s lower x y} (hx : Ready Δ s x) (hy : Ready Δ s y) :
    Lift Δ lower x (joinO lower x y) := by
  cases lower <;> cases x <;> cases y <;> simp_all [Lift, joinO, strict, loose]
  all_goals first
    | exact Derivation.refl (hx.1 _ rfl).1 (hx.2 _ rfl)
    | exact .joinLeft (hx.compatible hy)

theorem Lift.join_right {Δ s lower x y} (hx : Ready Δ s x) (hy : Ready Δ s y) :
    Lift Δ lower y (joinO lower x y) := by
  cases lower <;> cases x <;> cases y <;> simp_all [Lift, joinO, strict, loose]
  all_goals first
    | exact Derivation.refl (hy.1 _ rfl).1 (hy.2 _ rfl)
    | exact .joinRight (hx.compatible hy)

theorem Lift.meet_left {Δ s lower x y} (hx : Ready Δ s x) (hy : Ready Δ s y) :
    Lift Δ lower (meetO lower x y) x := by
  cases lower <;> cases x <;> cases y <;> simp_all [Lift, meetO, strict, loose]
  all_goals first
    | exact Derivation.refl (hx.1 _ rfl).1 (hx.2 _ rfl)
    | exact .meetLeft (hx.compatible hy)

theorem Lift.meet_right {Δ s lower x y} (hx : Ready Δ s x) (hy : Ready Δ s y) :
    Lift Δ lower (meetO lower x y) y := by
  cases lower <;> cases x <;> cases y <;> simp_all [Lift, meetO, strict, loose]
  all_goals first
    | exact Derivation.refl (hy.1 _ rfl).1 (hy.2 _ rfl)
    | exact .meetRight (hx.compatible hy)

theorem Lift.join_least {Δ lower x y z} (hx : Lift Δ lower x z)
    (hy : Lift Δ lower y z) : Lift Δ lower (joinO lower x y) z := by
  cases lower <;> cases x <;> cases y <;> cases z <;> simp_all [Lift, joinO, strict, loose]
  all_goals exact .joinLeast hx hy

theorem Lift.meet_greatest {Δ lower x y z} (hx : Lift Δ lower x y)
    (hy : Lift Δ lower x z) : Lift Δ lower x (meetO lower y z) := by
  cases lower <;> cases x <;> cases y <;> cases z <;> simp_all [Lift, meetO, strict, loose]
  all_goals exact .meetGreatest hx hy

private theorem modal_binary {Δ lower a b c d m} {op : CompareTy → CompareTy → CompareTy}
    (step : ∀ {w x y z}, Derivation Δ (.modal w m) (.modal y m) →
      Derivation Δ (.modal x m) (.modal z m) →
      (.modal (op w x) m : CompareTy).DefinedUnder Δ →
      (.modal (op y z) m : CompareTy).DefinedUnder Δ →
      Derivation Δ (.modal (op w x) m) (.modal (op y z) m))
    (ha : Lift Δ lower (a.map (CompareTy.modal · m)) (c.map (CompareTy.modal · m)))
    (hb : Lift Δ lower (b.map (CompareTy.modal · m)) (d.map (CompareTy.modal · m)))
    (hs : ∀ x, (strict op a b).map (CompareTy.modal · m) = some x → x.DefinedUnder Δ)
    (ht : ∀ x, (strict op c d).map (CompareTy.modal · m) = some x → x.DefinedUnder Δ) :
    Lift Δ lower ((strict op a b).map (CompareTy.modal · m))
      ((strict op c d).map (CompareTy.modal · m)) := by
  cases lower <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [Lift, strict]

private theorem modal_function {Δ lower a b c d m n}
    (ha : Lift Δ (!lower) c a) (hb : Lift Δ lower b d)
    (hm : Submode Δ m (.compose n .top))
    (hs : ∀ x, (strict .fn a b).map (CompareTy.modal · m) = some x → x.DefinedUnder Δ)
    (ht : ∀ x, (strict .fn c d).map (CompareTy.modal · n) = some x → x.DefinedUnder Δ) :
    Lift Δ lower ((strict .fn a b).map (CompareTy.modal · m))
      ((strict .fn c d).map (CompareTy.modal · n)) := by
  cases lower <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [Lift, strict]
  all_goals exact .fn ha hb hm hs ht

noncomputable section
attribute [local instance] Classical.propDecidable

theorem normal_fn {Δ a b c d m n}
    (ha : AlgebraSubtype Δ c a) (hb : AlgebraSubtype Δ b d)
    (hm : Submode Δ m (.compose n .top))
    (iha : ∀ lower, Lift Δ lower (normal Δ lower c) (normal Δ lower a))
    (ihb : ∀ lower, Lift Δ lower (normal Δ lower b) (normal Δ lower d))
    (lower : Bool) :
    Lift Δ lower (normal Δ lower (.modal (.fn a b) m))
      (normal Δ lower (.modal (.fn c d) n)) := by
  have hn := (Entails.defined_compose_iff.mp hm.defined.2).1
  have h₃ := (Ready.normal (AlgebraSubtype.fn ha hb hm).wellShaped_left lower).2
  have h₄ := (Ready.normal (AlgebraSubtype.fn ha hb hm).wellShaped_right lower).2
  simp only [normal, if_pos hm.defined.1, if_pos hn] at h₃ h₄ ⊢
  exact modal_function (iha (!lower)) (ihb lower) hm h₃ h₄

theorem normal_identity {Δ a} (hs : CompareTy.WellShaped Δ a) (lower : Bool) :
    Lift Δ lower (normal Δ lower (.modal a .epsilon)) (normal Δ lower a) ∧
    Lift Δ lower (normal Δ lower a) (normal Δ lower (.modal a .epsilon)) := by
  have he : Entails Δ (.defined .epsilon) := by intro η _; rfl
  simp only [normal, if_pos he]
  cases hx : normal Δ lower a with
  | none => exact ⟨trivial, trivial⟩
  | some x =>
    have hh := normal_sound hs lower hx
    exact ⟨.identity hh.2.shape.1 hh.1, .identityRev hh.2.shape.1 hh.1⟩

theorem normal_compose {Δ a} (hs : CompareTy.WellShaped Δ a) (lower : Bool) (m n : ModExpr) :
    Lift Δ lower (normal Δ lower (.modal (.modal a m) n))
      (normal Δ lower (.modal a (.compose m n))) ∧
    Lift Δ lower (normal Δ lower (.modal a (.compose m n)))
      (normal Δ lower (.modal (.modal a m) n)) := by
  by_cases hmn : Entails Δ (.defined (.compose m n))
  · obtain ⟨hm, hn⟩ := Entails.defined_compose_iff.mp hmn
    simp only [normal, if_pos hm, if_pos hn, if_pos hmn]
    cases hx : normal Δ lower a with
    | none => exact ⟨trivial, trivial⟩
    | some x =>
      have hh := normal_sound hs lower hx
      exact ⟨.compose hh.2.shape.1 hh.1 hm hn, .composeRev hh.2.shape.1 hh.1 hm hn⟩
  · by_cases hn : Entails Δ (.defined n)
    · have hm : ¬ Entails Δ (.defined m) := fun hm =>
        hmn (Entails.defined_compose_iff.mpr ⟨hm, hn⟩)
      simp [normal, hn, hm, hmn, Lift]
    · simp [normal, hn, hmn, Lift]

theorem normal_prod {Δ a b c d m}
    (ha : AlgebraSubtype Δ (.modal a m) (.modal c m))
    (hb : AlgebraSubtype Δ (.modal b m) (.modal d m))
    (iha : ∀ lower, Lift Δ lower (normal Δ lower (.modal a m)) (normal Δ lower (.modal c m)))
    (ihb : ∀ lower, Lift Δ lower (normal Δ lower (.modal b m)) (normal Δ lower (.modal d m)))
    (lower : Bool) :
    Lift Δ lower (normal Δ lower (.modal (.prod a b) m))
      (normal Δ lower (.modal (.prod c d) m)) := by
  by_cases hm : Entails Δ (.defined m)
  · have h₁ := iha lower
    have h₂ := ihb lower
    have h₃ := (Ready.normal (AlgebraSubtype.prod ha hb).wellShaped_left lower).2
    have h₄ := (Ready.normal (AlgebraSubtype.prod ha hb).wellShaped_right lower).2
    simp only [normal, if_pos hm] at h₁ h₂ h₃ h₄ ⊢
    exact modal_binary Derivation.prod h₁ h₂ h₃ h₄
  · simp [normal, hm, Lift]

theorem normal_sum {Δ a b c d m}
    (ha : AlgebraSubtype Δ (.modal a m) (.modal c m))
    (hb : AlgebraSubtype Δ (.modal b m) (.modal d m))
    (iha : ∀ lower, Lift Δ lower (normal Δ lower (.modal a m)) (normal Δ lower (.modal c m)))
    (ihb : ∀ lower, Lift Δ lower (normal Δ lower (.modal b m)) (normal Δ lower (.modal d m)))
    (lower : Bool) :
    Lift Δ lower (normal Δ lower (.modal (.sum a b) m))
      (normal Δ lower (.modal (.sum c d) m)) := by
  by_cases hm : Entails Δ (.defined m)
  · have h₁ := iha lower
    have h₂ := ihb lower
    have h₃ := (Ready.normal (AlgebraSubtype.sum ha hb).wellShaped_left lower).2
    have h₄ := (Ready.normal (AlgebraSubtype.sum ha hb).wellShaped_right lower).2
    simp only [normal, if_pos hm] at h₁ h₂ h₃ h₄ ⊢
    exact modal_binary Derivation.sum h₁ h₂ h₃ h₄
  · simp [normal, hm, Lift]

theorem normal_shaped_of_bounds {Δ a b}
    (hΔ : ∀ x y, Constraint.sub x y ∈ Δ → ∀ lower,
      Lift Δ lower (normal Δ lower (.ofTy x)) (normal Δ lower (.ofTy y)))
    (h : ShapedSubtype Δ a b) :
    ∀ lower, Lift Δ lower (normal Δ lower a) (normal Δ lower b) := by
  induction h with
  | refl hs => exact fun lower => Lift.refl lower (Ready.normal hs lower)
  | trans _ _ ih₁ ih₂ => exact fun lower => (ih₁ lower).trans (ih₂ lower)
  | bound h => exact hΔ _ _ h
  | identity hs => exact fun lower => (normal_identity hs lower).1
  | identityRev hs => exact fun lower => (normal_identity hs lower).2
  | compose hs => exact fun lower => (normal_compose hs lower _ _).1
  | composeRev hs => exact fun lower => (normal_compose hs lower _ _).2
  | congr _ hm ih =>
    intro lower
    simpa only [normal, if_pos hm.defined.1, if_pos hm.defined.2] using (ih lower).modal hm
  | prod ha hb ih₁ ih₂ => exact normal_prod (.shaped ha) (.shaped hb) ih₁ ih₂
  | sum ha hb ih₁ ih₂ => exact normal_sum (.shaped ha) (.shaped hb) ih₁ ih₂
  | fn ha hb hm ih₁ ih₂ => exact normal_fn (.shaped ha) (.shaped hb) hm ih₁ ih₂
  | joinLeft hs =>
    intro lower
    exact Lift.join_left (Ready.normal hs.1 lower)
      ((Ready.normal hs.2.1 lower).rebase hs.2.2.symm)
  | joinRight hs =>
    intro lower
    exact Lift.join_right (Ready.normal hs.1 lower)
      ((Ready.normal hs.2.1 lower).rebase hs.2.2.symm)
  | joinLeast _ _ ih₁ ih₂ => exact fun lower => (ih₁ lower).join_least (ih₂ lower)
  | meetLeft hs =>
    intro lower
    exact Lift.meet_left (Ready.normal hs.1 lower)
      ((Ready.normal hs.2.1 lower).rebase hs.2.2.symm)
  | meetRight hs =>
    intro lower
    exact Lift.meet_right (Ready.normal hs.1 lower)
      ((Ready.normal hs.2.1 lower).rebase hs.2.2.symm)
  | meetGreatest _ _ ih₁ ih₂ => exact fun lower => (ih₁ lower).meet_greatest (ih₂ lower)

theorem normal_derivation_of_bounds {Δ a b}
    (hΔ : ∀ x y, Constraint.sub x y ∈ Δ → ∀ lower,
      Lift Δ lower (normal Δ lower (.ofTy x)) (normal Δ lower (.ofTy y)))
    (h : AlgebraSubtype Δ a b) :
    ∀ lower, Lift Δ lower (normal Δ lower a) (normal Δ lower b) := by
  induction h with
  | shaped h => exact normal_shaped_of_bounds hΔ h
  | trans _ _ ih₁ ih₂ => exact fun lower => (ih₁ lower).trans (ih₂ lower)
  | equation h =>
    intro lower
    rw [normal_defined (equation_defined h).1, normal_defined (equation_defined h).2]
    exact Derivation.equation h
  | equationRev h =>
    intro lower
    rw [normal_defined (equation_defined h).1, normal_defined (equation_defined h).2]
    exact Derivation.equationRev h
  | congr _ hm ih =>
    intro lower
    simpa only [normal, if_pos hm.defined.1, if_pos hm.defined.2] using (ih lower).modal hm
  | prod ha hb ih₁ ih₂ => exact normal_prod ha hb ih₁ ih₂
  | sum ha hb ih₁ ih₂ => exact normal_sum ha hb ih₁ ih₂
  | fn ha hb hm ih₁ ih₂ => exact normal_fn ha hb hm ih₁ ih₂
  | joinLeast _ _ ih₁ ih₂ => exact fun lower => (ih₁ lower).join_least (ih₂ lower)
  | meetGreatest _ _ ih₁ ih₂ => exact fun lower => (ih₁ lower).meet_greatest (ih₂ lower)
  | clamp h₁ h₂ hm _ _ ih₁ ih₂ =>
    intro lower
    have hd := clamp_endpoints_defined h₁ h₂ hm
    have ih₁ := ih₁ lower
    have ih₂ := ih₂ lower
    rw [normal_defined hd.1, normal_defined hd.2]
    rw [normal_defined h₁.2.1, normal_defined h₁.2.2] at ih₁
    rw [normal_defined h₂.2.1, normal_defined h₂.2.2] at ih₂
    exact Derivation.clamp h₁ h₂ hm ih₁ ih₂
  | clampRev h₁ h₂ hm _ _ ih₁ ih₂ =>
    intro lower
    have hd := clamp_endpoints_defined h₁ h₂ hm
    have ih₁ := ih₁ lower
    have ih₂ := ih₂ lower
    rw [normal_defined hd.1, normal_defined hd.2]
    rw [normal_defined h₁.2.1, normal_defined h₁.2.2] at ih₁
    rw [normal_defined h₂.2.1, normal_defined h₂.2.2] at ih₂
    exact Derivation.clampRev h₁ h₂ hm ih₁ ih₂

/-- The context enters normalization only through its original subtype edges. -/
theorem normal_bound {Δ a b} (hΔ : Bounds.TypeBoundsDefined Δ)
    (h : Constraint.sub a b ∈ Δ) (lower : Bool) :
    Lift Δ lower (normal Δ lower (.ofTy a)) (normal Δ lower (.ofTy b)) := by
  simpa only [normal_defined ((CompareTy.definedUnder_ofTy _ _).mpr (hΔ _ _ h).1),
    normal_defined ((CompareTy.definedUnder_ofTy _ _).mpr (hΔ _ _ h).2), Lift] using
      Derivation.bound h ((CompareTy.definedUnder_ofTy _ _).mpr (hΔ _ _ h).1)
        ((CompareTy.definedUnder_ofTy _ _).mpr (hΔ _ _ h).2)

theorem normal_shaped {Δ a b} (hΔ : Bounds.TypeBoundsDefined Δ)
    (h : ShapedSubtype Δ a b) :
    ∀ lower, Lift Δ lower (normal Δ lower a) (normal Δ lower b) :=
  normal_shaped_of_bounds (fun _ _ => normal_bound hΔ) h

theorem normal_derivation {Δ a b} (hΔ : Bounds.TypeBoundsDefined Δ)
    (h : AlgebraSubtype Δ a b) :
    ∀ lower, Lift Δ lower (normal Δ lower a) (normal Δ lower b) :=
  normal_derivation_of_bounds (fun _ _ => normal_bound hΔ) h

theorem derivation_of_bounds {Δ a b}
    (hΔ : ∀ x y, Constraint.sub x y ∈ Δ → ∀ lower,
      Lift Δ lower (normal Δ lower (.ofTy x)) (normal Δ lower (.ofTy y)))
    (ha : CompareTy.DefinedUnder a Δ) (hb : CompareTy.DefinedUnder b Δ)
    (h : AlgebraSubtype Δ a b) : Derivation Δ a b := by
  simpa only [normal_defined ha, normal_defined hb, Lift] using
    normal_derivation_of_bounds hΔ h true

/-- Defined endpoints admit a derivation with defined terms throughout, also
inside every structural child premise. -/
theorem derivation {Δ a b} (hΔ : Bounds.TypeBoundsDefined Δ)
    (ha : CompareTy.DefinedUnder a Δ) (hb : CompareTy.DefinedUnder b Δ)
    (h : AlgebraSubtype Δ a b) : Derivation Δ a b := by
  have hh := normal_derivation hΔ h true
  simpa only [normal_defined ha, normal_defined hb, Lift] using hh

theorem derivation_iff {Δ a b} (hΔ : Bounds.TypeBoundsDefined Δ)
    (ha : CompareTy.DefinedUnder a Δ) (hb : CompareTy.DefinedUnder b Δ) :
    Derivation Δ a b ↔ AlgebraSubtype Δ a b :=
  ⟨Derivation.subtype, derivation hΔ ha hb⟩

end
end ModalityInference.ComparisonTotalDerivation
