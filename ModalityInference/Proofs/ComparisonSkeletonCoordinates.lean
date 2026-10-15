import ModalityInference.Proofs.ComparisonModalSeparation
import ModalityInference.Proofs.ComparisonBoundDefinedness

/-! Defined structural coordinate trees retain actual comparison-algebra types
at opaque leaves and symbolic, defined modality expressions at constructors.
Products and sums inherit modal actions in their children; function domains
reverse lattice variance and closure modes compare only future coordinates.
Coordinate comparisons reify to the original algebraic subtype relation. -/
namespace ModalityInference.ComparisonSkeletonCoordinates

open ComparisonAlgebra

namespace Scalar

variable {Δ : Bounds}

def le (a b : GuardedMode Δ) : Prop :=
  ∀ η, ModeModels Δ η → (a.value η).le (b.value η) = true

def futureLe (a b : GuardedMode Δ) : Prop :=
  ∀ η, ModeModels Δ η → ((a.value η).compose Mode.top).le
    ((b.value η).compose Mode.top) = true

def compose (a b : GuardedMode Δ) : GuardedMode Δ where
  expression := .compose a.expression b.expression
  value η := (a.value η).compose (b.value η)
  eval η hη := by simp [ModExpr.eval, a.eval η hη, b.eval η hη]

def blend (p : Bool) (a b : GuardedMode Δ) : GuardedMode Δ where
  expression := ComparisonAlgebra.modeOp p a.expression b.expression
  value η := ComparisonLattice.Profile.blendMode p (a.value η) (b.value η)
  eval η hη := ComparisonAlgebra.eval_modeOp (a.eval η hη) (b.eval η hη) p

def equivalent (a b : GuardedMode Δ) : Prop := le a b ∧ le b a

def futureEquivalent (a b : GuardedMode Δ) : Prop := futureLe a b ∧ futureLe b a

theorem clamp {b a t : GuardedMode Δ} (hba : le b a) (hat : le a t)
    (m : GuardedMode Δ) :
    equivalent (compose a m) (blend false (blend true a (compose b m)) (compose t m)) := by
  have h : ∀ η, ModeModels Δ η →
      (blend false (blend true a (compose b m)) (compose t m)).value η =
        (compose a m).value η := fun η hη =>
    ComparisonLattice.mode_clamp (hba η hη) (hat η hη) (m.value η)
  exact ⟨fun η hη => by rw [h η hη]; exact Mode.le_refl _,
    fun η hη => by rw [h η hη]; exact Mode.le_refl _⟩

theorem future_clamp {b a t : GuardedMode Δ} (hba : futureLe b a) (hat : futureLe a t)
    (m : GuardedMode Δ) :
    futureEquivalent (compose a m) (blend false (blend true a (compose b m)) (compose t m)) := by
  have h : ∀ η, ModeModels Δ η →
      ((blend false (blend true a (compose b m)) (compose t m)).value η).compose Mode.top =
        ((compose a m).value η).compose Mode.top := by
    intro η hη
    dsimp only [blend, compose, ComparisonLattice.Profile.blendMode]
    simp only [Bool.false_eq_true, if_false, if_true]
    have he := ComparisonLattice.mode_clamp (hba η hη) (hat η hη) (m.value η)
    simpa only [← ComparisonLattice.Profile.blendMode_compose false,
      ← ComparisonLattice.Profile.blendMode_compose true,
      ComparisonLattice.Profile.blendMode, Bool.false_eq_true, if_false, if_true,
      Mode.compose_assoc, Mode.compose_comm] using he
  exact ⟨fun η hη => by rw [h η hη]; exact Mode.le_refl _,
    fun η hη => by rw [h η hη]; exact Mode.le_refl _⟩

theorem blend_universal (p : Bool) (a b c : GuardedMode Δ) :
    if p then le (blend p a b) c ↔ le a c ∧ le b c
    else le c (blend p a b) ↔ le c a ∧ le c b := by
  cases p <;> simp [le, blend, ComparisonLattice.Profile.blendMode,
    ComparisonLattice.mode_join_le, ComparisonLattice.mode_le_meet, forall_and]

theorem future_blend_universal (p : Bool) (a b c : GuardedMode Δ) :
    if p then futureLe (blend p a b) c ↔ futureLe a c ∧ futureLe b c
    else futureLe c (blend p a b) ↔ futureLe c a ∧ futureLe c b := by
  simp only [futureLe, blend, ← ComparisonLattice.Profile.blendMode_compose]
  cases p <;> simp [ComparisonLattice.Profile.blendMode, ComparisonLattice.mode_join_le,
    ComparisonLattice.mode_le_meet, forall_and]

theorem refl (a : GuardedMode Δ) : le a a := fun _ _ => Mode.le_refl _
theorem trans {a b c : GuardedMode Δ} (h : le a b) (k : le b c) : le a c :=
  fun η hη => Mode.le_trans (h η hη) (k η hη)
theorem future_refl (a : GuardedMode Δ) : futureLe a a := fun _ _ => Mode.le_refl _
theorem future_trans {a b c : GuardedMode Δ} (h : futureLe a b) (k : futureLe b c) : futureLe a c :=
  fun η hη => Mode.le_trans (h η hη) (k η hη)

theorem submode {a b : GuardedMode Δ} (h : le a b) : Submode Δ a.expression b.expression :=
  .valid fun η hη => ⟨a.value η, b.value η, a.eval η hη, b.eval η hη, h η hη⟩

theorem future_submode {a b : GuardedMode Δ} (h : futureLe a b) :
    Submode Δ a.expression (.compose b.expression .top) := by
  apply Submode.valid
  intro η hη
  refine ⟨a.value η, (b.value η).compose Mode.top, a.eval η hη,
    by simp [ModExpr.eval, b.eval η hη, ModExpr.top], ?_⟩
  apply Mode.le_trans (b := (a.value η).compose Mode.top) _ (h η hη)
  simp [Mode.le_iff, Mode.compose, Mode.top]

def identity : GuardedMode Δ where
  expression := .epsilon
  value _ := Mode.identity
  eval _ _ := rfl

end Scalar

inductive Tree (Δ : Bounds) : ComparisonShape → Type where
  | atom {v : TypeVar} (a : Carrier Δ (.var v)) : Tree Δ (.var v)
  | unit (m : GuardedMode Δ) : Tree Δ .unit
  | credit (m : GuardedMode Δ) : Tree Δ .credit
  | prod {s t : ComparisonShape} (a : Tree Δ s) (b : Tree Δ t)
      (m : GuardedMode Δ) : Tree Δ (.prod s t)
  | sum {s t : ComparisonShape} (a : Tree Δ s) (b : Tree Δ t)
      (m : GuardedMode Δ) : Tree Δ (.sum s t)
  | fn {s t : ComparisonShape} (a : Tree Δ s) (b : Tree Δ t)
      (m : GuardedMode Δ) : Tree Δ (.fn s t)

namespace Tree

variable {Δ : Bounds}

def Le : {shape : ComparisonShape} → Tree Δ shape → Tree Δ shape → Prop
  | _, .atom a, .atom b => a ≤ b
  | _, .unit m, .unit n | _, .credit m, .credit n => Scalar.le m n
  | _, .prod a b m, .prod c d n | _, .sum a b m, .sum c d n =>
      Le a c ∧ Le b d ∧ Scalar.le m n
  | _, .fn a b m, .fn c d n => Le c a ∧ Le b d ∧ Scalar.futureLe m n

def Equivalent {shape : ComparisonShape} (a b : Tree Δ shape) : Prop := Le a b ∧ Le b a

def blend : {shape : ComparisonShape} → Bool → Tree Δ shape → Tree Δ shape → Tree Δ shape
  | _, p, .atom a, .atom b => .atom (if p then a.join b else a.meet b)
  | _, p, .unit m, .unit n => .unit (Scalar.blend p m n)
  | _, p, .credit m, .credit n => .credit (Scalar.blend p m n)
  | _, p, .prod a b m, .prod c d n => .prod (blend p a c) (blend p b d) (Scalar.blend p m n)
  | _, p, .sum a b m, .sum c d n => .sum (blend p a c) (blend p b d) (Scalar.blend p m n)
  | _, p, .fn a b m, .fn c d n => .fn (blend (!p) a c) (blend p b d) (Scalar.blend p m n)

def modal (m : GuardedMode Δ) : {shape : ComparisonShape} → Tree Δ shape → Tree Δ shape
  | _, .atom a => .atom (m.act a)
  | _, .unit n => .unit (Scalar.compose n m)
  | _, .credit n => .credit (Scalar.compose n m)
  | _, .prod a b n => .prod (modal m a) (modal m b) (Scalar.compose n m)
  | _, .sum a b n => .sum (modal m a) (modal m b) (Scalar.compose n m)
  | _, .fn a b n => .fn a b (Scalar.compose n m)

theorem Le.refl {shape : ComparisonShape} (a : Tree Δ shape) : Le a a := by
  induction a with
  | atom => exact le_refl _
  | unit a | credit a => exact Scalar.refl a
  | prod _ _ m ih₁ ih₂ | sum _ _ m ih₁ ih₂ => exact ⟨ih₁, ih₂, Scalar.refl m⟩
  | fn _ _ m ih₁ ih₂ => exact ⟨ih₁, ih₂, Scalar.future_refl m⟩

theorem Le.trans {shape : ComparisonShape} {a b c : Tree Δ shape}
    (hab : Le a b) (hbc : Le b c) : Le a c := by
  induction shape with
  | var => cases a; cases b; cases c; exact le_trans hab hbc
  | unit => cases a; cases b; cases c; exact Scalar.trans hab hbc
  | credit => cases a; cases b; cases c; exact Scalar.trans hab hbc
  | prod _ _ ih₁ ih₂ | sum _ _ ih₁ ih₂ =>
    cases a; cases b; cases c
    exact ⟨ih₁ hab.1 hbc.1, ih₂ hab.2.1 hbc.2.1, Scalar.trans hab.2.2 hbc.2.2⟩
  | fn _ _ ih₁ ih₂ =>
    cases a; cases b; cases c
    exact ⟨ih₁ hbc.1 hab.1, ih₂ hab.2.1 hbc.2.1, Scalar.future_trans hab.2.2 hbc.2.2⟩

theorem blend_universal {shape : ComparisonShape} (p : Bool) (a b c : Tree Δ shape) :
    if p then Le (blend p a b) c ↔ Le a c ∧ Le b c
    else Le c (blend p a b) ↔ Le c a ∧ Le c b := by
  induction a generalizing p with
  | atom a =>
    cases b with | atom b =>
      cases c with | atom c =>
        cases p
        · exact ⟨fun h => ⟨h.trans (Carrier.meet_le_left _ _), h.trans (Carrier.meet_le_right _ _)⟩,
            fun h => Carrier.le_meet h.1 h.2⟩
        · exact ⟨fun h => ⟨(Carrier.le_join_left _ _).trans h, (Carrier.le_join_right _ _).trans h⟩,
            fun h => Carrier.join_le h.1 h.2⟩
  | unit a => cases b; cases c; exact Scalar.blend_universal p _ _ _
  | credit a => cases b; cases c; exact Scalar.blend_universal p _ _ _
  | prod a₁ a₂ am ih₁ ih₂ =>
    cases b with | prod b₁ b₂ bm =>
      cases c with | prod c₁ c₂ cm =>
        have h₁ := ih₁ p b₁ c₁
        have h₂ := ih₂ p b₂ c₂
        have hm := Scalar.blend_universal p am bm cm
        cases p <;> simp_all only [blend, Le, Bool.false_eq_true, if_false, if_true,
          and_assoc, and_left_comm, and_comm]
  | sum a₁ a₂ am ih₁ ih₂ =>
    cases b with | sum b₁ b₂ bm =>
      cases c with | sum c₁ c₂ cm =>
        have h₁ := ih₁ p b₁ c₁
        have h₂ := ih₂ p b₂ c₂
        have hm := Scalar.blend_universal p am bm cm
        cases p <;> simp_all only [blend, Le, Bool.false_eq_true, if_false, if_true,
          and_assoc, and_left_comm, and_comm]
  | fn a₁ a₂ am ih₁ ih₂ =>
    cases b with | fn b₁ b₂ bm =>
      cases c with | fn c₁ c₂ cm =>
        have h₁ := ih₁ (!p) b₁ c₁
        have h₂ := ih₂ p b₂ c₂
        have hm := Scalar.future_blend_universal p am bm cm
        cases p <;> simp_all only [blend, Le, Bool.false_eq_true, if_false, if_true,
          Bool.not_false, Bool.not_true, and_assoc, and_left_comm, and_comm]

theorem sandwich {shape : ComparisonShape} (p : Bool) (a b t : Tree Δ shape)
    (h : if p then Le b a ∧ Le a t else Le t a ∧ Le a b) :
    Equivalent (blend (!p) (blend p a b) t) a := by
  cases p
  · have hm := (blend_universal false a b (blend false a b)).mp (Le.refl _)
    have hj := (blend_universal true (blend false a b) t (blend true (blend false a b) t)).mp (Le.refl _)
    exact ⟨(blend_universal true (blend false a b) t a).mpr ⟨hm.1, h.1⟩,
      ((blend_universal false a b a).mpr ⟨Le.refl a, h.2⟩).trans hj.1⟩
  · have hj := (blend_universal true a b (blend true a b)).mp (Le.refl _)
    have hm := (blend_universal false (blend true a b) t (blend false (blend true a b) t)).mp (Le.refl _)
    exact ⟨hm.1.trans ((blend_universal true a b a).mpr ⟨Le.refl a, h.1⟩),
      (blend_universal false (blend true a b) t a).mpr ⟨hj.1, h.2⟩⟩

/-- Clamping holds at every structural depth, including the contravariant
function domain and the inherited actions of products and sums. -/
theorem clamp {shape : ComparisonShape} {b a t : Tree Δ shape}
    (hba : Le b a) (hat : Le a t) (m : GuardedMode Δ) :
    Equivalent (modal m a) (blend false (blend true a (modal m b)) (modal m t)) := by
  induction a with
  | atom a =>
    cases b with | atom b =>
      cases t with | atom t =>
        exact ⟨AlgebraSubtype.clamp (b.compatible a) (a.compatible t) m.defined hba hat,
          AlgebraSubtype.clampRev (b.compatible a) (a.compatible t) m.defined hba hat⟩
  | unit a =>
    cases b with | unit b =>
      cases t with | unit t => exact Scalar.clamp hba hat m
  | credit a =>
    cases b with | credit b =>
      cases t with | credit t => exact Scalar.clamp hba hat m
  | prod a₁ a₂ am ih₁ ih₂ =>
    cases b with | prod b₁ b₂ bm =>
      cases t with | prod t₁ t₂ tm =>
        have h₁ := ih₁ hba.1 hat.1
        have h₂ := ih₂ hba.2.1 hat.2.1
        have hm := Scalar.clamp hba.2.2 hat.2.2 m
        exact ⟨⟨h₁.1, h₂.1, hm.1⟩, h₁.2, h₂.2, hm.2⟩
  | sum a₁ a₂ am ih₁ ih₂ =>
    cases b with | sum b₁ b₂ bm =>
      cases t with | sum t₁ t₂ tm =>
        have h₁ := ih₁ hba.1 hat.1
        have h₂ := ih₂ hba.2.1 hat.2.1
        have hm := Scalar.clamp hba.2.2 hat.2.2 m
        exact ⟨⟨h₁.1, h₂.1, hm.1⟩, h₁.2, h₂.2, hm.2⟩
  | fn a₁ a₂ am _ _ =>
    cases b with | fn b₁ b₂ bm =>
      cases t with | fn t₁ t₂ tm =>
        have h₁ := sandwich false a₁ b₁ t₁ ⟨hat.1, hba.1⟩
        have h₂ := sandwich true a₂ b₂ t₂ ⟨hba.2.1, hat.2.1⟩
        have hm := Scalar.future_clamp hba.2.2 hat.2.2 m
        exact ⟨⟨h₁.1, h₂.2, hm.1⟩, h₁.2, h₂.1, hm.2⟩

def reify : {shape : ComparisonShape} → Tree Δ shape → CompareTy
  | _, .atom a => a.type
  | _, .unit m => .modal .unit m.expression
  | _, .credit m => .modal .credit m.expression
  | _, .prod a b m => .modal (.prod (reify a) (reify b)) m.expression
  | _, .sum a b m => .modal (.sum (reify a) (reify b)) m.expression
  | _, .fn a b m => .modal (.fn (reify a) (reify b)) m.expression

theorem reify_shaped {shape : ComparisonShape} (a : Tree Δ shape) : (reify a).WellShaped Δ := by
  induction a with
  | atom a => exact a.shaped
  | unit | credit => trivial
  | prod _ _ _ ih₁ ih₂ | sum _ _ _ ih₁ ih₂ | fn _ _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩

theorem reify_defined {shape : ComparisonShape} (a : Tree Δ shape) : (reify a).DefinedUnder Δ := by
  induction a with
  | atom a => exact a.defined
  | unit m | credit m =>
    refine CompareTy.definedUnder_modal_iff.mpr ⟨?_, m.defined⟩
    intro η hη c hc
    cases hc
  | prod _ _ m ih₁ ih₂ =>
    exact CompareTy.definedUnder_modal_iff.mpr ⟨CompareTy.definedUnder_prod_iff.mpr ⟨ih₁, ih₂⟩, m.defined⟩
  | sum _ _ m ih₁ ih₂ =>
    exact CompareTy.definedUnder_modal_iff.mpr ⟨CompareTy.definedUnder_sum_iff.mpr ⟨ih₁, ih₂⟩, m.defined⟩
  | fn _ _ m ih₁ ih₂ =>
    exact CompareTy.definedUnder_modal_iff.mpr ⟨CompareTy.definedUnder_fn_iff.mpr ⟨ih₁, ih₂⟩, m.defined⟩

theorem reify_shape {shape : ComparisonShape} (a : Tree Δ shape) :
    ComparisonShape.Equivalent Δ (reify a).shape shape := by
  induction a with
  | atom a => exact a.shape_eq
  | unit | credit => exact ComparisonShape.Equivalent.refl
  | prod a b m ih₁ ih₂ | sum a b m ih₁ ih₂ | fn a b m ih₁ ih₂ =>
    intro ρ hρ
    simp only [reify, CompareTy.shape, ComparisonShape.subst, ih₁ ρ hρ, ih₂ ρ hρ]

/-- Coordinate order is sound for the original algebraic subtype relation. -/
theorem reify_le {shape : ComparisonShape} {a b : Tree Δ shape} (h : Le a b) :
    AlgebraSubtype Δ (reify a) (reify b) := by
  induction shape with
  | var => cases a; cases b; exact h
  | unit => cases a; cases b; exact .congr (.refl trivial) (Scalar.submode h)
  | credit => cases a; cases b; exact .congr (.refl trivial) (Scalar.submode h)
  | prod s t ih₁ ih₂ =>
    cases a with | prod a₁ a₂ am =>
      cases b with | prod b₁ b₂ bm =>
        exact (AlgebraSubtype.prod
          (.congr (ih₁ h.1) (Scalar.submode (Scalar.refl am)))
          (.congr (ih₂ h.2.1) (Scalar.submode (Scalar.refl am)))).trans
            (.congr (.refl ⟨reify_shaped b₁, reify_shaped b₂⟩) (Scalar.submode h.2.2))
  | sum s t ih₁ ih₂ =>
    cases a with | sum a₁ a₂ am =>
      cases b with | sum b₁ b₂ bm =>
        exact (AlgebraSubtype.sum
          (.congr (ih₁ h.1) (Scalar.submode (Scalar.refl am)))
          (.congr (ih₂ h.2.1) (Scalar.submode (Scalar.refl am)))).trans
            (.congr (.refl ⟨reify_shaped b₁, reify_shaped b₂⟩) (Scalar.submode h.2.2))
  | fn s t ih₁ ih₂ =>
    cases a; cases b
    exact AlgebraSubtype.fn (ih₁ h.1) (ih₂ h.2.1) (Scalar.future_submode h.2.2)

private theorem acted_absorb {a : CompareTy} (ha : a.WellShaped Δ)
    (m n : GuardedMode Δ) :
    AlgebraSubtype Δ (.modal (.modal a m.expression) (Scalar.compose n m).expression)
        (.modal a (Scalar.compose n m).expression) ∧
      AlgebraSubtype Δ (.modal a (Scalar.compose n m).expression)
        (.modal (.modal a m.expression) (Scalar.compose n m).expression) := by
  have he : Scalar.equivalent (Scalar.compose m (Scalar.compose n m)) (Scalar.compose n m) :=
    ⟨fun η _ => by simp only [Scalar.compose, Mode.compose_absorb_right]; exact Mode.le_refl _,
     fun η _ => by simp only [Scalar.compose, Mode.compose_absorb_right]; exact Mode.le_refl _⟩
  exact ⟨(AlgebraSubtype.shaped (.compose ha)).trans (.congr (.refl ha) (Scalar.submode he.1)),
    (AlgebraSubtype.congr (.refl ha) (Scalar.submode he.2)).trans (.shaped (.composeRev ha))⟩

theorem reify_modal {shape : ComparisonShape} (a : Tree Δ shape) (m : GuardedMode Δ) :
    AlgebraSubtype Δ (reify (modal m a)) (.modal (reify a) m.expression) ∧
      AlgebraSubtype Δ (.modal (reify a) m.expression) (reify (modal m a)) := by
  induction a with
  | atom a => exact ⟨.refl a.shaped, .refl a.shaped⟩
  | unit a | credit a => exact ⟨.shaped (.composeRev trivial), .shaped (.compose trivial)⟩
  | fn a b n _ _ =>
    exact ⟨.shaped (.composeRev ⟨reify_shaped a, reify_shaped b⟩),
      .shaped (.compose ⟨reify_shaped a, reify_shaped b⟩)⟩
  | prod a b n ih₁ ih₂ =>
    have ha := acted_absorb (reify_shaped a) m n
    have hb := acted_absorb (reify_shaped b) m n
    have hk := Scalar.submode (Scalar.refl (Scalar.compose n m))
    exact ⟨(AlgebraSubtype.prod
      ((AlgebraSubtype.congr ih₁.1 hk).trans ha.1)
      ((AlgebraSubtype.congr ih₂.1 hk).trans hb.1)).trans
        (.shaped (.composeRev ⟨reify_shaped a, reify_shaped b⟩)),
      (AlgebraSubtype.shaped (.compose (a := .prod (reify a) (reify b))
        ⟨reify_shaped a, reify_shaped b⟩)).trans
        (.prod (ha.2.trans (.congr ih₁.2 hk)) (hb.2.trans (.congr ih₂.2 hk)))⟩
  | sum a b n ih₁ ih₂ =>
    have ha := acted_absorb (reify_shaped a) m n
    have hb := acted_absorb (reify_shaped b) m n
    have hk := Scalar.submode (Scalar.refl (Scalar.compose n m))
    exact ⟨(AlgebraSubtype.sum
      ((AlgebraSubtype.congr ih₁.1 hk).trans ha.1)
      ((AlgebraSubtype.congr ih₂.1 hk).trans hb.1)).trans
        (.shaped (.composeRev ⟨reify_shaped a, reify_shaped b⟩)),
      (AlgebraSubtype.shaped (.compose (a := .sum (reify a) (reify b))
        ⟨reify_shaped a, reify_shaped b⟩)).trans
        (.sum (ha.2.trans (.congr ih₁.2 hk)) (hb.2.trans (.congr ih₂.2 hk)))⟩

theorem reify_clamp {shape : ComparisonShape} {b a t : Tree Δ shape}
    (hba : Le b a) (hat : Le a t) (m : GuardedMode Δ) :
    AlgebraSubtype Δ (reify (modal m a))
        (reify (blend false (blend true a (modal m b)) (modal m t))) ∧
      AlgebraSubtype Δ (reify (blend false (blend true a (modal m b)) (modal m t)))
        (reify (modal m a)) :=
  ⟨reify_le (clamp hba hat m).1, reify_le (clamp hba hat m).2⟩

def ofPublic : (a : Ty) → (CompareTy.ofTy a).DefinedUnder Δ → Tree Δ (ComparisonShape.ofTy a)
  | .var v, _ => .atom {
      type := .var v
      shaped := trivial
      defined := by intro η hη c hc; cases hc
      shape_eq := ComparisonShape.Equivalent.refl }
  | .unit, _ => .unit Scalar.identity
  | .credit, _ => .credit Scalar.identity
  | .prod a b, h => .prod
      (ofPublic a (CompareTy.definedUnder_prod_iff.mp h).1)
      (ofPublic b (CompareTy.definedUnder_prod_iff.mp h).2) Scalar.identity
  | .sum a b, h => .sum
      (ofPublic a (CompareTy.definedUnder_sum_iff.mp h).1)
      (ofPublic b (CompareTy.definedUnder_sum_iff.mp h).2) Scalar.identity
  | .fn a b, h => .fn
      (ofPublic a (CompareTy.definedUnder_fn_iff.mp h).1)
      (ofPublic b (CompareTy.definedUnder_fn_iff.mp h).2) Scalar.identity
  | .modal a m, h => modal (GuardedMode.ofDefined m (CompareTy.definedUnder_modal_iff.mp h).2)
      (ofPublic a (CompareTy.definedUnder_modal_iff.mp h).1)

/-- Reification fixes every defined public type up to algebraic equivalence. -/
theorem ofPublic_correct (a : Ty) (ha : (CompareTy.ofTy a).DefinedUnder Δ) :
    AlgebraSubtype Δ (reify (ofPublic a ha)) (CompareTy.ofTy a) ∧
      AlgebraSubtype Δ (CompareTy.ofTy a) (reify (ofPublic a ha)) := by
  induction a with
  | var v => exact ⟨.refl trivial, .refl trivial⟩
  | unit | credit => exact ⟨.shaped (.identity trivial), .shaped (.identityRev trivial)⟩
  | prod a b ih₁ ih₂ =>
    have h₁ := ih₁ (CompareTy.definedUnder_prod_iff.mp ha).1
    have h₂ := ih₂ (CompareTy.definedUnder_prod_iff.mp ha).2
    have he := Scalar.submode (Scalar.refl (Scalar.identity (Δ := Δ)))
    exact ⟨(AlgebraSubtype.prod (.congr h₁.1 he) (.congr h₂.1 he)).trans
      (.shaped (.identity (CompareTy.wellShaped_ofTy (.prod a b) Δ))),
      (AlgebraSubtype.shaped (.identityRev (CompareTy.wellShaped_ofTy (.prod a b) Δ))).trans
        (.prod (.congr h₁.2 he) (.congr h₂.2 he))⟩
  | sum a b ih₁ ih₂ =>
    have h₁ := ih₁ (CompareTy.definedUnder_sum_iff.mp ha).1
    have h₂ := ih₂ (CompareTy.definedUnder_sum_iff.mp ha).2
    have he := Scalar.submode (Scalar.refl (Scalar.identity (Δ := Δ)))
    exact ⟨(AlgebraSubtype.sum (.congr h₁.1 he) (.congr h₂.1 he)).trans
      (.shaped (.identity (CompareTy.wellShaped_ofTy (.sum a b) Δ))),
      (AlgebraSubtype.shaped (.identityRev (CompareTy.wellShaped_ofTy (.sum a b) Δ))).trans
        (.sum (.congr h₁.2 he) (.congr h₂.2 he))⟩
  | fn a b ih₁ ih₂ =>
    have h₁ := ih₁ (CompareTy.definedUnder_fn_iff.mp ha).1
    have h₂ := ih₂ (CompareTy.definedUnder_fn_iff.mp ha).2
    have he := Scalar.future_submode (Scalar.future_refl (Scalar.identity (Δ := Δ)))
    exact ⟨(AlgebraSubtype.fn h₁.2 h₂.1 he).trans
      (.shaped (.identity (CompareTy.wellShaped_ofTy (.fn a b) Δ))),
      (AlgebraSubtype.shaped (.identityRev (CompareTy.wellShaped_ofTy (.fn a b) Δ))).trans
        (.fn h₁.1 h₂.2 he)⟩
  | modal a m ih =>
    have h := ih (CompareTy.definedUnder_modal_iff.mp ha).1
    let mode := GuardedMode.ofDefined m (CompareTy.definedUnder_modal_iff.mp ha).2
    have hc := reify_modal (ofPublic a (CompareTy.definedUnder_modal_iff.mp ha).1) mode
    have hm := Scalar.submode (Scalar.refl mode)
    exact ⟨hc.1.trans (.congr h.1 hm), (AlgebraSubtype.congr h.2 hm).trans hc.2⟩

end Tree

end ModalityInference.ComparisonSkeletonCoordinates
