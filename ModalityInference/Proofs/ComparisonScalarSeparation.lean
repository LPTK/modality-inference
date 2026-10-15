import ModalityInference.Proofs.ComparisonControlSeparation

/-! Finite observations in one modal band extend to a genuine mode model of
the declared assumptions. Scalar entailment and Boolean complementation make
this an instance of finite Boolean algebra separation. -/
namespace ModalityInference.ComparisonAlgebra

open ComparisonControls

def channelMode : Channel → Bool → Mode
  | .lower, b => ⟨true, true, !b⟩
  | .locality, b => ⟨b, true, true⟩
  | .affinity, b => ⟨true, b, true⟩

theorem channelMode_meet (c : Channel) (a b : Bool) :
    (channelMode c a).meet (channelMode c b) = channelMode c (a && b) := by
  cases c <;> cases a <;> cases b <;> rfl

theorem channelMode_join (c : Channel) (a b : Bool) :
    (channelMode c a).join (channelMode c b) = channelMode c (a || b) := by
  cases c <;> cases a <;> cases b <;> rfl

theorem channelMode_le (c : Channel) {a b : Bool} (h : a ≤ b) :
    (channelMode c a).le (channelMode c b) = true := by
  cases c <;> cases a <;> cases b <;> simp_all [channelMode, Mode.le, Bool.le_iff_imp]

structure BandScalar (Δ : Bounds) (c : Channel) where
  expression : ModExpr
  truth : (ModVar → Mode) → Bool
  eval : ∀ η, ModeModels Δ η →
    expression.eval (some ∘ η) = some (channelMode c (truth η))

namespace BandScalar

variable {Δ : Bounds} {c : Channel}

def const (b : Bool) : BandScalar Δ c where
  expression := .const (channelMode c b)
  truth := fun _ => b
  eval _ _ := rfl

def meet (a b : BandScalar Δ c) : BandScalar Δ c where
  expression := .meet a.expression b.expression
  truth := fun η => a.truth η && b.truth η
  eval η hη := by simp [ModExpr.eval, a.eval η hη, b.eval η hη, channelMode_meet]

def join (a b : BandScalar Δ c) : BandScalar Δ c where
  expression := .join a.expression b.expression
  truth := fun η => a.truth η || b.truth η
  eval η hη := by simp [ModExpr.eval, a.eval η hη, b.eval η hη, channelMode_join]

def neg (a : BandScalar Δ c) : BandScalar Δ c where
  expression := match c with
    | .lower => .leftResidual (.const (channelMode c true)) a.expression
    | _ => .rightResidual a.expression (.const (channelMode c false))
  truth := fun η => !(a.truth η)
  eval η hη := by
    cases c <;> simp only [ModExpr.eval, a.eval η hη] <;>
      cases a.truth η <;> rfl

def control (q : Control) : BandScalar Δ q.channel where
  expression := q.expression
  truth := fun η => encodeModes η q.atom == q.positive
  eval η _ := by
    rw [control_eval]
    cases q <;> rfl

theorem defined (a : BandScalar Δ c) : DefinedMode Δ a.expression := by
  intro η hη
  simp [ModExpr.WellFormed, a.eval η hη]

def act (p : BandScalar Δ c) (a : Carrier Δ shape) : Carrier Δ shape :=
  a.modal p.expression p.defined

theorem act_le {p q : BandScalar Δ c} (a : Carrier Δ shape)
    (h : ∀ η, ModeModels Δ η → p.truth η ≤ q.truth η) : p.act a ≤ q.act a :=
  Carrier.modal_le (le_refl a) (.valid fun η hη =>
    ⟨_, _, p.eval η hη, q.eval η hη, channelMode_le c (h η hη)⟩)

theorem act_meet (p q : BandScalar Δ c) (a : Carrier Δ shape) :
    Order.of ((p.meet q).act a) = Order.of (p.act a) ⊓ Order.of (q.act a) :=
  Quotient.sound ⟨.equation (.scalar false a.shaped a.defined p.defined q.defined),
    .equationRev (.scalar false a.shaped a.defined p.defined q.defined)⟩

theorem act_join (p q : BandScalar Δ c) (a : Carrier Δ shape) :
    Order.of ((p.join q).act a) = Order.of (p.act a) ⊔ Order.of (q.act a) :=
  Quotient.sound ⟨.equation (.scalar true a.shaped a.defined p.defined q.defined),
    .equationRev (.scalar true a.shaped a.defined p.defined q.defined)⟩

theorem act_eq {p q : BandScalar Δ c} (a : Carrier Δ shape)
    (h : ∀ η, ModeModels Δ η → p.truth η = q.truth η) :
    Order.of (p.act a) = Order.of (q.act a) :=
  Quotient.sound ⟨act_le a fun η hη => le_of_eq (h η hη),
    act_le a fun η hη => le_of_eq (h η hη).symm⟩

def observe (f : LatticeHom (Order Δ shape) Bool) (a : Carrier Δ shape)
    (p : BandScalar Δ c) : Bool := observer f (p.act a)

theorem observe_meet (f : LatticeHom (Order Δ shape) Bool) (a : Carrier Δ shape)
    (p q : BandScalar Δ c) :
    observe f a (p.meet q) = (observe f a p && observe f a q) :=
  (congrArg f (act_meet p q a)).trans (f.map_inf' _ _)

theorem observe_join (f : LatticeHom (Order Δ shape) Bool) (a : Carrier Δ shape)
    (p q : BandScalar Δ c) :
    observe f a (p.join q) = (observe f a p || observe f a q) :=
  (congrArg f (act_join p q a)).trans (f.map_sup' _ _)

theorem observe_neg (f : LatticeHom (Order Δ shape) Bool) (a : Carrier Δ shape)
    (hl : observe f a (const (c := c) false) = false)
    (hu : observe f a (const (c := c) true) = true) (p : BandScalar Δ c) :
    observe f a p.neg = !observe f a p := by
  have hm : (observe f a p && observe f a p.neg) = false := by
    rw [← observe_meet]
    exact (congrArg f (act_eq a (p := p.meet p.neg) (q := const false)
      fun η _ => by change (p.truth η && !p.truth η) = false; cases p.truth η <;> rfl)).trans hl
  have hj : (observe f a p || observe f a p.neg) = true := by
    rw [← observe_join]
    exact (congrArg f (act_eq a (p := p.join p.neg) (q := const true)
      fun η _ => by change (p.truth η || !p.truth η) = true; cases p.truth η <;> rfl)).trans hu
  cases hp : observe f a p <;> cases hn : observe f a p.neg <;> simp_all

def agreement (value : BandScalar Δ c → Bool) : List (BandScalar Δ c) → BandScalar Δ c
  | [] => const true
  | p :: ps => (if value p then p else p.neg).meet (agreement value ps)

@[simp] theorem const_truth (b : Bool) (η) : (const (Δ := Δ) (c := c) b).truth η = b := rfl
@[simp] theorem meet_truth (p q : BandScalar Δ c) (η) :
    (p.meet q).truth η = (p.truth η && q.truth η) := rfl
@[simp] theorem neg_truth (p : BandScalar Δ c) (η) : p.neg.truth η = !p.truth η := rfl

theorem agreement_truth (value : BandScalar Δ c → Bool) (ps : List (BandScalar Δ c))
    (η : ModVar → Mode) :
    (agreement value ps).truth η = true ↔ ∀ p ∈ ps, p.truth η = value p := by
  induction ps with
  | nil => simp [agreement]
  | cons p ps ih =>
    cases hp : value p <;> cases he : p.truth η <;>
      simp [agreement, hp, he, ih]

theorem observe_agreement (f : LatticeHom (Order Δ shape) Bool) (a : Carrier Δ shape)
    (hl : observe f a (const (c := c) false) = false)
    (hu : observe f a (const (c := c) true) = true) (ps : List (BandScalar Δ c)) :
    observe f a (agreement (observe f a) ps) = true := by
  induction ps with
  | nil => exact hu
  | cons p ps ih =>
    cases hp : observe f a p <;>
      simp [agreement, hp, observe_meet, observe_neg f a hl hu, ih]

/-- Every finite collection of observations in a nontrivial scalar band is
realized by one mode assignment satisfying all declared assumptions. -/
theorem observations_realizable (f : LatticeHom (Order Δ shape) Bool)
    (a : Carrier Δ shape)
    (hl : observe f a (const (c := c) false) = false)
    (hu : observe f a (const (c := c) true) = true) (ps : List (BandScalar Δ c)) :
    ∃ η, ModeModels Δ η ∧ ∀ p ∈ ps, p.truth η = observe f a p := by
  by_contra hn
  have he (η) (hη : ModeModels Δ η) :
      (agreement (observe f a) ps).truth η = false := by
    apply Bool.eq_false_iff.mpr
    exact fun h => hn ⟨η, hη, (agreement_truth _ _ _).mp h⟩
  have ho := congrArg f (act_eq a (p := agreement (observe f a) ps) (q := const false) he)
  exact Bool.noConfusion ((observe_agreement f a hl hu ps).symm.trans (ho.trans hl))

end BandScalar

end ModalityInference.ComparisonAlgebra
