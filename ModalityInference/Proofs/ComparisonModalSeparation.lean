import ModalityInference.Proofs.ComparisonScalarSeparation

/-! Boolean observations of a finite set of defined modal actions are captured
by one of the four coordinate actions and, for active coordinates, one model
of the declared modality constraints. -/
namespace ModalityInference.ComparisonAlgebra

open ComparisonControls

structure GuardedMode (Δ : Bounds) where
  expression : ModExpr
  value : (ModVar → Mode) → Mode
  eval : ∀ η, ModeModels Δ η → expression.eval (some ∘ η) = some (value η)

namespace GuardedMode

def ofDefined (m : ModExpr) (hm : DefinedMode Δ m) : GuardedMode Δ where
  expression := m
  value η := (m.eval (some ∘ η)).getD Mode.identity
  eval η hη := by
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hm η hη)
    simp [hn]

theorem defined (m : GuardedMode Δ) : DefinedMode Δ m.expression := by
  intro η hη
  simp [ModExpr.WellFormed, m.eval η hη]

def act (m : GuardedMode Δ) (a : Carrier Δ shape) : Carrier Δ shape :=
  a.modal m.expression m.defined

def meet (m n : GuardedMode Δ) : GuardedMode Δ where
  expression := .meet m.expression n.expression
  value η := (m.value η).meet (n.value η)
  eval η hη := by simp [ModExpr.eval, m.eval η hη, n.eval η hη]

theorem act_meet (m n : GuardedMode Δ) (a : Carrier Δ shape) :
    Order.of ((m.meet n).act a) = Order.of (m.act a) ⊓ Order.of (n.act a) :=
  Quotient.sound ⟨.equation (.scalar false a.shaped a.defined m.defined n.defined),
    .equationRev (.scalar false a.shaped a.defined m.defined n.defined)⟩

def bandValue : Channel → Mode → Bool
  | .lower, m => !m.unique
  | .locality, m => m.isLocal
  | .affinity, m => m.once

def band (m : GuardedMode Δ) (c : Channel) : BandScalar Δ c where
  expression := match c with
    | .lower => .join m.expression .epsilon
    | .locality => .join (.future m.expression) (.const Mode.global)
    | .affinity => .join (.future m.expression) (.const Mode.many)
  truth η := bandValue c (m.value η)
  eval η hη := by
    cases c <;> simp [ModExpr.eval, m.eval η hη, channelMode, bandValue,
      Mode.join, Mode.future, Mode.global, Mode.many, ModExpr.epsilon, Mode.identity]

end GuardedMode

def BandScalar.guarded (p : BandScalar Δ c) : GuardedMode Δ :=
  ⟨p.expression, fun η => channelMode c (p.truth η), p.eval⟩

namespace Carrier

theorem after_const_eq (a : Carrier Δ shape) (k : Mode) (m n : GuardedMode Δ)
    (h : ∀ η, ModeModels Δ η → k.compose (m.value η) = k.compose (n.value η)) :
    Order.of (m.act (a.atMode k)) = Order.of (n.act (a.atMode k)) := by
  have hmn : Submode Δ (.compose (.const k) m.expression) (.compose (.const k) n.expression) :=
    .valid fun η hη => ⟨k.compose (m.value η), k.compose (n.value η),
      by simp [ModExpr.eval, m.eval η hη],
      by simp [ModExpr.eval, n.eval η hη], by rw [h η hη]; exact Mode.le_refl _⟩
  have hnm : Submode Δ (.compose (.const k) n.expression) (.compose (.const k) m.expression) :=
    .valid fun η hη => ⟨k.compose (n.value η), k.compose (m.value η),
      by simp [ModExpr.eval, n.eval η hη],
      by simp [ModExpr.eval, m.eval η hη], by rw [h η hη]; exact Mode.le_refl _⟩
  exact Quotient.sound
    ⟨(AlgebraSubtype.shaped (.compose a.shaped)).trans
        ((AlgebraSubtype.congr (.refl a.shaped) hmn).trans (.shaped (.composeRev a.shaped))),
      (AlgebraSubtype.shaped (.compose a.shaped)).trans
        ((AlgebraSubtype.congr (.refl a.shaped) hnm).trans (.shaped (.composeRev a.shaped)))⟩

end Carrier

theorem modal_bottom (a : Carrier Δ shape) (m : GuardedMode Δ) :
    Order.of (m.act (a.atMode Mode.bottom)) =
      Order.of ((m.band .lower).act (a.atMode Mode.bottom)) :=
  Carrier.after_const_eq a Mode.bottom m (m.band .lower).guarded fun η _ => by
    simp [GuardedMode.band, BandScalar.guarded, channelMode, GuardedMode.bandValue,
      Mode.compose, Mode.bottom]

theorem modal_top (a : Carrier Δ shape) (m : GuardedMode Δ) :
    Order.of (m.act (a.atMode Mode.top)) =
      Order.of ((m.band .locality).act (a.atMode Mode.top)) ⊓
        Order.of ((m.band .affinity).act (a.atMode Mode.top)) := by
  refine (Carrier.after_const_eq a Mode.top m
    ((m.band .locality).guarded.meet (m.band .affinity).guarded) ?_).trans
      (GuardedMode.act_meet _ _ _)
  intro η _
  simp [GuardedMode.band, GuardedMode.meet, BandScalar.guarded, channelMode,
    GuardedMode.bandValue, Mode.compose, Mode.top, Mode.meet]

namespace BandScalar

theorem observe_false_of_upper (f : LatticeHom (Order Δ shape) Bool)
    (a : Carrier Δ shape) (hu : observe f a (const (c := c) true) = false)
    (p : BandScalar Δ c) : observe f a p = false := by
  apply Bool.eq_false_iff.mpr
  intro hp
  have hh := observer_mono f (p.act_le a (q := const true) fun η _ =>
    by simp [Bool.le_iff_imp]) hp
  simp [show observe f a (const (c := c) true) = true from hh] at hu

theorem observe_true_of_lower (f : LatticeHom (Order Δ shape) Bool)
    (a : Carrier Δ shape) (hl : observe f a (const (c := c) false) = true)
    (p : BandScalar Δ c) : observe f a p = true :=
  observer_mono f (act_le a (p := const false) (q := p) fun η _ =>
    by simp [Bool.le_iff_imp]) hl

@[simp] theorem observe_const_lower (f : LatticeHom (Order Δ shape) Bool)
    (a : Carrier Δ shape) (b : Bool) :
    observe f a (const (c := .lower) b) =
      if b then observer f (a.atMode Mode.top) else observer f a := by
  cases b
  · exact congrArg f (Carrier.atMode_identity a)
  · rfl

@[simp] theorem observe_const_locality (f : LatticeHom (Order Δ shape) Bool)
    (a : Carrier Δ shape) (b : Bool) :
    observe f a (const (c := .locality) b) =
      if b then observer f a else observer f (a.atMode Mode.global) := by
  cases b
  · rfl
  · exact congrArg f (Carrier.atMode_identity a)

@[simp] theorem observe_const_affinity (f : LatticeHom (Order Δ shape) Bool)
    (a : Carrier Δ shape) (b : Bool) :
    observe f a (const (c := .affinity) b) =
      if b then observer f a else observer f (a.atMode Mode.many) := by
  cases b
  · rfl
  · exact congrArg f (Carrier.atMode_identity a)

end BandScalar

theorem observer_modal_interval (f : LatticeHom (Order Δ shape) Bool)
    (a b x : Carrier Δ shape) (hxlo : a.atMode Mode.bottom ≤ x)
    (hxhi : x ≤ b.atMode Mode.top) (m : GuardedMode Δ) :
    observer f (m.act x) =
      ((observer f x || BandScalar.observe f (a.atMode Mode.bottom) (m.band .lower)) &&
        (BandScalar.observe f (b.atMode Mode.top) (m.band .locality) &&
          BandScalar.observe f (b.atMode Mode.top) (m.band .affinity))) := by
  have he : Order.of (m.act x) =
      (Order.of x ⊔ Order.of (m.act (a.atMode Mode.bottom))) ⊓
        Order.of (m.act (b.atMode Mode.top)) :=
    Quotient.sound
      ⟨.clamp ((a.atMode Mode.bottom).compatible x) (x.compatible (b.atMode Mode.top))
          m.defined hxlo hxhi,
        .clampRev ((a.atMode Mode.bottom).compatible x) (x.compatible (b.atMode Mode.top))
          m.defined hxlo hxhi⟩
  rw [modal_bottom a m, modal_top b m] at he
  exact (congrArg f he).trans ((f.map_inf' _ _).trans
    (congrArg₂ (· ⊓ ·) (f.map_sup' _ _) (f.map_inf' _ _)))

def coordinateValue : Coordinate → Bool → Mode → Bool
  | .unaffected, x, _ => x
  | .locality, x, m => x && m.isLocal
  | .affinity, x, m => x && m.once
  | .uniqueness, x, m => x || !m.unique

/-- A common finite set of modal labels can be observed using one coordinate
and one mode assignment. The unaffected coordinate requires no scalar model. -/
theorem observer_modal_realizable (f : LatticeHom (Order Δ shape) Bool)
    (a b : Carrier Δ shape) (hab : a ≤ b)
    (hb : observer f (a.atMode Mode.bottom) = false)
    (ht : observer f (b.atMode Mode.top) = true) (ms : List (GuardedMode Δ)) :
    ∃ c η, (c = Coordinate.unaffected ∨ ModeModels Δ η) ∧
      ∀ x, a.atMode Mode.bottom ≤ x → x ≤ b.atMode Mode.top →
        ∀ m ∈ ms, observer f (m.act x) = coordinateValue c (observer f x) (m.value η) := by
  rcases observer_coordinate_cases f hab ht with h | h | h | h
  · refine ⟨.unaffected, fun _ => Mode.identity, Or.inl rfl, ?_⟩
    intro x hxlo hxhi m _
    rw [observer_modal_interval f a b x hxlo hxhi m]
    simp only [BandScalar.observe_false_of_upper f (a.atMode Mode.bottom)
        (by simpa using h.1) (m.band .lower),
      BandScalar.observe_true_of_lower f (b.atMode Mode.top)
        (by simpa using h.2.1) (m.band .locality),
      BandScalar.observe_true_of_lower f (b.atMode Mode.top)
        (by simpa using h.2.2) (m.band .affinity),
      Bool.or_false, Bool.and_true, coordinateValue]
  · obtain ⟨η, hη, he⟩ := BandScalar.observations_realizable f (b.atMode Mode.top)
      (c := .locality) (by simpa using h.2.1) (by simpa using ht)
      (ms.map (fun m => m.band .locality))
    refine ⟨.locality, η, Or.inr hη, ?_⟩
    intro x hxlo hxhi m hm
    rw [observer_modal_interval f a b x hxlo hxhi m]
    have hlo := BandScalar.observe_false_of_upper f (a.atMode Mode.bottom)
      (by simpa using h.1) (m.band .lower)
    have haff := BandScalar.observe_true_of_lower f (b.atMode Mode.top)
      (by simpa using h.2.2) (m.band .affinity)
    simpa only [hlo, haff, Bool.or_false, Bool.and_true, coordinateValue] using
      congrArg (observer f x && ·) (he (m.band .locality) (List.mem_map.mpr ⟨m, hm, rfl⟩)).symm
  · obtain ⟨η, hη, he⟩ := BandScalar.observations_realizable f (b.atMode Mode.top)
      (c := .affinity) (by simpa using h.2.2) (by simpa using ht)
      (ms.map (fun m => m.band .affinity))
    refine ⟨.affinity, η, Or.inr hη, ?_⟩
    intro x hxlo hxhi m hm
    rw [observer_modal_interval f a b x hxlo hxhi m]
    have hlo := BandScalar.observe_false_of_upper f (a.atMode Mode.bottom)
      (by simpa using h.1) (m.band .lower)
    have hloc := BandScalar.observe_true_of_lower f (b.atMode Mode.top)
      (by simpa using h.2.1) (m.band .locality)
    simpa only [hlo, hloc, Bool.or_false, Bool.true_and, coordinateValue] using
      congrArg (observer f x && ·) (he (m.band .affinity) (List.mem_map.mpr ⟨m, hm, rfl⟩)).symm
  · obtain ⟨η, hη, he⟩ := BandScalar.observations_realizable f (a.atMode Mode.bottom)
      (c := .lower) (by simpa using hb) (by simpa using h.1)
      (ms.map (fun m => m.band .lower))
    refine ⟨.uniqueness, η, Or.inr hη, ?_⟩
    intro x hxlo hxhi m hm
    rw [observer_modal_interval f a b x hxlo hxhi m]
    have hloc := BandScalar.observe_true_of_lower f (b.atMode Mode.top)
      (by simpa using h.2.1) (m.band .locality)
    have haff := BandScalar.observe_true_of_lower f (b.atMode Mode.top)
      (by simpa using h.2.2) (m.band .affinity)
    simpa only [hloc, haff, Bool.and_true, coordinateValue] using
      congrArg (observer f x || ·) (he (m.band .lower) (List.mem_map.mpr ⟨m, hm, rfl⟩)).symm

end ModalityInference.ComparisonAlgebra
