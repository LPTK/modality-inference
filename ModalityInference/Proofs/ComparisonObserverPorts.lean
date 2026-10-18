import ModalityInference.Proofs.ComparisonAlgebraOrder
import ModalityInference.Proofs.ComparisonAlgebraReification

/-! Exact finite observation patterns for actual child lattice observers.
A mixed pattern is realizable precisely when its finite meet-to-join algebra
obligation fails. One-sided patterns use constant observers. This applies to
the original full algebra under arbitrary ambient bounds; every supplied
carrier retains its own shape and definedness certificates. -/

namespace ModalityInference.ComparisonObserverPorts

open ComparisonAlgebra

section Lattice
variable {α : Type*} [DistribLattice α]

def meetList (a : α) (as : List α) : α := as.foldr (· ⊓ ·) a

def joinList (a : α) (as : List α) : α := as.foldr (· ⊔ ·) a

theorem meetList_le (a : α) (as : List α) {x : α} (hx : x ∈ a :: as) :
    meetList a as ≤ x := by
  induction as with
  | nil => exact (List.mem_singleton.mp hx).symm.le
  | cons b bs ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact inf_le_right.trans (ih (List.mem_cons_self))
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact inf_le_left
      · exact inf_le_right.trans (ih (List.mem_cons_of_mem _ hx))

theorem le_joinList (a : α) (as : List α) {x : α} (hx : x ∈ a :: as) :
    x ≤ joinList a as := by
  induction as with
  | nil => exact (List.mem_singleton.mp hx).le
  | cons b bs ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (ih (List.mem_cons_self)).trans le_sup_right
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact le_sup_left
      · exact (ih (List.mem_cons_of_mem _ hx)).trans le_sup_right

theorem observer_meetList (f : LatticeHom α Bool) (a : α) (as : List α)
    (h : ∀ x ∈ a :: as, f x = true) : f (meetList a as) = true := by
  induction as with
  | nil => exact h _ (List.mem_cons_self)
  | cons b bs ih =>
    change f (b ⊓ meetList a bs) = true
    calc
      _ = f b ⊓ f (meetList a bs) := f.map_inf' _ _
      _ = true := by
        rw [h b (by simp), ih (fun x hx => h x (by simp only [List.mem_cons] at hx ⊢; tauto))]
        rfl

theorem observer_joinList (f : LatticeHom α Bool) (a : α) (as : List α)
    (h : ∀ x ∈ a :: as, f x = false) : f (joinList a as) = false := by
  induction as with
  | nil => exact h _ (List.mem_cons_self)
  | cons b bs ih =>
    change f (b ⊔ joinList a bs) = false
    calc
      _ = f b ⊔ f (joinList a bs) := f.map_sup' _ _
      _ = false := by
        rw [h b (by simp), ih (fun x hx => h x (by simp only [List.mem_cons] at hx ⊢; tauto))]
        rfl

/-- A finite mixed observation pattern has one actual lattice observer exactly
when its meet-to-join child obligation is not derivable. -/
theorem pattern_iff (a : α) (as : List α) (b : α) (bs : List α) :
    (∃ f : LatticeHom α Bool, (∀ x ∈ a :: as, f x = true) ∧
      (∀ x ∈ b :: bs, f x = false)) ↔ ¬ meetList a as ≤ joinList b bs := by
  constructor
  · rintro ⟨f,ht,hf⟩ hab
    have h := OrderHomClass.monotone f hab
    rw [observer_meetList f a as ht, observer_joinList f b bs hf] at h
    exact (by decide : ¬(true : Bool) ≤ false) h
  · intro h
    obtain ⟨f,ht,hf⟩ := lattice_separator h
    refine ⟨f,?_,?_⟩
    · intro x hx
      have h := OrderHomClass.monotone f (meetList_le a as hx)
      rw [ht] at h
      exact Bool.eq_true_of_true_le h
    · intro x hx
      have h := OrderHomClass.monotone f (le_joinList b bs hx)
      rw [hf] at h
      exact Bool.eq_false_of_le_false h

/-- Empty sides require no lattice top or bottom. A constant observer realizes
every one-sided finite pattern. -/
def obstruction : List α → List α → Prop
  | a :: as, b :: bs => meetList a as ≤ joinList b bs
  | _, _ => False

private def constant (b : Bool) : LatticeHom α Bool where
  toFun _ := b
  map_sup' _ _ := by cases b <;> rfl
  map_inf' _ _ := by cases b <;> rfl

theorem pattern_iff_no_obstruction (positive negative : List α) :
    (∃ f : LatticeHom α Bool, (∀ x ∈ positive, f x = true) ∧
      (∀ x ∈ negative, f x = false)) ↔ ¬ obstruction positive negative := by
  cases positive with
  | nil =>
    constructor
    · simp [obstruction]
    · intro _
      exact ⟨constant false, by simp, fun _ _ => rfl⟩
  | cons a as =>
    cases negative with
    | nil =>
      constructor
      · simp [obstruction]
      · intro _
        exact ⟨constant true, (fun _ _ => rfl), by simp⟩
    | cons b bs => exact pattern_iff a as b bs

end Lattice

section Carriers
variable {Δ : Bounds} {shape : ComparisonShape}

def meetCarrier (a : Carrier Δ shape) (as : List (Carrier Δ shape)) : Carrier Δ shape :=
  as.foldr Carrier.meet a

def joinCarrier (a : Carrier Δ shape) (as : List (Carrier Δ shape)) : Carrier Δ shape :=
  as.foldr Carrier.join a

theorem of_meetCarrier (a : Carrier Δ shape) (as : List (Carrier Δ shape)) :
    Order.of (meetCarrier a as) = meetList (Order.of a) (as.map Order.of) := by
  induction as with
  | nil => rfl
  | cons b bs ih => simp only [meetCarrier, List.foldr_cons, Order.of_meet, List.map_cons, meetList] at *; rw [ih]

theorem of_joinCarrier (a : Carrier Δ shape) (as : List (Carrier Δ shape)) :
    Order.of (joinCarrier a as) = joinList (Order.of a) (as.map Order.of) := by
  induction as with
  | nil => rfl
  | cons b bs ih => simp only [joinCarrier, List.foldr_cons, Order.of_join, List.map_cons, joinList] at *; rw [ih]

/-- The separator test is an actual full-algebra child comparison between
finite lattice combinations of the supplied ports. -/
theorem carrier_pattern_iff (a : Carrier Δ shape) (as : List (Carrier Δ shape))
    (b : Carrier Δ shape) (bs : List (Carrier Δ shape)) :
    (∃ f : LatticeHom (Order Δ shape) Bool,
      (∀ x ∈ a :: as, f (Order.of x) = true) ∧
      (∀ x ∈ b :: bs, f (Order.of x) = false)) ↔
    ¬ AlgebraSubtype Δ (meetCarrier a as).type (joinCarrier b bs).type := by
  have h := pattern_iff (Order.of a) (as.map Order.of) (Order.of b) (bs.map Order.of)
  rw [←of_meetCarrier, ←of_joinCarrier, Order.of_le_of] at h
  simpa only [←List.map_cons, List.forall_mem_map] using h

/-- Empty observation sides have no obligation; no type-level top or bottom
is introduced into the witness language. -/
def carrierObstruction : List (Carrier Δ shape) → List (Carrier Δ shape) → Prop
  | a :: as, b :: bs => AlgebraSubtype Δ (meetCarrier a as).type (joinCarrier b bs).type
  | _, _ => False

theorem carrier_pattern_iff_no_obstruction
    (positive negative : List (Carrier Δ shape)) :
    (∃ f : LatticeHom (Order Δ shape) Bool,
      (∀ x ∈ positive, f (Order.of x) = true) ∧
      (∀ x ∈ negative, f (Order.of x) = false)) ↔
    ¬ carrierObstruction positive negative := by
  cases positive with
  | nil =>
    constructor
    · simp [carrierObstruction]
    · intro _
      exact ⟨constant false, by simp, fun _ _ => rfl⟩
  | cons a as =>
    cases negative with
    | nil =>
      constructor
      · simp [carrierObstruction]
      · intro _
        exact ⟨constant true, (fun _ _ => rfl), by simp⟩
    | cons b bs => exact carrier_pattern_iff a as b bs


theorem boolean_pattern_iff_no_obstruction
    (positive negative : List (Carrier Δ shape)) :
    (∃ f : LatticeHom (Order Δ shape) Bool,
      (∀ x ∈ positive, booleanValue f x.type = true) ∧
      (∀ x ∈ negative, booleanValue f x.type = false)) ↔
    ¬ carrierObstruction positive negative := by
  simpa only [booleanValue_carrier] using carrier_pattern_iff_no_obstruction positive negative

end Carriers
end ModalityInference.ComparisonObserverPorts
