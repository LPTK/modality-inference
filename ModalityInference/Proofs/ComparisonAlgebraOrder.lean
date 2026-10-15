import ModalityInference.Proofs.ComparisonAlgebra
import Mathlib.Order.Antisymmetrization
import Mathlib.Order.PrimeSeparator

/-! The guarded comparison algebra forms a distributive lattice on each
defined structural shape. Its order is the original derivability relation. -/
namespace ModalityInference.ComparisonAlgebra

structure Carrier (Δ : Bounds) (shape : ComparisonShape) where
  type : CompareTy
  shaped : type.WellShaped Δ
  defined : type.DefinedUnder Δ
  shape_eq : ComparisonShape.Equivalent Δ type.shape shape

namespace Carrier

variable {Δ : Bounds} {shape : ComparisonShape}

instance : Preorder (Carrier Δ shape) where
  le a b := AlgebraSubtype Δ a.type b.type
  le_refl a := .refl a.shaped
  le_trans _ _ _ := AlgebraSubtype.trans

theorem compatible (a b : Carrier Δ shape) : Compatible Δ a.type b.type :=
  ⟨⟨a.shaped, b.shaped, a.shape_eq.trans b.shape_eq.symm⟩, a.defined, b.defined⟩

def join (a b : Carrier Δ shape) : Carrier Δ shape where
  type := .join a.type b.type
  shaped := (a.compatible b).1
  defined := by
    intro η hη
    exact fun c hc => (List.mem_append.mp hc).elim
      (a.defined η hη c) (b.defined η hη c)
  shape_eq := a.shape_eq

def meet (a b : Carrier Δ shape) : Carrier Δ shape where
  type := .meet a.type b.type
  shaped := (a.compatible b).1
  defined := by
    intro η hη
    exact fun c hc => (List.mem_append.mp hc).elim
      (a.defined η hη c) (b.defined η hη c)
  shape_eq := a.shape_eq

theorem le_join_left (a b : Carrier Δ shape) : a ≤ a.join b :=
  .shaped (.joinLeft (a.compatible b).1)

theorem le_join_right (a b : Carrier Δ shape) : b ≤ a.join b :=
  .shaped (.joinRight (a.compatible b).1)

theorem join_le {a b c : Carrier Δ shape} (ha : a ≤ c) (hb : b ≤ c) : a.join b ≤ c :=
  .joinLeast ha hb

theorem meet_le_left (a b : Carrier Δ shape) : a.meet b ≤ a :=
  .shaped (.meetLeft (a.compatible b).1)

theorem meet_le_right (a b : Carrier Δ shape) : a.meet b ≤ b :=
  .shaped (.meetRight (a.compatible b).1)

theorem le_meet {a b c : Carrier Δ shape} (hab : a ≤ b) (hac : a ≤ c) : a ≤ b.meet c :=
  .meetGreatest hab hac

theorem join_mono {a b c d : Carrier Δ shape} (hac : a ≤ c) (hbd : b ≤ d) :
    a.join b ≤ c.join d :=
  join_le (hac.trans (le_join_left _ _)) (hbd.trans (le_join_right _ _))

theorem meet_mono {a b c d : Carrier Δ shape} (hac : a ≤ c) (hbd : b ≤ d) :
    a.meet b ≤ c.meet d :=
  le_meet ((meet_le_left _ _).trans hac) ((meet_le_right _ _).trans hbd)

end Carrier

abbrev Order (Δ : Bounds) (shape : ComparisonShape) :=
  Antisymmetrization (Carrier Δ shape) (· ≤ ·)

namespace Order

variable {Δ : Bounds} {shape : ComparisonShape}

def of (a : Carrier Δ shape) : Order Δ shape := toAntisymmetrization (· ≤ ·) a

instance : Max (Order Δ shape) where
  max := Quotient.lift₂ (fun a b => of (a.join b)) (by
    intro a b c d hac hbd
    exact Quotient.sound ⟨Carrier.join_mono hac.1 hbd.1, Carrier.join_mono hac.2 hbd.2⟩)

instance : Min (Order Δ shape) where
  min := Quotient.lift₂ (fun a b => of (a.meet b)) (by
    intro a b c d hac hbd
    exact Quotient.sound ⟨Carrier.meet_mono hac.1 hbd.1, Carrier.meet_mono hac.2 hbd.2⟩)

instance : Lattice (Order Δ shape) where
  sup := max
  inf := min
  le_sup_left a b := Quotient.inductionOn₂ a b Carrier.le_join_left
  le_sup_right a b := Quotient.inductionOn₂ a b Carrier.le_join_right
  sup_le a b c := Quotient.inductionOn₃ a b c fun _ _ _ => Carrier.join_le
  inf_le_left a b := Quotient.inductionOn₂ a b Carrier.meet_le_left
  inf_le_right a b := Quotient.inductionOn₂ a b Carrier.meet_le_right
  le_inf a b c := Quotient.inductionOn₃ a b c fun _ _ _ => Carrier.le_meet

instance : DistribLattice (Order Δ shape) where
  le_sup_inf a b c := by
    induction a using Antisymmetrization.induction_on
    induction b using Antisymmetrization.induction_on
    induction c using Antisymmetrization.induction_on
    rename_i a b c
    exact AlgebraSubtype.equationRev (.distrib true (a.compatible b) (a.compatible c))

@[simp] theorem of_le_of (a b : Carrier Δ shape) :
    of a ≤ of b ↔ AlgebraSubtype Δ a.type b.type := Iff.rfl

@[simp] theorem of_join (a b : Carrier Δ shape) : of (a.join b) = of a ⊔ of b := rfl

@[simp] theorem of_meet (a b : Carrier Δ shape) : of (a.meet b) = of a ⊓ of b := rfl

end Order

private theorem bounded_separator {α : Type*} [DistribLattice α] [BoundedOrder α]
    {a b : α} (hab : ¬ a ≤ b) :
    ∃ f : LatticeHom α Bool, f a = true ∧ f b = false := by
  classical
  have hd : Disjoint ((_root_.Order.PFilter.principal a : _root_.Order.PFilter α) : Set α)
      ((_root_.Order.Ideal.principal b : _root_.Order.Ideal α) : Set α) :=
    Set.disjoint_left.mpr fun _ hx hy => hab (le_trans hx hy)
  obtain ⟨J, hJ, hbJ, hdJ⟩ := DistribLattice.prime_ideal_of_disjoint_filter_ideal hd
  have ha : a ∉ J := Set.disjoint_left.mp hdJ (by exact le_rfl)
  have hb : b ∈ J := hbJ (by exact le_rfl)
  let value := fun x : α => decide (x ∉ J)
  refine ⟨{ toFun := value, map_sup' := ?_, map_inf' := ?_ }, ?_, ?_⟩
  · intro x y
    apply Bool.eq_iff_iff.mpr
    simp [value, _root_.Order.Ideal.sup_mem_iff]
  · intro x y
    have he : x ⊓ y ∈ J ↔ x ∈ J ∨ y ∈ J :=
      ⟨hJ.mem_or_mem, fun h => h.elim (J.lower inf_le_left) (J.lower inf_le_right)⟩
    apply Bool.eq_iff_iff.mpr
    simp [value, he]
  · exact decide_eq_true ha
  · exact decide_eq_false (not_not_intro hb)

theorem lattice_separator {α : Type*} [DistribLattice α] {a b : α} (hab : ¬ a ≤ b) :
    ∃ f : LatticeHom α Bool, f a = true ∧ f b = false := by
  have he : ¬ ((a : WithBot α) : WithTop (WithBot α)) ≤
      ((b : WithBot α) : WithTop (WithBot α)) := by simpa using hab
  obtain ⟨f, ha, hb⟩ := bounded_separator he
  refine ⟨{ toFun := fun x => f ((x : WithBot α) : WithTop (WithBot α))
            map_sup' := ?_, map_inf' := ?_ }, ha, hb⟩
  · intro x y
    simpa only [← WithTop.coe_sup, ← WithBot.coe_sup] using
      f.map_sup' ((x : WithBot α) : WithTop (WithBot α))
      ((y : WithBot α) : WithTop (WithBot α))
  · intro x y
    simpa only [← WithTop.coe_inf, ← WithBot.coe_inf] using
      f.map_inf' ((x : WithBot α) : WithTop (WithBot α))
      ((y : WithBot α) : WithTop (WithBot α))

/-- Boolean lattice observations separate exactly the derivable inequalities
of defined types in a common shape class. -/
theorem subtype_iff_boolean_observers {Δ : Bounds} {shape : ComparisonShape}
    (a b : Carrier Δ shape) :
    AlgebraSubtype Δ a.type b.type ↔
      ∀ f : LatticeHom (Order Δ shape) Bool, f (Order.of a) ≤ f (Order.of b) := by
  constructor
  · intro hab f
    exact OrderHomClass.monotone f hab
  · intro h
    by_contra hn
    obtain ⟨f, ha, hb⟩ := lattice_separator
      (a := Order.of a) (b := Order.of b) hn
    have hh := h f
    exact (by decide : ¬ (true : Bool) ≤ false) (by simpa only [ha, hb] using hh)

end ModalityInference.ComparisonAlgebra
