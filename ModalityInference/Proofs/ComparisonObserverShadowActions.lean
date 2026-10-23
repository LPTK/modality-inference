import ModalityInference.Proofs.ComparisonObserverShadowActionRows
import ModalityInference.Proofs.ComparisonObserverMachineModeTransport
import ModalityInference.Proofs.ComparisonFiniteControlRange
import ModalityInference.Proofs.ComparisonRelativeDiagramActions

/-! One finite shadow diagram carries every total control action. Its defined
part uses the finite range algebra; its boundary part is the literal head
orbit. The certified raw action rows establish both mixed-order transports. -/
namespace ModalityInference.ComparisonObserverShadowActions

open ComparisonObserverShadowPresentation ComparisonObserverShadowActionRows
  ComparisonObserverHeadCuts ComparisonRawHeadFiniteOrbits ComparisonFiniteControls
  ComparisonObserverRangeTransfer ComparisonRelativeIntervals ComparisonRelativeDiagramActions

noncomputable section
attribute [local instance] Classical.propDecidable

variable {Δ : Bounds} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (B : Boundary Δ) (names : List ModVar) (base : Nat)

def diagramRows (extra : List (RawRow hn (assign hn B names base))) : List (Ty × Ty) :=
  orderRows (assign hn B names base) (presentation hn B names base).shadowVars ++
    RawRow.rows hn (assign hn B names base) (rows hn B names base ++ extra)

structure Realization (extra : List (RawRow hn (assign hn B names base))) where
  count : Nat
  machine : ComparisonObserverMachine.Machine count
  certified : ComparisonObserverMachine.Certified (context Δ (diagramRows hn B names base extra)) machine
  interval : IntervalData (ComparisonObserverFiniteRange.Value machine) (Point B names)
  lower_eq : ∀ p, interval.lower p = if LowerInhabited (Δ := Δ) (shape := .unit) p.term
    then some (ComparisonObserverFiniteRange.atom certified.range (shadowName base (p,false))) else none
  upper_eq : ∀ p, interval.upper p = if UpperInhabited (Δ := Δ) (shape := .unit) p.term
    then some (ComparisonObserverFiniteRange.atom certified.range (shadowName base (p,true))) else none

theorem exists_bounded_realization (extra : List (RawRow hn (assign hn B names base))) :
    ∃ R : Realization hn B names base extra,
      R.count ≤ ComparisonObserverBoundary.sizeBound
        (context Δ (diagramRows hn B names base extra))
        ((presentation hn B names base).shadowVars.map CompareTy.var) := by
  obtain ⟨count,hcount,machine,hc,J,hl,hu⟩ := finite_head_diagram hn
    Point.term Point.le_iff base (rows hn B names base ++ extra)
  exact ⟨⟨count,machine,hc,J,hl,hu⟩,hcount⟩

theorem exists_realization (extra : List (RawRow hn (assign hn B names base))) :
    Nonempty (Realization hn B names base extra) := by
  obtain ⟨R,_⟩ := exists_bounded_realization hn B names base extra
  exact ⟨R⟩

namespace Realization

variable {hn B names base} {extra : List (RawRow hn (assign hn B names base))}
    (R : Realization hn B names base extra)

def modal : ComparisonObserverMachine.ModalValid Δ R.machine :=
  ComparisonObserverMachineModeTransport.modal_valid
    (fun η => (context_modes Δ (diagramRows hn B names base extra) η).mp) R.certified.modal

def range : ComparisonObserverMachine.RangeClosed Δ R.machine :=
  ComparisonObserverMachineModeTransport.range_closed
    (fun η => (context_modes Δ (diagramRows hn B names base extra) η).mp) R.certified.range

def coherent : ComparisonObserverMachine.Coherent Δ R.machine :=
  ComparisonObserverMachineModeTransport.coherent
    (fun η => (context_modes Δ (diagramRows hn B names base extra) η).mp) R.certified.coherent

theorem contains_row {r : RawRow hn (assign hn B names base)}
    (hr : r ∈ rows hn B names base) : r.pair ∈ diagramRows hn B names base extra :=
  List.mem_append_right _ (List.mem_map.mpr ⟨r,List.mem_append_left _ hr,rfl⟩)

def action (m : Control Δ names) : Action R.interval where
  defined := ⟨ComparisonFiniteControlRange.action R.modal R.range m,
    ComparisonObserverFiniteRange.modal_mono R.range R.modal (expression m) (expression_defined m)⟩
  boundary := Point.action m
  lower_shadow := by
    intro p a ha
    have hp : LowerInhabited (Δ := Δ) (shape := .unit) p.term := by
      by_contra hp
      rw [R.lower_eq p,if_neg hp] at ha
      cases ha
    have he : a = ComparisonObserverFiniteRange.atom R.certified.range (shadowName base (p,false)) := by
      simpa only [R.lower_eq p,if_pos hp,Option.some.injEq] using ha.symm
    refine ⟨ComparisonObserverFiniteRange.atom R.certified.range (shadowName base (Point.act m p,false)),?_,?_⟩
    · exact (R.lower_eq (Point.act m p)).trans (if_pos (lower_act B names m p hp))
    · rw [he]
      intro i
      apply R.certified.bounds i (.modal (.var (shadowName base (p,false))) (expression m))
        (.var (shadowName base (Point.act m p,false)))
      exact context_sub.mpr (contains_row (extra := extra) (lowerRow_mem hn B names base m p hp))
  upper_shadow := by
    intro p b hb
    have hp : UpperInhabited (Δ := Δ) (shape := .unit) p.term := by
      by_contra hp
      rw [R.upper_eq p,if_neg hp] at hb
      cases hb
    have he : b = ComparisonObserverFiniteRange.atom R.certified.range (shadowName base (p,true)) := by
      simpa only [R.upper_eq p,if_pos hp,Option.some.injEq] using hb.symm
    refine ⟨ComparisonObserverFiniteRange.atom R.certified.range (shadowName base (Point.act m p,true)),?_,?_⟩
    · exact (R.upper_eq (Point.act m p)).trans (if_pos (upper_act B names m p hp))
    · rw [he]
      intro i
      apply R.certified.bounds i (.var (shadowName base (Point.act m p,true)))
        (.modal (.var (shadowName base (p,true))) (expression m))
      exact context_sub.mpr (contains_row (extra := extra) (upperRow_mem hn B names base m p hp))

theorem defined_index (x : ComparisonObserverFiniteRange.Value R.machine) :
    Monotone (fun m : Control Δ names => (R.action m).defined x) :=
  ComparisonFiniteControlRange.action_index R.modal R.range x

theorem boundary_index (p : Point B names) :
    Monotone (fun m : Control Δ names => (R.action m).boundary p) := Point.act_index_mono p

theorem map_one (x : ComparisonObserverFiniteRange.Value R.machine ⊕ Point B names) :
    (R.action 1).map x = x := by
  cases x with
  | inl a => exact congrArg Sum.inl (ComparisonFiniteControlRange.action_one R.modal R.range a)
  | inr p => exact congrArg Sum.inr (Point.act_one p)

theorem map_mul (m n : Control Δ names)
    (x : ComparisonObserverFiniteRange.Value R.machine ⊕ Point B names) :
    (R.action m).map ((R.action n).map x) = (R.action (n * m)).map x := by
  cases x with
  | inl a => exact congrArg Sum.inl (ComparisonFiniteControlRange.action_mul R.modal R.range n m a).symm
  | inr p => exact congrArg Sum.inr (Point.act_mul m n p)

def orbit (x : ComparisonObserverFiniteRange.Value R.machine ⊕ Point B names) :
    ComparisonRelativeCoordinates.Coordinates (Control Δ names) R.interval.Completion :=
  diagramOrbit R.action R.defined_index R.boundary_index x

theorem orbit_le_iff (x y : ComparisonObserverFiniteRange.Value R.machine ⊕ Point B names) :
    R.orbit x ≤ R.orbit y ↔ R.interval.Rel x y := by
  apply diagramOrbit_le_iff R.action R.defined_index R.boundary_index
  intro z
  rw [R.map_one]
  exact ⟨R.interval.rel_refl z,R.interval.rel_refl z⟩

theorem shift_orbit (m : Control Δ names)
    (x : ComparisonObserverFiniteRange.Value R.machine ⊕ Point B names) :
    ComparisonRelativeCoordinates.shift mul_mono m (R.orbit x) = R.orbit ((R.action m).map x) := by
  apply shift_diagramOrbit mul_mono R.action R.defined_index R.boundary_index
  intro n r z
  rw [R.map_mul]
  exact ⟨R.interval.rel_refl _,R.interval.rel_refl _⟩

theorem orbit_space_finite :
    Finite (ComparisonRelativeCoordinates.Coordinates (Control Δ names) R.interval.Completion) :=
  ComparisonRelativeCoordinates.coordinates_finite

end Realization
end
end ModalityInference.ComparisonObserverShadowActions
