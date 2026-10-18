import ModalityInference.Proofs.ComparisonShapeCandidateZones
import ModalityInference.Proofs.ComparisonShapeRetraction

/-! Simultaneous structural cuts retain anchored template subtrees literally
and erase only parameters whose resolved shapes have no input anchor. -/
namespace ModalityInference.ComparisonShapeRetraction

open ComparisonShape ComparisonShapeSolver

def retained (choices : List ComparisonShape) (ρ : TypeVar → ComparisonShape)
    (s : ComparisonShape) : Bool := s.vars.all fun v => choices.contains (ρ v)

def choose (choices : List ComparisonShape) (ρ : TypeVar → ComparisonShape)
    (v : TypeVar) : ComparisonShape := if choices.contains (ρ v) then ρ v else .unit

def Cut.ofTemplate (choices : List ComparisonShape) (ρ : TypeVar → ComparisonShape)
    (s : ComparisonShape) : Cut :=
  if retained choices ρ s then .keep (s.subst ρ) else
    match s with
    | .var v => .erase (ρ v)
    | .unit => .keep .unit
    | .credit => .keep .credit
    | .prod a b => .prod (ofTemplate choices ρ a) (ofTemplate choices ρ b)
    | .sum a b => .sum (ofTemplate choices ρ a) (ofTemplate choices ρ b)
    | .fn a b => .fn (ofTemplate choices ρ a) (ofTemplate choices ρ b)

theorem retained_iff {choices : List ComparisonShape} {ρ : TypeVar → ComparisonShape}
    {s : ComparisonShape} : retained choices ρ s = true ↔ ∀ v ∈ s.vars, ρ v ∈ choices := by
  simp [retained]

theorem subst_choose_of_retained {choices : List ComparisonShape}
    {ρ : TypeVar → ComparisonShape} {s : ComparisonShape}
    (h : retained choices ρ s = true) : s.subst (choose choices ρ) = s.subst ρ := by
  exact subst_congr s (fun v hv => by simp [choose, (retained_iff.mp h) v hv])

@[simp] theorem Cut.ofTemplate_source (choices : List ComparisonShape)
    (ρ : TypeVar → ComparisonShape) (s : ComparisonShape) :
    (ofTemplate choices ρ s).source = s.subst ρ := by
  induction s <;> rw [ofTemplate] <;> split <;> simp_all [source, ComparisonShape.subst]

@[simp] theorem Cut.ofTemplate_target (choices : List ComparisonShape)
    (ρ : TypeVar → ComparisonShape) (s : ComparisonShape) :
    (ofTemplate choices ρ s).target = s.subst (choose choices ρ) := by
  induction s <;> rw [ofTemplate] <;> split
  all_goals first
    | exact (subst_choose_of_retained ‹_›).symm
    | simp_all [target, ComparisonShape.subst, choose, retained, ComparisonShape.vars]

theorem not_retained_iff {choices : List ComparisonShape} {ρ : TypeVar → ComparisonShape}
    {s : ComparisonShape} : retained choices ρ s ≠ true ↔
      ∃ v ∈ s.vars, ρ v ∉ choices := by
  simp [retained]

theorem subst_values_fixed (s : ComparisonShape) {ρ φ : TypeVar → ComparisonShape}
    (h : ∀ v, (ρ v).subst φ = ρ v) : (s.subst ρ).subst φ = s.subst ρ := by
  rw [subst_comp]
  exact subst_congr s (fun v _ => h v)

theorem not_retained_zone {Δ : Bounds} {assignment : Assignment}
    {names : List TypeVar} {ρ : TypeVar → ComparisonShape}
    {templates : List ComparisonShape} {s : ComparisonShape}
    (hmodel : ComparisonShape.Models Δ (action assignment))
    (hkeys : ∀ entry ∈ assignment, entry.1 ∈ names)
    (hbounds : ∀ {a b}, Constraint.sub a b ∈ Δ → ComparisonShape.ofTy a ∈ templates)
    (hρ : ∀ v, (ρ v).subst (action assignment) = ρ v)
    (hn : retained (candidates names (action assignment) templates) ρ s ≠ true)
    (hroot : ∀ w, s.subst ρ ≠ .var w) :
    ComparisonUnanchoredProjection.Zone Δ (action assignment) ((s.subst ρ).subst (action assignment)) := by
  rw [subst_values_fixed s hρ]
  obtain ⟨v, hv, hn⟩ := not_retained_iff.mp hn
  exact unselected_zone hmodel hkeys hbounds hv hn hroot

theorem Cut.ofTemplate_valid {Δ : Bounds} {assignment : Assignment}
    {names : List TypeVar} {ρ : TypeVar → ComparisonShape}
    {templates : List ComparisonShape}
    (hmodel : ComparisonShape.Models Δ (action assignment))
    (hkeys : ∀ entry ∈ assignment, entry.1 ∈ names)
    (hbounds : ∀ {a b}, Constraint.sub a b ∈ Δ → ComparisonShape.ofTy a ∈ templates)
    (hρ : ∀ v, (ρ v).subst (action assignment) = ρ v) (s : ComparisonShape) :
    (ofTemplate (candidates names (action assignment) templates) ρ s).Valid Δ (action assignment) := by
  induction s <;> rw [ofTemplate] <;> split
  all_goals try trivial
  all_goals rename_i a b iha ihb hn
  all_goals refine ⟨?_, iha, ihb⟩
  all_goals simp only [ofTemplate_source]
  all_goals exact not_retained_zone hmodel hkeys hbounds hρ hn (by intro w; simp [ComparisonShape.subst])

end ModalityInference.ComparisonShapeRetraction
