import ModalityInference.Proofs.ComparisonJointAssembly
import ModalityInference.Proofs.ComparisonJointGroupInvariance
import ModalityInference.Proofs.ComparisonJointAssemblyNominal

/-! One assembled result supplies all four observations of the opaque group. -/
namespace ModalityInference.ComparisonJointAssembly

open ComparisonPropagation ComparisonJointGroup ComparisonControls

def parameters (heads : Nat) (headWorld modeWorld : Nat → Bool) (v : Nat) : Bool :=
  if v < heads then headWorld v else modeWorld (v - heads)

@[simp] theorem modes_parameters (heads : Nat) (headWorld modeWorld : Nat → Bool) :
    modes heads (parameters heads headWorld modeWorld) = modeWorld := by
  funext v
  simp [modes, parameters, show ¬heads + v < heads by omega]

theorem valuation_parameters (heads : Nat) (state : ComparisonJointAxes.State count)
    (strategy : (Nat → Bool) → Nat → Bool) (headWorld inputWorld : Nat → Bool) :
    ComparisonJointAxes.valuation heads state strategy headWorld inputWorld =
      ComparisonJointEncoding.valuation (state headWorld inputWorld)
        (parameters heads headWorld (strategy inputWorld)) := by
  funext v
  by_cases hv : v < count
  · simp [ComparisonJointAxes.valuation, ComparisonJointEncoding.valuation, hv]
  · by_cases hh : v < count + heads
    · simp [ComparisonJointAxes.valuation, ComparisonJointEncoding.valuation, parameters, hv, hh,
        show v - count < heads by omega]
    · simp [ComparisonJointAxes.valuation, ComparisonJointEncoding.valuation, parameters, hv, hh,
        show ¬v - count < heads by omega, Nat.sub_sub]

def Result.strategy (result : Result input count flex) (world : Nat → Bool) (v : Nat) : Bool :=
  (result.solution.modes.substitute v).eval world

def Result.choice (result : Result input count flex) (i : Fin (constantCount input)) : Bool :=
  result.solution.constants[i]

noncomputable def Result.localityState (result : Result input count flex) (heads : Nat) :
    ComparisonJointAxes.State (4 * count) :=
  ComparisonJointAxisSummary.coordinateState heads (localityEmbedding input)
    result.choice result.strategy result.locality

noncomputable def Result.otherState (result : Result input count flex) (heads : Nat) :
    ComparisonJointAxes.State (4 * count) :=
  ComparisonJointAxisSummary.coordinateState heads (otherEmbedding input)
    result.choice result.strategy result.other

noncomputable def Result.state (result : Result input count flex) (heads : Nat) :
    ComparisonJointAxes.State (4 * count) :=
  fun headWorld inputWorld v =>
    if hv : v.val < count then ComparisonJointProgram.values result.solution.types headWorld ⟨v.val, hv⟩
    else if v.val < 2 * count then result.localityState heads headWorld inputWorld v
    else result.otherState heads headWorld inputWorld v

@[simp] theorem Result.state_unaffected (result : Result input count flex) (heads : Nat)
    (headWorld inputWorld : Nat → Bool) (i : Fin count) :
    result.state heads headWorld inputWorld (ComparisonJointGroup.state .unaffected i) =
      ComparisonJointProgram.values result.solution.types headWorld i := by
  simp [Result.state, ComparisonJointGroup.state, coordinateNumber, i.isLt]

@[simp] theorem Result.state_locality (result : Result input count flex) (heads : Nat)
    (headWorld inputWorld : Nat → Bool) (i : Fin count) :
    result.state heads headWorld inputWorld (ComparisonJointGroup.state .locality i) =
      result.localityState heads headWorld inputWorld (ComparisonJointGroup.state .locality i) := by
  simp [Result.state, ComparisonJointGroup.state, coordinateNumber,
    show ¬count + i.val < count by omega, show count + i.val < 2 * count by omega]

@[simp] theorem Result.state_affinity (result : Result input count flex) (heads : Nat)
    (headWorld inputWorld : Nat → Bool) (i : Fin count) :
    result.state heads headWorld inputWorld (ComparisonJointGroup.state .affinity i) =
      result.otherState heads headWorld inputWorld (ComparisonJointGroup.state .affinity i) := by
  simp [Result.state, ComparisonJointGroup.state, coordinateNumber,
    show ¬2 * count + i.val < count by omega, show ¬2 * count + i.val < 2 * count by omega]

@[simp] theorem Result.state_uniqueness (result : Result input count flex) (heads : Nat)
    (headWorld inputWorld : Nat → Bool) (i : Fin count) :
    result.state heads headWorld inputWorld (ComparisonJointGroup.state .uniqueness i) =
      result.otherState heads headWorld inputWorld (ComparisonJointGroup.state .uniqueness i) := by
  simp [Result.state, ComparisonJointGroup.state, coordinateNumber,
    show ¬3 * count + i.val < count by omega, show ¬3 * count + i.val < 2 * count by omega]

theorem run_group_input {prepareFuel fuel : Nat} {assumptions required : Bounds}
    {g : ComparisonGroups.Group} {input : Input} {side : Nat → Bool} {flex : List Nat}
    {result : Result input g.leaves.length flex}
    (hp : prepare prepareFuel assumptions required g = .success input)
    (hr : run fuel side flex g.leaves.length g.heads.length input = .success result) :
    ∀ headWorld inputWorld,
      input.Holds g.heads.length (parameters g.heads.length headWorld (result.strategy inputWorld))
        (result.state g.heads.length headWorld inputWorld) := by
  have hlinear := prepare_linear hp
  have hcompiled := run_compiled hr
  have hcoordinates := run_coordinates hlinear.2.1 hlinear.2.2 hr
  have hclauses := run_coordinate_clauses hlinear.2.1 hlinear.2.2 hr
  have hparts := hcompiled.2.2
  simp only [compile, holds_append, and_assoc] at hparts
  intro headWorld inputWorld
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hn := (nominalProgram_guarded_iff hp hcompiled.1.2.1 result.choice
      (result.state g.heads.length) result.strategy (result.state_unaffected g.heads.length)).mp hparts.1
    simpa only [valuation_parameters] using hn headWorld inputWorld
  · have hboundary : ∀ i,
        result.localityState g.heads.length headWorld inputWorld (ComparisonJointGroup.state .unaffected i) =
          result.state g.heads.length headWorld inputWorld (ComparisonJointGroup.state .unaffected i) := by
      intro i
      rw [Result.state_unaffected]
      simpa only [Result.localityState, Result.strategy, Result.choice, boundary,
        Fin.getElem_fin, Vector.getElem_ofFn] using
        ComparisonJointAxisSummary.coordinateState_boundary
          (selectors := input.locality.length + 1) (modes := modeBound input)
          (embedding := localityEmbedding input) (choice := result.choice)
          (strategy := result.strategy) (input := inputWorld) hcompiled.1.2.1
          (hcoordinates.1.2.2.2 inputWorld).2 headWorld i
    apply (prepare_locality_congr hp hboundary
      (fun i => (result.state_locality g.heads.length headWorld inputWorld i).symm)).mp
    simpa only [valuation_parameters, Result.localityState, Result.strategy, Result.choice] using
      hclauses.1 headWorld inputWorld
  · have hboundary : ∀ i,
        result.otherState g.heads.length headWorld inputWorld (ComparisonJointGroup.state .unaffected i) =
          result.state g.heads.length headWorld inputWorld (ComparisonJointGroup.state .unaffected i) := by
      intro i
      rw [Result.state_unaffected]
      simpa only [Result.otherState, Result.strategy, Result.choice, boundary,
        Fin.getElem_fin, Vector.getElem_ofFn] using
        ComparisonJointAxisSummary.coordinateState_boundary
          (selectors := input.other.length + 1) (modes := modeBound input)
          (embedding := otherEmbedding input) (choice := result.choice)
          (strategy := result.strategy) (input := inputWorld) hcompiled.1.2.1
          (hcoordinates.2.2.2.2 inputWorld).2 headWorld i
    apply (prepare_other_congr hp hboundary
      (fun i => (result.state_affinity g.heads.length headWorld inputWorld i).symm)
      (fun i => (result.state_uniqueness g.heads.length headWorld inputWorld i).symm)).mp
    simpa only [valuation_parameters, Result.otherState, Result.strategy, Result.choice] using
      hclauses.2 headWorld inputWorld
  · rw [modes_parameters]
    exact (scalarClauses_correct _ _ _ _).mp hparts.2.2.2.2.2 inputWorld

/-- Every successful assembled solve satisfies all four original group
observations, their compatibility inequalities, and the original scalar guards. -/
theorem run_group_sound {prepareFuel fuel : Nat} {assumptions required : Bounds}
    {g : ComparisonGroups.Group} {input : Input} {side : Nat → Bool} {flex : List Nat}
    {result : Result input g.leaves.length flex}
    (hp : prepare prepareFuel assumptions required g = .success input)
    (hr : run fuel side flex g.leaves.length g.heads.length input = .success result) :
    ∀ headWorld inputWorld,
      GroupHolds assumptions required g
        (parameters g.heads.length headWorld (result.strategy inputWorld))
        (result.state g.heads.length headWorld inputWorld) :=
  fun headWorld inputWorld => (prepare_correct hp _ _).mp (run_group_input hp hr headWorld inputWorld)

theorem run_compatible {prepareFuel fuel : Nat} {assumptions required : Bounds}
    {g : ComparisonGroups.Group} {input : Input} {side : Nat → Bool} {flex : List Nat}
    {result : Result input g.leaves.length flex}
    (hp : prepare prepareFuel assumptions required g = .success input)
    (hr : run fuel side flex g.leaves.length g.heads.length input = .success result)
    (headWorld inputWorld : Nat → Bool) :
    Compatible (result.state g.heads.length headWorld inputWorld) :=
  (run_group_sound hp hr headWorld inputWorld).2.1

end ModalityInference.ComparisonJointAssembly
