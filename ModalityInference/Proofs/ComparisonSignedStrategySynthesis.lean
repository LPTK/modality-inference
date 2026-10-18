import ModalityInference.ComparisonSignedStrategySynthesis
import ModalityInference.Proofs.ComparisonSignedPoints
import ModalityInference.Proofs.ComparisonWorldModes

/-! Point abstraction and world-selector separation compose with one uniform
scalar solver while retaining the same finite image family and selector choices. -/
namespace ModalityInference.ComparisonSignedStrategySynthesis
open ComparisonSignedEndpoints ComparisonWorldClauses

/-- One family is evaluated only at nominal point coordinates. -/
def nominalValue (size : Nat → Nat) (clauses : List CompiledClause)
    (images : Nat → (Nat → Bool) → Bool) : (Nat → Bool) → Nat → Bool :=
  ComparisonSignedWorlds.nominalValue
    (ComparisonSignedWorlds.calls (clauses.map ComparisonSignedPoints.clause))
    (fun world=>world)
    (ComparisonSignedPoints.nominalImages (ComparisonSignedWorlds.calls clauses) size images)

def Valid (size : Nat → Nat) (decode : Nat → Nat × Nat)
    (theory : CNF) (clauses : List CompiledClause)
    (images : Nat → (Nat → Bool) → Bool) (strategy : (Nat → Bool) → Nat → Bool) : Prop :=
  ∀world,∀c∈clauses,CNFHolds (ComparisonSignedPoints.raw decode strategy world) theory →
    c.Holds (ComparisonSignedPoints.raw decode strategy world)
      (ComparisonSignedPoints.basisImages size images (ComparisonSignedPoints.raw decode strategy world))

theorem worlds_correct (size : Nat → Nat) (decode : Nat → Nat × Nat)
    (theory : CNF) (clauses : List CompiledClause)
    (images : Nat → (Nat → Bool) → Bool) (strategy : (Nat → Bool) → Nat → Bool) :
    ComparisonWorldClauses.Valid (nominalValue size clauses images) strategy
      (worlds size decode theory clauses) ↔ Valid size decode theory clauses images strategy := by
  exact (ComparisonSignedWorlds.query_valid
    (ComparisonSignedPoints.decode decode)
    (ComparisonSignedPoints.theory (ComparisonSignedWorlds.calls clauses) size theory)
    (clauses.map ComparisonSignedPoints.clause) (fun world=>world) strategy
    (ComparisonSignedPoints.nominalImages (ComparisonSignedWorlds.calls clauses) size images)).trans
    (ComparisonSignedPoints.abstract_valid size decode strategy images theory clauses).symm

/-- The executable scalar query and the remaining nominal obligations share
exactly the same selectors. Its complete reconstruction chooses one modality
strategy for every route and keeps one image family for every source key. -/
theorem query_iff (side : Nat → Bool) (flex : List Nat) (size : Nat → Nat)
    (decode : Nat → Nat × Nat) (theory : CNF) (clauses : List CompiledClause)
    (images : Nat → (Nat → Bool) → Bool) :
    (∃selectors,CNFHolds selectors (scalarQuery side flex size decode theory clauses) ∧
      ∀world,CNFHolds
        (selectedValue (ComparisonWorldModes.worldChoice selectors) (nominalValue size clauses images world))
        (nominalQuery size decode theory clauses)) ↔
      ∃strategy,ModalSynthesis.Uniform side flex strategy ∧
        Valid size decode theory clauses images strategy := by
  rw [show (∃selectors,CNFHolds selectors (scalarQuery side flex size decode theory clauses) ∧
      ∀world,CNFHolds
        (selectedValue (ComparisonWorldModes.worldChoice selectors) (nominalValue size clauses images world))
        (nominalQuery size decode theory clauses)) ↔ _ from
    ComparisonWorldModes.separated_iff side flex (worlds size decode theory clauses)
      (nominalValue size clauses images)]
  apply exists_congr
  intro strategy
  apply and_congr_right
  intro _
  exact worlds_correct size decode theory clauses images strategy

theorem modes_sound {side : Nat → Bool} {flex : List Nat} {size : Nat → Nat}
    {decode : Nat → Nat × Nat} {theory : CNF} {clauses : List CompiledClause}
    {images : Nat → (Nat → Bool) → Bool} {selectors : Nat → Bool}
    (hs : CNFHolds selectors (scalarQuery side flex size decode theory clauses))
    (hn : ∀world,CNFHolds
      (selectedValue (ComparisonWorldModes.worldChoice selectors) (nominalValue size clauses images world))
      (nominalQuery size decode theory clauses)) :
    Valid size decode theory clauses images (fun world v =>
      ((modes side flex size decode theory clauses selectors).substitute v).eval world) := by
  apply (worlds_correct size decode theory clauses images _).mp
  apply selectors_sound (choice:=ComparisonWorldModes.worldChoice selectors)
  exact ⟨(ComparisonWorldModes.query_parts side flex _ selectors |>.mp hs).1,hn,
    ComparisonWorldModes.witness_sound hs⟩

theorem modes_uniform (side : Nat → Bool) (flex : List Nat) (size : Nat → Nat)
    (decode : Nat → Nat × Nat) (theory : CNF) (clauses : List CompiledClause)
    (selectors : Nat → Bool) :
    ModalSynthesis.Uniform side flex (fun world v =>
      ((modes side flex size decode theory clauses selectors).substitute v).eval world) :=
  ComparisonWorldModes.witness_uniform side flex _ selectors

theorem modes_assembles (flex : List Nat) (size : Nat → Nat) (decode : Nat → Nat × Nat)
    (theory : CNF) (clauses : List CompiledClause) (selectors : Nat → Bool)
    (parameters : List (Nat × ModVar)) :
    ∃action,SymbolicSchemeModes.assemble
      (modes ModalSynthesis.locality flex size decode theory clauses selectors) parameters=some action :=
  ComparisonWorldModes.witness_assembles _ selectors parameters

end ModalityInference.ComparisonSignedStrategySynthesis
