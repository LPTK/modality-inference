import ModalityInference.ComparisonJointBatch
import ModalityInference.ComparisonJointAssemblyReification
import ModalityInference.SchemeModeSynthesis

/-! Assemble finite type images and one modality action from a shared batch. -/
namespace ModalityInference.ComparisonJointBatchReification

open ComparisonControls

structure Compiled where
  group : ComparisonGroups.Group
  input : ComparisonJointGroup.Input

def Compiled.entry (c : Compiled) : ComparisonJointBatch.Entry :=
  ⟨c.group.heads.length, c.group.leaves.length, c.input⟩

def entries (groups : List Compiled) : List ComparisonJointBatch.Entry := groups.map Compiled.entry

def prepare (fuel : Nat) (assumptions required : Bounds) (groups : List ComparisonGroups.Group) :
    RunResult (List Compiled) :=
  groups.mapM fun group => do
    let input ← ComparisonJointGroup.prepare fuel assumptions required group
    return ⟨group, input⟩

def entryIndex (groups : List Compiled) (i : Fin groups.length) : Fin (entries groups).length :=
  ⟨i.val, by simpa only [entries, List.length_map] using i.isLt⟩

def recastSolution (compiled : Compiled) (entry : ComparisonJointBatch.Entry)
    (h : entry = compiled.entry)
    (solution : ComparisonJointGuarded.Result entry.count (ComparisonJointBatch.constants entry) flex) :
    ComparisonJointGuarded.Result compiled.group.leaves.length
      (ComparisonJointAssembly.constantCount compiled.input) flex := by
  subst entry
  exact solution

def localSolution (groups : List Compiled)
    (batch : ComparisonJointBatch.Result (entries groups) flex) (i : Fin groups.length) :
    ComparisonJointGuarded.Result groups[i].group.leaves.length
      (ComparisonJointAssembly.constantCount groups[i].input) flex :=
  recastSolution groups[i] (entries groups)[entryIndex groups i]
    (by simp [entries, entryIndex])
    (ComparisonJointBatch.localSolution (entries groups) batch (entryIndex groups i))

def localResult (groups : List Compiled)
    (batch : ComparisonJointBatch.Result (entries groups) flex)
    (i : Fin groups.length) (minimumModes : Nat := 0) :
    ComparisonJointAssembly.Result groups[i].input groups[i].group.leaves.length flex :=
  ComparisonJointAssembly.reconstruct ModalSynthesis.locality groups[i].group.leaves.length
    groups[i].group.heads.length groups[i].input (localSolution groups batch i) minimumModes

def basis (allowed : List ModVar) (group : ComparisonGroups.Group) : Option Basis :=
  match group.heads with
  | [] => none
  | first :: rest => some ⟨.var first, rest.map CompareTy.var, allowed⟩

def groupImages (allowed : List ModVar) (compiled : Compiled)
    (result : ComparisonJointAssembly.Result compiled.input compiled.group.leaves.length flex) :
    Option (List (Nat × CompareTy)) := do
  let b ← basis allowed compiled.group
  (List.finRange compiled.group.leaves.length).mapM fun i => do
    return (compiled.group.leaves[i], ← ComparisonJointAssemblyReification.leaf b result i)

def typeImages (allowed : List ModVar) (groups : List Compiled)
    (batch : ComparisonJointBatch.Result (entries groups) flex) (minimumModes : Nat := 0) :
    Option (List (Nat × CompareTy)) := do
  let images ← (List.finRange groups.length).mapM fun i =>
    groupImages allowed groups[i] (localResult groups batch i minimumModes)
  return images.flatten

structure Output where
  modeAction : Substitution
  types : List (Nat × CompareTy)

def Output.substitution (result : Output) : CompareSubstitution :=
  ⟨result.types, result.modeAction.modes⟩

def assemble (allowed : List ModVar) (modeIds : List Nat) (groups : List Compiled)
    (batch : ComparisonJointBatch.Result (entries groups) (SchemeModeSynthesis.atoms modeIds))
    (minimumModes : Nat := 0) : Option Output := do
  let modeAction ← SymbolicSchemeModes.assemble
    (ComparisonJointAssemblyReification.projectElimination allowed batch.solution.modes)
    (SchemeModeSynthesis.parameters modeIds)
  let types ← typeImages allowed groups batch minimumModes
  return ⟨modeAction, types⟩

end ModalityInference.ComparisonJointBatchReification
