import ModalityInference.ComparisonJointAssembly
import ModalityInference.ComparisonJointReindex

/-! One guarded solve for all opaque groups, with a shared modality action. -/
namespace ModalityInference.ComparisonJointBatch

open ComparisonPropagation ComparisonJointGuarded

structure Entry where
  heads : Nat
  count : Nat
  input : ComparisonJointGroup.Input

def total (size : Entry → Nat) (entries : List Entry) : Nat :=
  (entries.map size).sum

def offset (size : Entry → Nat) (entries : List Entry) (i : Nat) : Nat :=
  total size (entries.take i)

theorem offset_bound (size : Entry → Nat) (entries : List Entry) (i : Nat)
    (hi : i < entries.length) :
    offset size entries i + size entries[i] ≤ total size entries := by
  induction entries generalizing i with
  | nil => simp at hi
  | cons entry entries ih =>
    cases i with
    | zero => simp [offset, total]
    | succ i =>
      have h := ih i (by simpa using hi)
      simpa [offset, total, Nat.add_assoc] using Nat.add_le_add_left h (size entry)

def embed (size : Entry → Nat) (entries : List Entry) (i : Fin entries.length)
    (j : Fin (size entries[i])) : Fin (total size entries) :=
  ⟨offset size entries i.val + j.val,
    lt_of_lt_of_le (Nat.add_lt_add_left j.isLt _) (offset_bound size entries i.val i.isLt)⟩

/-- Unrelated nominal heads are identified with the group's first head. -/
def project (size : Entry → Nat) (entries : List Entry) (i : Fin entries.length) (v : Nat) : Nat :=
  if offset size entries i.val ≤ v ∧ v < offset size entries i.val + size entries[i]
  then v - offset size entries i.val else 0

def constants (entry : Entry) : Nat := ComparisonJointAssembly.constantCount entry.input

def compile (side : Nat → Bool) (entries : List Entry) (minimumModes : Nat := 0)
    (scalar : CNF := []) :
    List (GuardedClause (total Entry.heads entries) (total Entry.count entries) (total constants entries)) :=
  (List.finRange entries.length).flatMap (fun i =>
    ComparisonJointReindex.clauses (embed Entry.heads entries i) (embed Entry.count entries i)
      (embed constants entries i)
      (ComparisonJointAssembly.compile side entries[i].count entries[i].heads entries[i].input minimumModes)) ++
    ComparisonJointAssembly.scalarClauses scalar

structure Result (entries : List Entry) (flex : List Nat) where
  solution : ComparisonJointGuarded.Result (total Entry.count entries) (total constants entries) flex

def localSolution (entries : List Entry) (result : Result entries flex) (i : Fin entries.length) :
    ComparisonJointGuarded.Result entries[i].count (constants entries[i]) flex :=
  ComparisonJointReindex.result (project Entry.heads entries i) (embed Entry.count entries i)
    (embed constants entries i) result.solution

def localResult (side : Nat → Bool) (entries : List Entry) (result : Result entries flex)
    (i : Fin entries.length) (minimumModes : Nat := 0) :
    ComparisonJointAssembly.Result entries[i].input entries[i].count flex :=
  ComparisonJointAssembly.reconstruct side entries[i].count entries[i].heads entries[i].input
    (localSolution entries result i) minimumModes

def run (fuel : Nat) (side : Nat → Bool) (flex : List Nat) (entries : List Entry)
    (minimumModes : Nat := 0) (scalar : CNF := []) : RunResult (Result entries flex) := do
  let solution ← ComparisonJointGuarded.run fuel side flex (compile side entries minimumModes scalar)
  return ⟨solution⟩

end ModalityInference.ComparisonJointBatch
