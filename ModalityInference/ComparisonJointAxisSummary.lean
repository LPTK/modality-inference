import ModalityInference.ComparisonJointAxes
import ModalityInference.ComparisonJointProgram
import ModalityInference.ComparisonJointSummary
import ModalityInference.ComparisonBoundaryPropagation

/-! An axis summary uses local selector slots and embeds them into one shared
constant vector. Original scalar atoms follow the local selector prefix. -/
namespace ModalityInference.ComparisonJointAxisSummary

open ComparisonPropagation

def decode (embedding : Fin selectors → Fin constants) (i : Nat) : Sum (Fin constants) Nat :=
  if hi : i < selectors then .inl (embedding ⟨i, hi⟩) else .inr (i - selectors)

def parameterWorld (embedding : Fin selectors → Fin constants) (choice : Fin constants → Bool)
    (modes : Nat → Bool) (i : Nat) : Bool :=
  (decode embedding i).elim choice modes

def program (side : Nat → Bool) (component : Bool) (count heads selectors modes : Nat)
    (clauses : CNF) : Program count :=
  ComparisonJointProgram.axisProgram count heads selectors modes
    (ComparisonJointAxes.ownClauses side component count heads clauses)

def compile (side : Nat → Bool) (component : Bool) (count heads selectors modes : Nat)
    (embedding : Fin selectors → Fin constants) (clauses : CNF)
    (boundary : Vector (Fin count) retained) :
    List (ComparisonJointGuarded.GuardedClause heads retained constants) :=
  ComparisonJointSummary.compileGuarded heads (decode embedding)
    (ComparisonBoundaryPropagation.summarize heads (selectors + modes)
      (program side component count heads selectors modes clauses) boundary)

/-- Keep heads, local selectors, and the coordinate's own scalar axis. -/
def keep (side : Nat → Bool) (component : Bool) (heads selectors v : Nat) : Bool :=
  decide (v < heads ∨ (v - heads) / 2 < selectors) ||
    (side ((v - heads) / 2 - selectors) == component)

def fixed (heads selectors : Nat) (baseline : Nat → Bool) (v : Nat) : Bool :=
  if (v - heads) % 2 == 0 then baseline ((v - heads) / 2 - selectors)
  else !baseline ((v - heads) / 2 - selectors)

def projectWorld (side : Nat → Bool) (component : Bool) (heads selectors : Nat)
    (baseline world : Nat → Bool) (v : Nat) : Bool :=
  if keep side component heads selectors v then world v else fixed heads selectors baseline v

/-- Substitute a fixed baseline only for opposite-axis parameter pairs. -/
def restrict (side : Nat → Bool) (component : Bool) (heads selectors : Nat)
    (baseline : Nat → Bool) (clauses : CNF) : CNF :=
  (clauses.filter fun clause => !(clause.any fun literal =>
    !keep side component heads selectors literal.1 && fixed heads selectors baseline literal.1 == literal.2)).map
      (List.filter fun literal => keep side component heads selectors literal.1)

def restrictStore (side : Nat → Bool) (component : Bool) (heads selectors : Nat)
    (baseline : Nat → Bool) (store : Store count) : Store count :=
  Vector.ofFn fun v => restrict side component heads selectors baseline store[v]

end ModalityInference.ComparisonJointAxisSummary
