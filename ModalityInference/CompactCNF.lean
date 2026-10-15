import ModalityInference.ModeBackend

/-! Direct CNF normalization with canonical clauses and subsumption deletion.
No new atoms are introduced. Distribution can still require exponentially many
clauses; fuel bounds recursive depth and every intermediate clause product. -/
namespace ModalityInference.CompactCNF

/-- A fixed ordering distinguishes the two polarities of each atom. -/
def literalKey (literal : Literal) : Nat :=
  2 * literal.1 + if literal.2 then 1 else 0

def canonical (clause : Clause) : Clause :=
  clause.dedup.mergeSort (fun a b => literalKey a ≤ literalKey b)

/-- Every literal in the stronger clause occurs in the weaker clause. -/
def subsumes (stronger weaker : Clause) : Bool :=
  stronger.all weaker.contains

/-- Maintain the conjunction while dropping tautologies and redundant clauses. -/
def insert (clause : Clause) (clauses : CNF) : CNF :=
  if clauseTautology clause then clauses
  else if clauses.any (fun old => subsumes old clause) then clauses
  else clause :: clauses.filter (fun old => !subsumes clause old)

def clean : CNF → CNF
  | [] => []
  | clause :: clauses => insert (canonical clause) (clean clauses)

/-- Process the same clauses in the same order using the tail-safe list fold. -/
def cleanTail (clauses : CNF) : CNF :=
  clauses.foldr (fun clause rest => insert (canonical clause) rest) []

@[csimp] theorem clean_eq_cleanTail : clean = cleanTail := by
  funext clauses
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
    simpa only [clean, cleanTail, List.foldr_cons] using congrArg (insert (canonical clause)) ih

def cnfOr (limit : Nat) (a b : CNF) : RunResult CNF :=
  if a.length * b.length > limit then .exhausted
  else .success (clean (a.flatMap fun x => b.map (x ++ ·)))

def toCNF : Nat → Bool → BoolExpr → RunResult CNF
  | 0, _, _ => .exhausted
  | fuel + 1, positive, e => match e with
    | .const b => .success (if b == positive then [] else [[]])
    | .atom n => .success [[(n, positive)]]
    | .and a b => do
      let x ← toCNF fuel positive a
      let y ← toCNF fuel positive b
      if positive then return clean (x ++ y) else cnfOr (fuel + 1) x y
    | .or a b => do
      let x ← toCNF fuel positive a
      let y ← toCNF fuel positive b
      if positive then cnfOr (fuel + 1) x y else return clean (x ++ y)
    | .imp a b => do
      let x ← toCNF fuel (!positive) a
      let y ← toCNF fuel positive b
      if positive then cnfOr (fuel + 1) x y else return clean (x ++ y)

end ModalityInference.CompactCNF
