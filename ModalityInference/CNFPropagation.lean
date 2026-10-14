import ModalityInference.ModeBackend

/-! Deterministic elimination for the unrestricted Boolean compatibility domain.

This backend can produce exponentially many resolvents. It is separate from the
polarized inference algorithm: it provides a total general-domain compatibility
procedure without guessing Boolean assignments or retaining search alternatives.
-/

namespace ModalityInference.CNFPropagation

abbrev Assignment := List (Nat × Bool)

def valuation (σ : Assignment) (v : Nat) : Bool := (σ.lookup v).getD false

def atoms (cs : CNF) : List Nat := cs.flatMap (List.map Prod.fst)

/-- A fixed order shared by elimination and witness reconstruction. -/
def pivots (cs : CNF) : List Nat := (atoms cs).dedup.mergeSort (· ≤ ·)

def without (v : Nat) (c : Clause) : Clause := c.filter (fun lit => lit.1 != v)

/-- Tautological pivot clauses impose neither a lower nor an upper bound. -/
def lower (cs : CNF) (v : Nat) : CNF :=
  (cs.filter (fun c => c.contains (v, true) && !c.contains (v, false))).map (without v)

def upper (cs : CNF) (v : Nat) : CNF :=
  (cs.filter (fun c => c.contains (v, false) && !c.contains (v, true))).map (without v)

def unaffected (cs : CNF) (v : Nat) : CNF :=
  cs.filter (fun c => !c.contains (v, true) && !c.contains (v, false))

/-- Cross every lower bound with every upper bound, then remove redundancy. -/
def eliminate (cs : CNF) (v : Nat) : CNF :=
  cleanCNF (unaffected cs v ++
    (lower cs v).flatMap (fun l => (upper cs v).map (l ++ ·)))

def crossSize (cs : CNF) (v : Nat) : Nat := (lower cs v).length * (upper cs v).length

def clauseValue (σ : Nat → Bool) (c : Clause) : Bool :=
  c.any (fun lit => σ lit.1 == lit.2)

/-- The Boolean join of the demands imposed by all lower bounds. -/
def lowerJoin (cs : CNF) (v : Nat) (σ : Nat → Bool) : Bool :=
  (lower cs v).any (fun c => !clauseValue σ c)

def run : Nat → List Nat → CNF → RunResult Assignment
  | 0, _, _ => .exhausted
  | fuel + 1, vs, cs =>
    if cs.any List.isEmpty then .rejected "inconsistent modality bounds: empty clause"
    else match vs with
      | [] => .success []
      | v :: rest => do
        if crossSize cs v > fuel + 1 then .exhausted else do
          let σ ← run fuel rest (eliminate cs v)
          return (v, lowerJoin cs v (valuation σ)) :: σ

/-- Fuel bounds elimination depth and the size of every crossed clause product. -/
def solve (fuel : Nat) (cs : CNF) : RunResult Assignment := run fuel (pivots cs) cs

end ModalityInference.CNFPropagation
