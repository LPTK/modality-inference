import ModalityInference.ComparisonInterpolation
import ModalityInference.SymbolicCNF
import ModalityInference.CompactCNF

/-! Symbolic propagation over a finite lattice basis. A positive CNF denotes a
finite meet of finite joins of basis types. Ordered resolution computes upward
closures and relational images without enumerating Boolean valuations.

The basis and transition relation are explicit inputs: connecting them to a
particular modality algebra requires a separate finite-basis correspondence.
Empty joins and meets are never reified as implicit type extrema. -/
namespace ModalityInference.ComparisonPropagation

def rename (f : Nat → Nat) (clauses : CNF) : CNF :=
  clauses.map (List.map fun literal => (f literal.1, literal.2))

/-- Even atoms are existential input coordinates; odd atoms are the retained
upper coordinates. Every retained occurrence is positive. -/
def upwardSystem (domain : List Nat) (clauses : CNF) : CNF :=
  rename (2 * ·) clauses ++
    domain.map (fun v => [(2 * v, false), (2 * v + 1, true)])

def upwardPivots (domain : List Nat) (clauses : CNF) : List Nat :=
  (CNFPropagation.pivots (upwardSystem domain clauses)).filter (fun v => v % 2 == 0)

/-- Ordered projection needs only the residual clauses. Subsumption minimization
between pivots prevents redundant resolvents from accumulating. -/
def project : List Nat → CNF → CNF
  | [], clauses => CompactCNF.clean clauses
  | v :: rest, clauses =>
      project rest (CNFPropagation.eliminate (CompactCNF.clean clauses) v)

/-- Existential image on `domain`, closed upward in every retained coordinate.
The result contains only positive literals from `domain`. -/
def upward (domain : List Nat) (clauses : CNF) : CNF :=
  rename (· / 2)
    (project (upwardPivots domain clauses) (upwardSystem domain clauses))

def join (left right : CNF) : CNF :=
  CompactCNF.clean (left.flatMap fun a => right.map (a ++ ·))

def meet (left right : CNF) : CNF := CompactCNF.clean (left ++ right)

def negateClause (clause : Clause) : CNF := clause.map fun (v, p) => [(v, !p)]

def negate (clauses : CNF) : CNF :=
  clauses.foldr (fun clause rest => join (negateClause clause) rest) [[]]

def implies (left right : CNF) : CNF := join (negate left) right

/-- The least polynomial without constants: the meet of all basis generators. -/
def seed (basisSize : Nat) : CNF := (List.range basisSize).map fun v => [(v, true)]

/-- A transition uses even atoms for its input and odd atoms for its output.
Other atoms are existential parameters. The output is closed upward. -/
def image (basisSize : Nat) (relation demand : CNF) : CNF :=
  rename (· / 2) (upward ((List.range basisSize).map fun v => 2 * v + 1)
    (relation ++ rename (2 * ·) demand))

structure Edge (count : Nat) where
  source : Fin count
  target : Fin count
  relation : CNF
  deriving Repr, DecidableEq

abbrev Store (count : Nat) := Vector CNF count

def initial (basisSize : Nat) (lower : Store count) : Store count :=
  Vector.ofFn fun v => join (seed basisSize) (upward (List.range basisSize) lower[v])

def step (basisSize : Nat) (edges : List (Edge count))
    (store : Store count) : Store count :=
  Vector.ofFn fun v => edges.foldr (fun e accumulated =>
    if e.target == v then join (image basisSize e.relation store[e.source]) accumulated
    else accumulated) store[v]

def iterate (basisSize : Nat) (edges : List (Edge count)) : Nat → Store count → Store count
  | 0, store => store
  | steps + 1, store => iterate basisSize edges steps (step basisSize edges store)

/-- A semantic state is a variable and a Boolean basis valuation. The bound is
its cardinality; the implementation never constructs this state space. -/
def height (count basisSize : Nat) : Nat := count * 2 ^ basisSize

/-- Stop early when canonical clauses have already stabilized. -/
def saturate (basisSize : Nat) (edges : List (Edge count)) : Nat → Store count → Store count
  | 0, store => store
  | steps + 1, store =>
    let next := step basisSize edges store
    if next = store then store else saturate basisSize edges steps next

def propagate (basisSize : Nat) (edges : List (Edge count))
    (lower : Store count) : Store count :=
  saturate basisSize edges (height count basisSize) (initial basisSize lower)

structure Action where
  lower : CNF
  upper : CNF
  deriving Repr, DecidableEq

def Action.apply (action : Action) (value : CNF) : CNF :=
  meet (join value action.lower) action.upper

inductive Leaf (count : Nat) where
  | fixed (value : CNF)
  | flex (index : Fin count)
  deriving Repr, DecidableEq

structure Endpoint (count : Nat) where
  leaf : Leaf count
  mode : ModExpr
  deriving Repr, DecidableEq

structure Bound (count : Nat) where
  left : Endpoint count
  right : Endpoint count
  deriving Repr, DecidableEq

inductive Obligation (count : Nat) where
  | lower (target : Fin count) (condition : CNF)
  | edge (source target : Fin count) (condition : CNF)
  | upper (source : Fin count) (condition : CNF)
  | check (condition : CNF)
  deriving Repr, DecidableEq

/-- Compile one modalized leaf inequality after clamping its action. The original
modal guards remain in `theory` or in separate constant obligations. -/
def compileBound (action : ModExpr → Action) (theory : CNF)
    (bound : Bound count) : List (Obligation count) :=
  let left := action bound.left.mode
  let right := action bound.right.mode
  let base := meet left.lower left.upper
  match bound.left.leaf, bound.right.leaf with
  | .fixed a, .fixed b =>
      [.check (implies theory (implies (left.apply a) (right.apply b)))]
  | .fixed a, .flex y =>
      [.lower y (meet theory (meet (left.apply a) (negate right.lower))),
       .check (implies theory (implies (left.apply a) right.upper))]
  | .flex x, .fixed b =>
      [.upper x (implies (meet theory left.upper) (right.apply b)),
       .check (implies theory (implies base (right.apply b)))]
  | .flex x, .flex y =>
      [.lower y (meet theory (meet base (negate right.lower))),
       .edge x y (meet theory (meet left.upper (negate right.lower))),
       .upper x (implies (meet theory left.upper) right.upper),
       .check (implies theory (implies base right.upper))]

/-- A local implication is a relational edge with identical input and output
basis coordinates. Upward closure is supplied by `image`. -/
def diagonal (basisSize : Nat) (condition : CNF) : CNF :=
  rename (2 * ·) condition ++ (List.range basisSize).flatMap fun v =>
    [[(2 * v, false), (2 * v + 1, true)], [(2 * v + 1, false), (2 * v, true)]]

structure Program (count : Nat) where
  lower : Store count
  edges : List (Edge count)
  upper : Store count
  checks : CNF

def Program.empty (count : Nat) : Program count :=
  ⟨Vector.replicate count [[]], [], Vector.replicate count [], []⟩

def Program.add (basisSize : Nat) (program : Program count)
    (obligation : Obligation count) : Program count :=
  match obligation with
  | .lower v condition => { program with
      lower := Vector.ofFn fun w =>
        if w == v then join condition program.lower[w] else program.lower[w] }
  | .edge source target condition => { program with
      edges := ⟨source, target, diagonal basisSize condition⟩ :: program.edges }
  | .upper v condition => { program with
      upper := Vector.ofFn fun w =>
        if w == v then meet condition program.upper[w] else program.upper[w] }
  | .check condition => { program with checks := meet condition program.checks }

def compile (basisSize : Nat) (action : ModExpr → Action) (theory : CNF)
    (bounds : List (Bound count)) : Program count :=
  (bounds.flatMap (compileBound action theory)).foldl
    (Program.add basisSize) (Program.empty count)

def clauseType (basis : List CompareTy) : Clause → Option CompareTy
  | [] => none
  | (v, positive) :: rest => do
    if !positive then none else do
      let head ← basis[v]?
      if rest.isEmpty then return head
      else return .join head (← clauseType basis rest)

/-- Successful reification consists only of actual basis terms, joins and meets.
An empty clause, an empty conjunction, or an out-of-domain atom is explicit failure. -/
def reify (basis : List CompareTy) : CNF → Option CompareTy
  | [] => none
  | clause :: rest => do
    let head ← clauseType basis clause
    if rest.isEmpty then return head
    else return .meet head (← reify basis rest)

/-- All atoms are eliminated algebraically; no valuation choices are explored. -/
def inconsistent (clauses : CNF) : Bool :=
  (project (CNFPropagation.pivots clauses) clauses).any List.isEmpty

def entails (left right : CNF) : Bool :=
  right.all fun clause => inconsistent (left ++ negateClause clause)

def reconstruct (basis : List CompareTy) (store : Store count) : Option (Vector CompareTy count) :=
  if (Vector.finRange count).all (fun v => (reify basis store[v]).isSome) then
    some (Vector.ofFn fun v => (reify basis store[v]).getD .unit)
  else none

/-- Constant and upper obligations are retained symbolically. In particular,
fresh source modalities remain available for the subsequent uniform synthesis. -/
def residual (program : Program count) (store : Store count) : CNF :=
  (List.finRange count).foldr
    (fun v rest => meet (implies store[v] program.upper[v]) rest) program.checks

structure Reduction (count : Nat) where
  store : Store count
  images : Vector CompareTy count
  obligation : CNF

/-- Propagate the lower obligations and reconstruct finite type syntax, while
retaining every upper and constant obligation for the modality stage. -/
def reduce (basis : List CompareTy) (program : Program count) : RunResult (Reduction count) :=
  let store := propagate basis.length program.edges program.lower
  match reconstruct basis store with
  | none => .rejected "no finite lattice image over the comparison basis"
  | some images => .success ⟨store, images, residual program store⟩

/-- Decide the explicit finite-basis problem and return actual finite type
images. This does not assert that an arbitrary input algebra has this basis. -/
def solve (basis : List CompareTy) (program : Program count) : RunResult (Vector CompareTy count) :=
  let store := propagate basis.length program.edges program.lower
  if !entails [] program.checks then .rejected "unsatisfied constant comparison obligation"
  else if !(Vector.finRange count).all (fun v => entails store[v] program.upper[v]) then
    .rejected "incompatible comparison interval"
  else match reconstruct basis store with
    | none => .rejected "no finite lattice image over the comparison basis"
    | some images => .success images

end ModalityInference.ComparisonPropagation
