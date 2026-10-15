import ModalityInference.ComparisonShapeSolver
import ModalityInference.ComparisonInterpolation
import ModalityInference.ModeBackend

/-! Finite propagation for partial body parameters with a fixed variance. Each
envelope retains its lattice operation below the outer action. Every accepted comparison
carries a checked structural derivation; no distributive law for partial types
is used. -/
namespace ModalityInference.ComparisonPartialPropagation

def wellShaped (shapes : TypeVar → ComparisonShape) : CompareTy → Bool
  | .var _ | .unit | .credit => true
  | .modal a _ => wellShaped shapes a
  | .prod a b | .sum a b | .fn a b => wellShaped shapes a && wellShaped shapes b
  | .join a b | .meet a b => wellShaped shapes a && wellShaped shapes b &&
      (a.shape.subst shapes == b.shape.subst shapes)

inductive Certificate where
  | refl (a : CompareTy)
  | bound (a b : Ty)
  | trans (ab bc : Certificate)
  | congr (ab : Certificate) (m n : ModExpr)
  | identity (a : CompareTy) (reverse : Bool)
  | compose (a : CompareTy) (m n : ModExpr) (reverse : Bool)
  | joinLeft (a b : CompareTy)
  | joinRight (a b : CompareTy)
  | meetLeft (a b : CompareTy)
  | meetRight (a b : CompareTy)
  | prod (a b c d : CompareTy) (m n : ModExpr) (ac bd : Certificate)
  | sum (a b c d : CompareTy) (m n : ModExpr) (ac bd : Certificate)
  | fn (a b c d : CompareTy) (m n : ModExpr) (ca bd : Certificate)
  deriving Repr

def Certificate.left : Certificate → CompareTy
  | .refl a => a
  | .bound a _ => .ofTy a
  | .trans ab _ => ab.left
  | .congr ab m _ => .modal ab.left m
  | .identity a reverse => if reverse then a else .modal a .epsilon
  | .compose a m n reverse =>
      if reverse then .modal a (.compose m n) else .modal (.modal a m) n
  | .joinLeft a _ => a
  | .joinRight _ b => b
  | .meetLeft a b | .meetRight a b => .meet a b
  | .prod a b _ _ m _ _ _ => .modal (.prod a b) m
  | .sum a b _ _ m _ _ _ => .modal (.sum a b) m
  | .fn a b _ _ m _ _ _ => .modal (.fn a b) m

def Certificate.right : Certificate → CompareTy
  | .refl a => a
  | .bound _ b => .ofTy b
  | .trans _ bc => bc.right
  | .congr ab _ n => .modal ab.right n
  | .identity a reverse => if reverse then .modal a .epsilon else a
  | .compose a m n reverse =>
      if reverse then .modal (.modal a m) n else .modal a (.compose m n)
  | .joinLeft a b | .joinRight a b => .join a b
  | .meetLeft a _ => a
  | .meetRight _ b => b
  | .prod _ _ c d _ n _ _ => .modal (.prod c d) n
  | .sum _ _ c d _ n _ _ => .modal (.sum c d) n
  | .fn _ _ c d _ n _ _ => .modal (.fn c d) n

def Certificate.check (shape : CompareTy → Bool) (mode : ModExpr → ModExpr → Bool)
    (assumptions : Bounds) : Certificate → Bool
  | .refl a => shape a
  | .bound a b => assumptions.contains (.sub a b)
  | .trans ab bc => ab.check shape mode assumptions && bc.check shape mode assumptions &&
      (ab.right == bc.left)
  | .congr ab m n => ab.check shape mode assumptions && mode m n
  | .identity a _ | .compose a _ _ _ => shape a
  | .joinLeft a b | .joinRight a b => shape (.join a b)
  | .meetLeft a b | .meetRight a b => shape (.meet a b)
  | .prod a b c d m n ac bd | .sum a b c d m n ac bd =>
      ac.check shape mode assumptions && bd.check shape mode assumptions && mode m n &&
      (ac.left == .modal a m) && (ac.right == .modal c n) &&
      (bd.left == .modal b m) && (bd.right == .modal d n)
  | .fn a b c d m n ca bd =>
      ca.check shape mode assumptions && bd.check shape mode assumptions &&
      mode m (.compose n .top) &&
      (ca.left == c) && (ca.right == a) && (bd.left == b) && (bd.right == d)

def subterms : Ty → List Ty
  | .var v => [.var v]
  | .unit => [.unit]
  | .credit => [.credit]
  | .modal a m => .modal a m :: subterms a
  | .prod a b => .prod a b :: (subterms a ++ subterms b)
  | .sum a b => .sum a b :: (subterms a ++ subterms b)
  | .fn a b => .fn a b :: (subterms a ++ subterms b)

def anchors (p : SchemePreparation.Prepared) : List Ty :=
  (subterms p.targetType ++ p.assumptions.flatMap (fun c => match c with
    | .sub a b | .equiv a b => subterms a ++ subterms b
    | .equal _ a => subterms a
    | _ => [])).dedup

def envelope : List Ty → CompareTy
  | [] => .unit
  | a :: rest => .modal (ComparisonInterpolation.meet (.ofTy a) (rest.map .ofTy)) .bottom

def ceiling : List Ty → CompareTy
  | [] => .unit
  | a :: rest => .modal (ComparisonInterpolation.join (.ofTy a) (rest.map .ofTy)) .top

/-- Check that every selected variable occurrence has the given variance.
An absent variable satisfies either polarity. -/
def positive (allowed : Nat → Bool) (polarity : Bool) : Ty → Bool
  | .var (.flex n) => !allowed n || polarity
  | .var (.rigid _) | .unit | .credit => true
  | .modal a _ => positive allowed polarity a
  | .prod a b | .sum a b => positive allowed polarity a && positive allowed polarity b
  | .fn a b => positive allowed (!polarity) a && positive allowed polarity b

def action (p : SchemePreparation.Prepared) (shapes : ComparisonShapeSolver.Solved) :
    CompareSubstitution :=
  { types := (List.range' p.firstType (p.nextType - p.firstType)).map fun n =>
      (n, (if positive (fun k => k == n) true p.sourceType then envelope else ceiling)
        ((anchors p).filter fun a =>
          (ComparisonShape.ofTy a).subst shapes.fixedShapes == shapes.resolveAll (.flex n))) }

/-- Expose a finite set of structural premises under the written action path.
No equation is asserted by this operation: every edge is separately certified. -/
def expose : CompareTy → ModExpr → List CompareTy
  | t@(.var _), m | t@(.unit), m | t@(.credit), m => [t, .modal t m]
  | t@(.modal a n), m => t :: .modal t m :: expose a (.compose n m) ++ expose a n
  | t@(.prod a b), m | t@(.sum a b), m | t@(.meet a b), m | t@(.join a b), m =>
      t :: .modal t m :: (expose a m ++ expose b m)
  | t@(.fn a b), m => t :: .modal t m :: (expose a .epsilon ++ expose b .epsilon)

def nodes (p : SchemePreparation.Prepared) (σ : CompareSubstitution) : List CompareTy :=
  (([σ.ty p.sourceType, .ofTy p.targetType] ++
    (anchors p).map CompareTy.ofTy).flatMap (fun t => expose t .epsilon)).dedup

def modeLabels (nodes : List CompareTy) : List ModExpr :=
  (nodes.flatMap fun t => match t with
    | .modal (.fn _ _) m => [m, .compose m .top]
    | .modal _ m => [m]
    | _ => []).dedup

def modeEdges (fuel : Nat) (assumptions : Bounds) (labels : List ModExpr) :
    RunResult (List (ModExpr × ModExpr)) := do
  let mut result := []
  for a in labels do
    for b in labels do
      let report ← ConcreteBackend.entails fuel assumptions [.mode a b]
      if report.valid then result := (a, b) :: result
  return result

structure Graph where
  nodes : Array CompareTy
  edges : Array (Option Certificate)

def Graph.empty (nodes : List CompareTy) : Graph :=
  ⟨nodes.toArray, Array.replicate (nodes.length * nodes.length) none⟩

def Graph.index (g : Graph) (a : CompareTy) : Nat := g.nodes.toList.idxOf a

def Graph.get (g : Graph) (a b : CompareTy) : Option Certificate :=
  let i := g.index a
  let j := g.index b
  if i < g.nodes.size && j < g.nodes.size then
    (g.edges[i * g.nodes.size + j]?).getD none
  else none

def Graph.add (g : Graph) (c : Certificate) : Graph :=
  let i := g.index c.left
  let j := g.index c.right
  let k := i * g.nodes.size + j
  if i < g.nodes.size && j < g.nodes.size && ((g.edges[k]?).getD none).isNone then
    { g with edges := g.edges.set! k (some c) }
  else g

def Graph.count (g : Graph) : Nat := g.edges.foldl (fun n c => if c.isSome then n + 1 else n) 0

def axioms (a : CompareTy) : List Certificate :=
  [.refl a, .identity a false, .identity a true] ++ match a with
  | .join b c => [.joinLeft b c, .joinRight b c]
  | .meet b c => [.meetLeft b c, .meetRight b c]
  | .modal (.modal b m) n => [.compose b m n false, .compose b m n true]
  | .modal b (.compose m n) => [.compose b m n false, .compose b m n true]
  | _ => []

def initialGraph (assumptions : Bounds) (nodes : List CompareTy) : Graph :=
  let seeds := nodes.flatMap axioms ++ assumptions.filterMap (fun c => match c with
    | .sub a b => some (Certificate.bound a b)
    | _ => none)
  seeds.foldl Graph.add (Graph.empty nodes)

/-- One Horn consequence uses existing type edges and one uniformly valid
scalar edge. Partial outer labels never acquire an implicit congruence rule. -/
def structural (mode : ModExpr → ModExpr → Bool) (g : Graph)
    (left right : CompareTy) : Option Certificate := do
  match left, right with
  | .modal a m, .modal b n =>
    if mode m n then
      if let some h := g.get a b then return .congr h m n
    match a, b with
    | .prod a b, .prod c d =>
      if !mode m n then none else
        return .prod a b c d m n (← g.get (.modal a m) (.modal c n))
          (← g.get (.modal b m) (.modal d n))
    | .sum a b, .sum c d =>
      if !mode m n then none else
        return .sum a b c d m n (← g.get (.modal a m) (.modal c n))
          (← g.get (.modal b m) (.modal d n))
    | .fn a b, .fn c d =>
      if !mode m (.compose n .top) then none else
        return .fn a b c d m n (← g.get c a) (← g.get b d)
    | _, _ => none
  | _, _ => none

def Graph.closeTransitive (graph : Graph) : Graph := Id.run do
  let mut g := graph
  for k in [:g.nodes.size] do
    for i in [:g.nodes.size] do
      if let some a := (g.edges[i * g.nodes.size + k]?).getD none then
        for j in [:g.nodes.size] do
          if ((g.edges[i * g.nodes.size + j]?).getD none).isNone then
            if let some b := (g.edges[k * g.nodes.size + j]?).getD none then
              g := { g with edges := g.edges.set! (i * g.nodes.size + j) (some (.trans a b)) }
  return g

def Graph.step (mode : ModExpr → ModExpr → Bool) (graph : Graph) : Graph := Id.run do
  let mut g := graph.closeTransitive
  for a in g.nodes do
    for b in g.nodes do
      if (g.get a b).isNone then
        if let some h := structural mode g a b then g := g.add h
  return g

def saturate (mode : ModExpr → ModExpr → Bool) (left right : CompareTy) :
    Nat → Graph → RunResult (Option Certificate)
  | 0, _ => .exhausted
  | fuel + 1, g =>
    match g.get left right with
    | some h => .success (some h)
    | none =>
      let next := g.step mode
      if next.count == g.count then .success none
      else saturate mode left right fuel next

structure Result where
  shapes : ComparisonShapeSolver.Solved
  action : CompareSubstitution
  certificate : Certificate
  scalarEdges : List (ModExpr × ModExpr)
  query : BoolExpr
  backend : ConcreteBackend.Report
  deriving Repr

/-- Each body parameter has one variance and receives its corresponding floor
or ceiling. Inputs with written source bounds, quantified source modes, or a
parameter of mixed variance remain available to the other comparison phases. -/
def attempt (fuel : Nat) (p : SchemePreparation.Prepared) : RunResult (Option Result) := do
  if !p.sourceBounds.isEmpty || p.firstMode != p.nextMode then return none
  if !(List.range' p.firstType (p.nextType - p.firstType)).all (fun n =>
      positive (fun k => k == n) true p.sourceType ||
      positive (fun k => k == n) false p.sourceType) then return none
  let solved ← ComparisonShapeSolver.prepare fuel p
  let .solved shapes := solved | return none
  let σ := action p shapes
  let shape := wellShaped shapes.fixedShapes
  if !σ.types.all (fun entry => shape entry.2) then return none
  let vertices := nodes p σ
  let scalarEdges ← modeEdges fuel p.assumptions (modeLabels vertices)
  let mode := fun a b => scalarEdges.contains (a, b)
  let some certificate ← saturate mode (σ.ty p.sourceType) (.ofTy p.targetType) fuel
    (initialGraph p.assumptions vertices) | return none
  if !(certificate.left == σ.ty p.sourceType && certificate.right == .ofTy p.targetType &&
      certificate.check shape mode p.assumptions) then return none
  let goals := scalarEdges.map fun (a, b) => Constraint.mode a b
  let query := BoolExpr.imp (boundsModeFormula p.assumptions) (boundsModeFormula goals)
  let backend ← ConcreteBackend.decideFormula fuel query
  if !backend.valid then return none
  return some ⟨shapes, σ, certificate, scalarEdges, query, backend⟩

end ModalityInference.ComparisonPartialPropagation
