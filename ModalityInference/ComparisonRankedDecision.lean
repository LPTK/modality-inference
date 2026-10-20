import ModalityInference.ComparisonObserverMachineFormula
import ModalityInference.ComparisonObserverMachineEncoding
import ModalityInference.ComparisonSignedQuerySolver
import ModalityInference.ComparisonRankedBasis

/-! Signed endpoint compilation over a finite observer machine. Constructor
successors retain their own tags, and every occurrence of a quantified name
calls the same image family at its selected observer state. -/
namespace ModalityInference.ComparisonRankedDecision

open ComparisonSignedEndpoints ComparisonObserverMachineFormula
  ComparisonStructuralLayout

def call (name state : Nat) : Call := ⟨name, List.replicate state true⟩

def choice (test : BoolExpr) (left right : List Branch) : List Branch :=
  left.map (Branch.guarded test) ++ right.map (Branch.guarded (neg test))

def dual (branches : List Branch) : List Branch :=
  branches.map fun b => ⟨b.guard, b.view.dual⟩

def acted (branches : List Branch) (lower upper : BoolExpr) : List Branch :=
  branches.map fun b => ⟨b.guard, b.view.act lower upper⟩

def choices {α : Type} (fallback : α) (test : α → BoolExpr)
    (branches : α → List Branch) : List α → List Branch
  | [] => branches fallback
  | i :: rest => choice (test i) (branches i) (choices fallback test branches rest)

def next {count} (data : Fin count → Fields count) (i : Fin count)
    (kind : Constructor) (branches : Fin count → List Branch) : List Branch :=
  choices i ((data i).next kind) branches (List.finRange count)

def reference {count} (keys : List Nat) (types : List TypeVar)
    (data : Fin count → Fields count) (i : Fin count) (v : TypeVar) : Data :=
  match v with
  | .flex n => if keys.contains n then .image (call n i) true
      else .fixed (atom types (data i) v)
  | .rigid _ => .fixed (atom types (data i) v)

def observe {count} (keys : List Nat) (types : List TypeVar) (names : List ModVar)
    (data : Fin count → Fields count) (modes : ModVar → ModExpr) :
    Ty → Fin count → List Branch
  | .var v, i => [⟨.const true, .base (reference keys types data i v)⟩]
  | .unit, i => [⟨.const true, .base (.fixed (data i).unitValue)⟩]
  | .credit, i => [⟨.const true, .base (.fixed (data i).creditValue)⟩]
  | .prod a b, i => choice ((data i).left .prod)
      (next data i .prod (observe keys types names data modes a))
      (next data i .prod (observe keys types names data modes b))
  | .sum a b, i => choice ((data i).left .sum)
      (next data i .sum (observe keys types names data modes a))
      (next data i .sum (observe keys types names data modes b))
  | .fn a b, i => choice ((data i).left .fn)
      (dual (next data i .fn (observe keys types names data modes a)))
      (next data i .fn (observe keys types names data modes b))
  | .modal a m, i => acted (observe keys types names data modes a i)
      (action names (data i) (m.subst modes) (.const false))
      (action names (data i) (m.subst modes) (.const true))

def compile {count} (keys : List Nat) (types : List TypeVar) (names : List ModVar)
    (data : Fin count → Fields count) (modes : ModVar → ModExpr)
    (left right : Ty) (i : Fin count) : List ComparisonSignedEndpoints.Clause :=
  (observe keys types names data modes left i).flatMap fun l =>
    (observe keys types names data modes right i).flatMap fun r =>
      compare (.and l.guard r.guard) l.view r.view

def imageTypes (keys : List Nat) (images : Nat → CompareTy) : TypeVar → CompareTy
  | .flex n => if keys.contains n then images n else .var (.flex n)
  | .rigid n => .var (.rigid n)

def instantiate (keys : List Nat) (images : Nat → CompareTy)
    (modes : ModVar → ModExpr) (a : Ty) : CompareTy :=
  (CompareTy.ofTy a).subst (imageTypes keys images) modes

def mapFields {count} (f : BoolExpr → BoolExpr) (d : Fields count) : Fields count where
  atoms := d.atoms.map f
  modes := d.modes.map fun m => (f m.1, f m.2.1, f m.2.2)
  first := f d.first
  second := f d.second
  unitValue := f d.unitValue
  creditValue := f d.creditValue
  left := fun k => f (d.left k)
  next := fun k j => f (d.next k j)
  range := fun b => f (d.range b)

def machineData (types : List TypeVar) (names : List ModVar) (count : Nat)
    (i : Fin count) : Fields count :=
  mapFields (ComparisonStructuralLayout.rename (2 * ·))
    (ComparisonObserverMachineEncoding.allocate types.length names.length count i)

def payload (c : Call) (index : Nat) : Nat :=
  2 * Nat.pair c.name (Nat.pair c.route.length index) + 1

def payloadTheory {count} (input : ComparisonSignedSynthesis.Input)
    (types : List TypeVar) (names : List ModVar) (data : Fin count → Fields count) : BoolExpr :=
  .all (input.keys.flatMap fun name => (List.finRange count).flatMap fun i =>
    ((input.bases name).zipIdx).map fun (a, index) =>
      .equal (.atom (payload (call name i) index)) (value types names data a i))

def theory {count} (Δ : Bounds) (input : ComparisonSignedSynthesis.Input)
    (types : List TypeVar) (names : List ModVar) (data : Fin count → Fields count) : BoolExpr :=
  .and (query Δ types names data) (payloadTheory input types names data)

def clauses {count} (keys : List Nat) (types : List TypeVar) (names : List ModVar)
    (data : Fin count → Fields count) (modes : ModVar → ModExpr)
    (endpoints : List (Ty × Ty)) : List ComparisonSignedEndpoints.Clause :=
  endpoints.flatMap fun (a, b) => (List.finRange count).flatMap fun i =>
    compile keys types names data modes a b i

def endpointRank (endpoints : List (Ty × Ty)) : Nat :=
  (endpoints.map fun pair => max (ComparisonRankedBasis.rank (.ofTy pair.1))
    (ComparisonRankedBasis.rank (.ofTy pair.2))).foldr max 0

def selected (images : List (Nat × CompareTy)) (name : Nat) : CompareTy :=
  (images.lookup name).getD .unit

def prepare (fuel : Nat) (Δ : Bounds) (input : ComparisonSignedSynthesis.Input)
    (types : List TypeVar) (names : List ModVar) (count : Nat)
    (modes : ModVar → ModExpr) (endpoints : List (Ty × Ty)) :
    RunResult ComparisonSignedQueries.Query := do
  let data := machineData types names count
  let original ← CompactCNF.toCNF fuel true (theory Δ input types names data)
  let required ← compileGuards fuel (clauses input.keys types names data modes endpoints)
  return ⟨payload, Sum.inr, original, required⟩

/-- For one shared modality strategy and one finite image basis, solve the
original endpoint conditions simultaneously at every bounded observer state. -/
def run (fuel : Nat) (Δ : Bounds) (input : ComparisonSignedSynthesis.Input)
    (types : List TypeVar) (names : List ModVar) (count : Nat)
    (modes : ModVar → ModExpr) (endpoints : List (Ty × Ty)) :
    RunResult ComparisonSignedQuerySolver.Solution := do
  let q ← prepare fuel Δ input types names count modes endpoints
  ComparisonSignedQuerySolver.run fuel input [q] []

end ModalityInference.ComparisonRankedDecision
