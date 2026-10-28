import ModalityInference.ComparisonFiniteCertificate
import ModalityInference.ComparisonExecutableAgreementFormula
import ModalityInference.ComparisonObserverRangeFormula

/-! Symbolic validation of a finite comparison certificate. Dimensions and
syntax keys are fixed; Boolean field choices remain symbolic throughout. -/
namespace ModalityInference.ComparisonFiniteCertificateFormula

open ComparisonFiniteCertificate ComparisonFiniteControlEncoding ComparisonExecutableTables

abbrev Vector (Δ : Bounds) (names : List ModVar) (observations : Nat) :=
  ComparisonExecutableAgreementFormula.Vector (Code Δ names) (Fin observations)

abbrev Selection (Δ : Bounds) (names : List ModVar) (tags : Nat) :=
  Row (Code Δ names) (Fin tags) → BoolExpr

structure Fields (Δ : Bounds) (names : List ModVar) (states tags observations : Nat) where
  machine : Fin states → ComparisonObserverMachineFormula.Fields states
  embed : Fin tags → Fin observations → BoolExpr
  prodRows : Selection Δ names tags
  sumRows : Selection Δ names tags
  fnRows : Selection Δ names tags
  prodLiterals : List (ModExpr × Selection Δ names tags)
  sumLiterals : List (ModExpr × Selection Δ names tags)
  frozen : List (CompareTy × Vector Δ names observations)
  defined : ComparisonObserverRangeEncoding.Bits states → Vector Δ names observations

def rows (Δ : Bounds) (names : List ModVar) (tags : Nat) : List (Row (Code Δ names) (Fin tags)) :=
  allRows (indices Δ names) (List.finRange tags)

def literalSelection {Δ names tags} (ordinary : Selection Δ names tags)
    (literals : List (ModExpr × Selection Δ names tags)) : Option ModExpr → Selection Δ names tags
  | none => ordinary
  | some p => ((literals.find? (fun row => decide (row.1 = p))).map Prod.snd).getD (fun _ => .const false)

namespace Fields

variable {Δ : Bounds} {names : List ModVar} {states tags observations : Nat}
  (F : Fields Δ names states tags observations)

def decode (types : List TypeVar) (modes : List ModVar) (world : Nat → Bool) : Candidate Δ names where
  states := states
  tags := tags
  observations := observations
  types := types
  modes := modes
  machine := ComparisonObserverMachineFormula.decode F.machine world
  embed a o := (F.embed a o).eval world
  prodRows := ComparisonExecutableTableFormula.selected (rows Δ names tags) F.prodRows world
  sumRows := ComparisonExecutableTableFormula.selected (rows Δ names tags) F.sumRows world
  fnRows := ComparisonExecutableTableFormula.selected (rows Δ names tags) F.fnRows world
  prodLiterals := F.prodLiterals.map fun r =>
    (r.1,ComparisonExecutableTableFormula.selected (rows Δ names tags) r.2 world)
  sumLiterals := F.sumLiterals.map fun r =>
    (r.1,ComparisonExecutableTableFormula.selected (rows Δ names tags) r.2 world)
  frozen := F.frozen.map fun r => (r.1,ComparisonExecutableAgreementFormula.decode world r.2)
  defined x := ComparisonExecutableAgreementFormula.decode world (F.defined x)

def definedAt (x : ComparisonObserverRangeFormula.Bits states) : Vector Δ names observations :=
  fun m o => ComparisonObserverRangeFormula.lookup (fun v => F.defined v m o) x

def pair (selected : Selection Δ names tags)
    (x y : Vector Δ names observations) : Vector Δ names observations := fun m =>
  ComparisonExecutableTableFormula.extend (List.finRange observations) F.embed order false false
    (rows Δ names tags) selected m (x m) (y m)

def function (x y : Vector Δ names observations) : Vector Δ names observations := fun m =>
  ComparisonExecutableTableFormula.extend (List.finRange observations) F.embed
    ComparisonExecutableControls.future true false (rows Δ names tags) F.fnRows m (x 1) (y 1)

def images (modes : List ModVar) :
    ComparisonExecutableAgreementFormula.Images (ComparisonObserverRangeEncoding.Bits states)
      (Code Δ names) (Fin observations) where
  domainLe x y := .const (ComparisonObserverRangeEncoding.le x y)
  join x y := F.defined (ComparisonObserverRangeEncoding.join x y)
  meet x y := F.defined (ComparisonObserverRangeEncoding.meet x y)
  action m x := F.definedAt (ComparisonObserverRangeFormula.modal F.machine modes (expression m)
    (fun i => .const (x i)))
  prod x y := F.definedAt (ComparisonObserverRangeFormula.op F.machine .prod
    (fun i => .const (x i)) (fun i => .const (y i)))
  sum x y := F.definedAt (ComparisonObserverRangeFormula.op F.machine .sum
    (fun i => .const (x i)) (fun i => .const (y i)))
  fn x y := F.definedAt (ComparisonObserverRangeFormula.op F.machine .fn
    (fun i => .const (x i)) (fun i => .const (y i)))
  vectorProd := F.pair F.prodRows
  vectorSum := F.pair F.sumRows
  vectorFn := F.function

def data (types : List TypeVar) :
    ComparisonExecutableSyntax.Data (Code Δ names) (Vector Δ names observations) where
  total := ScalarDecision.defined Δ
  control := project Δ names
  shift m x n := x (m * n)
  prod p := F.pair (literalSelection F.prodRows F.prodLiterals p)
  sum p := F.pair (literalSelection F.sumRows F.sumLiterals p)
  fn := F.function
  join x y m o := .or (x m o) (y m o)
  meet x y m o := .and (x m o) (y m o)
  atom v := F.definedAt (ComparisonObserverRangeFormula.atom F.machine types v)
  unit := F.definedAt (ComparisonObserverRangeFormula.unit F.machine)
  credit := F.definedAt (ComparisonObserverRangeFormula.credit F.machine)
  bottom _ _ := .const false
  frozen := F.frozen

def monotoneCheck (x : Vector Δ names observations) : BoolExpr :=
  .all ((indices Δ names).map fun m => .all ((indices Δ names).map fun n =>
    .imp (.const (order m n)) (ComparisonExecutableTableFormula.below (List.finRange observations) (x m) (x n))))

def tableCheck (le : Code Δ names → Code Δ names → Bool) (p q : Bool)
    (selected : Selection Δ names tags) : BoolExpr :=
  ComparisonExecutableTableFormula.check (List.finRange observations) F.embed le p q
    (rows Δ names tags) selected

def tablesCheck : BoolExpr :=
  .and (.and (.and (.and (F.tableCheck order false false F.prodRows)
    (F.tableCheck order false false F.sumRows))
    (F.tableCheck ComparisonExecutableControls.future true false F.fnRows))
    (.all (F.prodLiterals.map fun r => F.tableCheck order false false r.2)))
    (.all (F.sumLiterals.map fun r => F.tableCheck order false false r.2))

def embeddingCheck (modes : List ModVar) : BoolExpr :=
  ComparisonExecutableAgreementFormula.check (ComparisonObserverRangeEncoding.allBits states)
    (indices Δ names) (List.finRange observations)
    (fun x => ComparisonObserverRangeFormula.admitted F.machine (fun i => .const (x i)))
    order (· * ·) (F.images modes) F.defined

def structureCheck (types : List TypeVar) (modes : List ModVar) : BoolExpr :=
  .and (.and (.and (.and (.const (decide (Δ.modVars ⊆ names.toFinset)))
    (ComparisonObserverMachineFormula.query (shadow Δ) types modes F.machine)) F.tablesCheck)
    (F.embeddingCheck modes)) (.all (F.frozen.map fun r => monotoneCheck r.2))

def boundsCheck (types : List TypeVar) : BoolExpr := .all (Δ.map fun c => match c with
  | .sub a b => ComparisonExecutableAgreementFormula.vectorBelow (indices Δ names)
      (List.finRange observations) ((F.data types).evalRaw a) ((F.data types).evalRaw b)
  | _ => .const true)

def check (types : List TypeVar) (modes : List ModVar) : BoolExpr :=
  .and (F.structureCheck types modes) (F.boundsCheck types)

def separates (types : List TypeVar) (modes : List ModVar) (a b : CompareTy) : BoolExpr :=
  .and (F.check types modes) (.imp (ComparisonExecutableAgreementFormula.vectorBelow
    (indices Δ names) (List.finRange observations) ((F.data types).eval a none) ((F.data types).eval b none))
      (.const false))

end Fields
end ModalityInference.ComparisonFiniteCertificateFormula
