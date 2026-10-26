import ModalityInference.ComparisonExecutableControls
import ModalityInference.ComparisonExecutableRangeAgreement
import ModalityInference.ComparisonExecutableSyntax

/-! Finite data and executable validation for mixed-context comparison
certificates. The inner machine checks scalar and shape assumptions; original
raw subtype assumptions are checked in the outer coordinate interpreter. -/
namespace ModalityInference.ComparisonFiniteCertificate

open ComparisonFiniteControlEncoding ComparisonObserverMachineCheck
  ComparisonExecutableTables ComparisonExecutableAgreement

abbrev Coordinates (Δ : Bounds) (names : List ModVar) (observations : Nat) :=
  Code Δ names → Fin observations → Bool

structure Candidate (Δ : Bounds) (names : List ModVar) where
  states : Nat
  tags : Nat
  observations : Nat
  types : List TypeVar
  modes : List ModVar
  machine : Fin states → Description (Fin states)
  embed : Fin tags → Fin observations → Bool
  prodRows : List (Row (Code Δ names) (Fin tags))
  sumRows : List (Row (Code Δ names) (Fin tags))
  fnRows : List (Row (Code Δ names) (Fin tags))
  prodLiterals : List (ModExpr × List (Row (Code Δ names) (Fin tags)))
  sumLiterals : List (ModExpr × List (Row (Code Δ names) (Fin tags)))
  frozen : List (CompareTy × Coordinates Δ names observations)
  defined : ComparisonObserverRangeEncoding.Bits states → Coordinates Δ names observations

def indices (Δ : Bounds) (names : List ModVar) : List (Code Δ names) :=
  (List.finRange (labels Δ names).length).map Code.mk

def shadow (Δ : Bounds) : Bounds := Δ.map fun c => match c with
  | .sub a b => .equiv a b
  | c => c

def literalRows {M A : Type*} (ordinary : List (Row M A))
    (literals : List (ModExpr × List (Row M A))) : Option ModExpr → List (Row M A)
  | none => ordinary
  | some p => ((literals.find? (fun row => decide (row.1 = p))).map Prod.snd).getD []

namespace Candidate

variable {Δ : Bounds} {names : List ModVar} (C : Candidate Δ names)

def obs := List.finRange C.observations

def prodAt (p : Option ModExpr) := literalRows C.prodRows C.prodLiterals p

def sumAt (p : Option ModExpr) := literalRows C.sumRows C.sumLiterals p

def pair (rows : List (Row (Code Δ names) (Fin C.tags)))
    (x y : Coordinates Δ names C.observations) : Coordinates Δ names C.observations := fun m =>
  extend C.obs C.embed order false false rows m (x m) (y m)

def function (x y : Coordinates Δ names C.observations) : Coordinates Δ names C.observations := fun m =>
  extend C.obs C.embed ComparisonExecutableControls.future true false C.fnRows m (x 1) (y 1)

def operations := ComparisonExecutableRangeAgreement.rawOperations C.machine C.modes
  order (· * ·) expression (C.pair C.prodRows) (C.pair C.sumRows) C.function

def data : ComparisonExecutableSyntax.Data (Code Δ names) (Coordinates Δ names C.observations) where
  total := ScalarDecision.defined Δ
  control := project Δ names
  shift m x n := x (m * n)
  prod p := C.pair (C.prodAt p)
  sum p := C.pair (C.sumAt p)
  fn := C.function
  join x y m o := x m o || y m o
  meet x y m o := x m o && y m o
  atom v := C.defined (ComparisonObserverRangeEncoding.atom C.machine C.types v)
  unit := C.defined (ComparisonObserverRangeEncoding.unit C.machine)
  credit := C.defined (ComparisonObserverRangeEncoding.credit C.machine)
  bottom _ _ := false
  frozen := C.frozen

def monotoneCheck (x : Coordinates Δ names C.observations) : Bool :=
  (indices Δ names).all fun m => (indices Δ names).all fun n =>
    !order m n || below C.obs (x m) (x n)

def tablesCheck : Bool :=
  ComparisonExecutableTables.check C.obs C.embed order false false C.prodRows &&
  ComparisonExecutableTables.check C.obs C.embed order false false C.sumRows &&
  ComparisonExecutableTables.check C.obs C.embed ComparisonExecutableControls.future true false C.fnRows &&
  C.prodLiterals.all (fun row => ComparisonExecutableTables.check C.obs C.embed order false false row.2) &&
  C.sumLiterals.all (fun row => ComparisonExecutableTables.check C.obs C.embed order false false row.2)

def embeddingCheck : Bool :=
  ComparisonExecutableAgreement.check (ComparisonObserverRangeEncoding.vectors C.machine)
    (indices Δ names) C.obs C.operations C.defined

def structureCheck : Bool :=
  decide (Δ.modVars ⊆ names.toFinset) &&
  ComparisonObserverMachineCheck.check (shadow Δ) C.types C.modes C.machine &&
  C.tablesCheck && C.embeddingCheck && C.frozen.all (fun row => C.monotoneCheck row.2)

def boundsCheck : Bool := Δ.all fun c => match c with
  | .sub a b => vectorBelow (indices Δ names) C.obs (C.data.evalRaw a) (C.data.evalRaw b)
  | _ => true

def check : Bool := C.structureCheck && C.boundsCheck

def separates (a b : CompareTy) : Bool :=
  C.check && !vectorBelow (indices Δ names) C.obs (C.data.eval a none) (C.data.eval b none)

end Candidate
end ModalityInference.ComparisonFiniteCertificate
