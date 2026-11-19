import ModalityInference.ComparisonFiniteCertificateFormula
import ModalityInference.ComparisonFiniteCertificateDense
import ModalityInference.ComparisonObserverBitsCode
import ModalityInference.ComparisonRankedDecision
import Mathlib.Data.List.OfFn

/-! A disjoint Boolean address layout for every field of a finite comparison
certificate. Only dimensions and input-derived name/key lists are fixed. -/
namespace ModalityInference.ComparisonFiniteCertificateFormulaEncoding

open ComparisonFiniteCertificate ComparisonFiniteCertificateFormula
  ComparisonFiniteControlEncoding ComparisonExecutableTables

def address (family payload : Nat) : Nat := Nat.pair family payload

def rowAddress {Δ names tags} (r : Row (Code Δ names) (Fin tags)) : Nat :=
  Nat.pair r.index.index.val (Nat.pair r.left.val (Nat.pair r.right.val r.result.val))

def vectorAddress {Δ names observations} (m : Code Δ names) (o : Fin observations) : Nat :=
  Nat.pair m.index.val o.val

def readPair {left right : Nat} (value : Fin left → Fin right → Bool) (u : Nat) : Bool :=
  if hl : (Nat.unpair u).1 < left then
    if hr : (Nat.unpair u).2 < right then value ⟨_,hl⟩ ⟨_,hr⟩ else false
  else false

def readRow {Δ names tags} (value : Row (Code Δ names) (Fin tags) → Bool) (u : Nat) : Bool :=
  let m := (Nat.unpair u).1
  let a := (Nat.unpair (Nat.unpair u).2).1
  let b := (Nat.unpair (Nat.unpair (Nat.unpair u).2).2).1
  let c := (Nat.unpair (Nat.unpair (Nat.unpair u).2).2).2
  if hm : m < (labels Δ names).length then
    if ha : a < tags then
      if hb : b < tags then
        if hc : c < tags then value ⟨⟨⟨m,hm⟩⟩,⟨a,ha⟩,⟨b,hb⟩,⟨c,hc⟩⟩ else false
      else false
    else false
  else false

def readVector {Δ names observations} (value : Coordinates Δ names observations) : Nat → Bool :=
  readPair fun m o => value ⟨m⟩ o

def readLiteral {Δ names tags} (keys : List ModExpr)
    (value : ModExpr → List (Row (Code Δ names) (Fin tags))) (u : Nat) : Bool :=
  match keys[(Nat.unpair u).1]? with
  | none => false
  | some p => readRow (fun r => decide (r ∈ value p)) (Nat.unpair u).2

def readFrozen {Δ names observations} (keys : List CompareTy)
    (value : CompareTy → Coordinates Δ names observations) (u : Nat) : Bool :=
  match keys[(Nat.unpair u).1]? with
  | none => false
  | some a => readVector (value a) (Nat.unpair u).2

def selection {Δ names tags} (family : Nat) : Selection Δ names tags :=
  fun r => .atom (address family (rowAddress r))

def literal {Δ names tags} (family position : Nat) : Selection Δ names tags :=
  fun r => .atom (address family (Nat.pair position (rowAddress r)))

def vector {Δ names observations} (family position : Nat) : Vector Δ names observations :=
  fun m o => .atom (address family (Nat.pair position (vectorAddress m o)))

def allocate (Δ : Bounds) (names : List ModVar) (queries : List CompareTy)
    (states tags observations : Nat) : Fields Δ names states tags observations where
  machine i := ComparisonRankedDecision.mapFields (ComparisonStructuralLayout.rename (address 0))
    (ComparisonObserverMachineEncoding.allocate (inputTypes Δ queries).length names.length states i)
  embed a o := .atom (address 1 (Nat.pair a.val o.val))
  prodRows := selection 2
  sumRows := selection 3
  fnRows := selection 4
  prodLiterals := List.ofFn fun i : Fin (retainedPrefixes Δ queries).length =>
    ((retainedPrefixes Δ queries)[i],literal 5 i.val)
  sumLiterals := List.ofFn fun i : Fin (retainedPrefixes Δ queries).length =>
    ((retainedPrefixes Δ queries)[i],literal 6 i.val)
  frozen := List.ofFn fun i : Fin (retainedFrozen Δ queries).length =>
    ((retainedFrozen Δ queries)[i],vector 7 i.val)
  defined x := vector 8 (ComparisonObserverBitsCode.bitsCode x)

def encode {Δ names} (C : Candidate Δ names) (queries : List CompareTy) (u : Nat) : Bool :=
  let family := (Nat.unpair u).1
  let payload := (Nat.unpair u).2
  match family with
  | 0 => ComparisonObserverMachineEncoding.encode C.machine payload
  | 1 => readPair C.embed payload
  | 2 => readRow (fun r => decide (r ∈ C.prodRows)) payload
  | 3 => readRow (fun r => decide (r ∈ C.sumRows)) payload
  | 4 => readRow (fun r => decide (r ∈ C.fnRows)) payload
  | 5 => readLiteral (retainedPrefixes Δ queries) (fun p => C.prodAt (some p)) payload
  | 6 => readLiteral (retainedPrefixes Δ queries) (fun p => C.sumAt (some p)) payload
  | 7 => readFrozen (retainedFrozen Δ queries) C.data.frozenValue payload
  | 8 => readVector (C.defined (ComparisonObserverBitsCode.decodeBits C.states
      (Nat.unpair payload).1)) (Nat.unpair payload).2
  | _ => false

def query (Δ : Bounds) (names : List ModVar) (queries : List CompareTy)
    (states tags observations : Nat) (a b : CompareTy) : BoolExpr :=
  (allocate Δ names queries states tags observations).separates (inputTypes Δ queries) names a b

end ModalityInference.ComparisonFiniteCertificateFormulaEncoding
