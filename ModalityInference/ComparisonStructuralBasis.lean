import ModalityInference.ComparisonControls
import ModalityInference.ComparisonShapes

/-! Finite constructor and signed-control bases indexed by solved shapes.
The construction retains fixed names at their entire shapes. -/
namespace ModalityInference.ComparisonStructuralBasis

open ComparisonControls

def extend (modes : List ModVar) : List CompareTy → List CompareTy
  | [] => []
  | a :: rest => (Basis.mk a rest modes).types

def fixedHeads (names : List TypeVar) (shapes : TypeVar → ComparisonShape)
    (s : ComparisonShape) : List CompareTy :=
  (names.filter (fun v => shapes v == s)).map CompareTy.var

def pairs (op : CompareTy → CompareTy → CompareTy)
    (left right : List CompareTy) : List CompareTy :=
  left.flatMap fun a => right.map (op a)

def heads (names : List TypeVar) (modes : List ModVar) (shapes : TypeVar → ComparisonShape) :
    ComparisonShape → List CompareTy
  | s@(.var _) => fixedHeads names shapes s
  | .unit => fixedHeads names shapes .unit ++ [.unit]
  | .credit => fixedHeads names shapes .credit ++ [.credit]
  | .prod s t => fixedHeads names shapes (.prod s t) ++
      pairs .prod (extend modes (heads names modes shapes s)) (extend modes (heads names modes shapes t))
  | .sum s t => fixedHeads names shapes (.sum s t) ++
      pairs .sum (extend modes (heads names modes shapes s)) (extend modes (heads names modes shapes t))
  | .fn s t => fixedHeads names shapes (.fn s t) ++
      pairs .fn (extend modes (heads names modes shapes s)) (extend modes (heads names modes shapes t))

def basis (names : List TypeVar) (modes : List ModVar) (shapes : TypeVar → ComparisonShape)
    (s : ComparisonShape) : Option Basis :=
  match heads names modes shapes s with
  | [] => none
  | a :: rest => some ⟨a, rest, modes⟩

end ModalityInference.ComparisonStructuralBasis
