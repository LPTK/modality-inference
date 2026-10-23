import ModalityInference.ComparisonControls

/-! Finite row tables and their executable Boolean extensions. A certificate
supplies the observation list and the Boolean order on control indices. -/
namespace ModalityInference.ComparisonExecutableTables

structure Row (M A : Type*) where
  index : M
  left : A
  right : A
  result : A
  deriving DecidableEq, Repr

def allRows {M A : Type*} (indices : List M) (tags : List A) : List (Row M A) :=
  indices.flatMap fun m => tags.flatMap fun a => tags.flatMap fun b =>
    tags.map fun c => ⟨m,a,b,c⟩

def below {O : Type*} (observations : List O) (x y : O → Bool) : Bool :=
  observations.all fun o => !x o || y o

def direction {O : Type*} (observations : List O) (reverse : Bool) (x y : O → Bool) : Bool :=
  if reverse then below observations y x else below observations x y

def compatible {M A O : Type*} (observations : List O) (embed : A → O → Bool)
    (le : M → M → Bool) (p q : Bool) (a b : Row M A) : Bool :=
  !(le a.index b.index && direction observations p (embed a.left) (embed b.left) &&
    direction observations q (embed a.right) (embed b.right)) ||
    below observations (embed a.result) (embed b.result)

def check {M A O : Type*} (observations : List O) (embed : A → O → Bool)
    (le : M → M → Bool) (p q : Bool) (rows : List (Row M A)) : Bool :=
  rows.all fun a => rows.all fun b => compatible observations embed le p q a b

def extend {M A O : Type*} (observations : List O) (embed : A → O → Bool)
    (le : M → M → Bool) (p q : Bool) (rows : List (Row M A))
    (m : M) (x y : O → Bool) : O → Bool := fun o =>
  rows.any fun r => le r.index m && direction observations p (embed r.left) x &&
    direction observations q (embed r.right) y && embed r.result o

end ModalityInference.ComparisonExecutableTables
