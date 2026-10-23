import ModalityInference.ComparisonControls

/-! Finite reference families of total controls. These syntax generators are
available to certificate code without importing the semantic proof modules.
Scalar decisions continue to use symbolic Boolean elimination. -/
namespace ModalityInference.ComparisonControlForms

open ComparisonControls

def channelMode : Channel → Bool → Mode
  | .lower, b => ⟨true,true,!b⟩
  | .locality, b => ⟨b,true,true⟩
  | .affinity, b => ⟨true,b,true⟩

def signedAtom (c : Channel) (i : Nat) (positive : Bool) : ModExpr :=
  match atomControl c i positive with
  | some q => q.expression
  | none => .const (channelMode c false)

def band (c : Channel) : BoolExpr → Bool → ModExpr
  | .const b, p => .const (channelMode c (b == p))
  | .atom i, p => signedAtom c i p
  | .and a b, true => .meet (band c a true) (band c b true)
  | .and a b, false => .join (band c a false) (band c b false)
  | .or a b, true => .join (band c a true) (band c b true)
  | .or a b, false => .meet (band c a false) (band c b false)
  | .imp a b, true => .join (band c a false) (band c b true)
  | .imp a b, false => .meet (band c a true) (band c b false)

def branch (i : Nat) (yes no : BoolExpr) : BoolExpr :=
  .or (.and (.atom i) yes) (.and (.imp (.atom i) (.const false)) no)

def truthForms : List Nat → List BoolExpr
  | [] => [.const false,.const true]
  | i :: is => (truthForms is).flatMap fun yes =>
      (truthForms is).map fun no => branch i yes no

def channelAtoms : Channel → List ModVar → List Nat
  | .locality, names => names.map (fun v => v.atomIndex 0)
  | .affinity, names | .lower, names =>
      names.flatMap (fun v => [v.atomIndex 1,v.atomIndex 2])

def combine (localPart affine unique : BoolExpr) : ModExpr :=
  .compose (band .locality localPart true)
    (.compose (band .affinity affine true) (band .lower unique false))

def representatives (names : List ModVar) : List ModExpr :=
  (truthForms (channelAtoms .locality names)).flatMap fun localPart =>
    (truthForms (channelAtoms .affinity names)).flatMap fun affine =>
      (truthForms (channelAtoms .lower names)).map fun unique => combine localPart affine unique

end ModalityInference.ComparisonControlForms
