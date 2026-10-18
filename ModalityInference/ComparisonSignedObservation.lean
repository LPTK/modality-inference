import ModalityInference.ComparisonSignedEndpoints
import ModalityInference.ComparisonStructuralLayout

/-! Route-indexed endpoint observations over one finite structural layout.
All annotation formulas use the same modality substitution. Constructor choices
and fixed-head observations use the existing recursive layout namespaces. -/
namespace ModalityInference.ComparisonSignedObservation
open ComparisonSignedEndpoints ComparisonStructuralLayout ComparisonControls

def routeAtom : Route → Nat → Nat
  | [] => id
  | direction :: rest => (if direction then rightAtom else leftAtom) ∘ routeAtom rest

def nodeAt : Layout → Route → Option Layout
  | layout, [] => some layout
  | .leaf _ _, _ :: _ => none
  | .fork _ _ left right, direction :: rest => nodeAt (if direction then right else left) rest

def action (m : ModExpr) (value : Bool) : BoolExpr :=
  .any ([Coordinate.unaffected,.locality,.affinity,.uniqueness].map fun c =>
    .and (coordinateTest c) (c.modalWith modeAtom (.const value) m))

def context (layout : Layout) (modes : ModVar → ModExpr) : ComparisonSignedEndpoints.Context where
  fixed route a := match nodeAt layout route with
    | none => .const false
    | some node => .atom (routeAtom route (headAtom (node.basis.heads.idxOf (.ofTy a))))
  choose route := .atom (routeAtom route (choiceAtom 0))
  action route m :=
    (rename (routeAtom route) (action (m.subst modes) false),
     rename (routeAtom route) (action (m.subst modes) true))

end ModalityInference.ComparisonSignedObservation
