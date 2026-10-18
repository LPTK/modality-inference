import ModalityInference.ComparisonSignedPolynomials
import ModalityInference.ComparisonSignedCanonical

/-! Shared signed-graph synthesis over the input's finite image family. Keys
are encoded once; every image is reconstructed from the same canonical model
and retained parameter valuation. -/
namespace ModalityInference.ComparisonSignedSynthesis
open ComparisonPropagation ComparisonSignedRelations

structure Input where
  keys : List Nat
  bases : Nat → List CompareTy

def Input.key (input : Input) (name : Nat) : List Bool :=
  input.keys.map (fun k=>k==name)

def Input.payload (input : Input) : Nat :=
  input.keys.foldr (fun name rest=>max (input.bases name).length rest) 0

def Input.width (input : Input) : Nat := 1+input.keys.length+input.payload

def Input.polynomialEdges (input : Input) : CNF :=
  input.keys.foldr (fun name rest=>join
    (ComparisonSignedPolynomials.edges (input.key name) (input.bases name).length) rest) [[]]

def Input.edges (input : Input) (required : CNF) : CNF :=
  join required input.polynomialEdges

def Input.reached (input : Input) (required : CNF) : CNF :=
  closure input.width (input.edges required)

def Input.consistent (input : Input) (required : CNF) : CNF :=
  ComparisonSignedCanonical.consistent 0 (input.reached required)

def Input.assignment (input : Input) (required : CNF) : CNF :=
  ComparisonSignedCanonical.assignment input.width 0 (input.reached required)

def Input.reconstruct (input : Input) (required : CNF) (parameters : Nat → Bool) :
    Option (List (Nat × CompareTy)) :=
  input.keys.mapM fun name=>do
    let image ← ComparisonSignedPolynomials.reconstruct parameters (input.key name)
      (input.bases name) (input.assignment required)
    return (name,image)

end ModalityInference.ComparisonSignedSynthesis
