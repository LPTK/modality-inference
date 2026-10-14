import ModalityInference.ModalSynthesis

/-! Uniform expression synthesis differs from independent Boolean choices:
locality expressions cannot inspect affinity or uniqueness parameters. -/
namespace ModalityInference.ModalSynthesisRegression

def freshCoordinates : List Nat := [0, 1, 2]

-- A constant local witness satisfies a demand from an independent coordinate.
#guard (ModalSynthesis.synthesize 200 freshCoordinates
  (.imp (.atom 4) (.atom 0))).isSuccess

-- Pointwise Boolean witnesses exist, but no locality expression can track this
-- unconstrained rigid affinity coordinate uniformly.
#guard match ModalSynthesis.synthesize 200 freshCoordinates
    (.equal (.atom 0) (.atom 4)) with
  | .rejected _ => true
  | _ => false

-- A same-axis dependency reifies to an actual total modality expression.
#guard match ModalSynthesis.synthesize 200 freshCoordinates
    (.equal (.atom 0) (.atom 3)) with
  | .success result => match result.mode (.flex 0) with
    | some m => Mode.all.all fun rigid =>
      match m.eval (fun _ => some rigid) with
      | some actual => actual.isLocal == rigid.isLocal
      | none => false
    | none => false
  | _ => false

#guard (ModalSynthesis.synthesize 200 freshCoordinates
  (.or (.atom 0) (.atom 1))).isSuccess

-- Rigid assumptions are part of the query before uniform elimination.
#guard (ModalSynthesis.synthesize 200 freshCoordinates
  (.imp (.equal (.atom 3) (.atom 4)) (.equal (.atom 0) (.atom 4)))).isSuccess

-- Unused coordinates are eliminated as well, so no selected name leaks.
#guard match ModalSynthesis.synthesize 200 freshCoordinates (.const true) with
  | .success result => match result.mode (.flex 0) with
    | some m => m.freeVariables.isEmpty
    | none => false
  | _ => false

#guard match ModalSynthesis.synthesize 0 freshCoordinates (.const true) with
  | .exhausted => true
  | _ => false

end ModalityInference.ModalSynthesisRegression
