import ModalityInference.ModalSynthesis

/-! Uniform scalar synthesis with selector choices shared with type propagation.
The caller supplies the two component clause sets after allocating its global
selectors. Even atoms encode modality coordinates; odd atoms remain constant
selectors until the combined type-and-modality query is solved. -/
namespace ModalityInference.ComparisonJointModes

/-- Both scalar components retain the caller's selector namespace. -/
def prepare (side : Nat → Bool) (flex : List Nat) (locality other : CNF) :
    ModalSynthesis.Prepared :=
  ⟨SymbolicCNF.solve (ModalSynthesis.pivots side true flex) locality,
   SymbolicCNF.solve (ModalSynthesis.pivots side false flex) other⟩

end ModalityInference.ComparisonJointModes
