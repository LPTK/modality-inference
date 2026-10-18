import ModalityInference.ComparisonControls

/-! Direct compilation of lattice syntax over an explicit finite basis.
Repeated basis terms share their first index; clause operations retain their
symbolic representation throughout. -/
namespace ModalityInference.ComparisonLatticeCompiler

open ComparisonControls

def compile (b : Basis) (t : CompareTy) : Option CNF :=
  if b.types.contains t then some [[(b.types.idxOf t, true)]]
  else match t with
    | .join a c => do
        return ComparisonPropagation.join (← compile b a) (← compile b c)
    | .meet a c => do
        return ComparisonPropagation.meet (← compile b a) (← compile b c)
    | _ => none

end ModalityInference.ComparisonLatticeCompiler
