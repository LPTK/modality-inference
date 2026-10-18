import ModalityInference.ComparisonStructuralBasis

/-! Finite constructor-and-control generator levels. A level contains lattice
polynomials over finitely many generators; it does not enumerate those
polynomials. Constructor height increases the level, while lattice operations
and guarded modal actions stay within a level. -/
namespace ModalityInference.ComparisonRankedBasis

open ComparisonControls ComparisonStructuralBasis

def basis (names : List TypeVar) (modes : List ModVar) : Nat → Basis
  | 0 => ⟨.unit, .credit :: names.map CompareTy.var, modes⟩
  | n+1 =>
      let previous := (basis names modes n).types
      ⟨.unit, previous ++ pairs .prod previous previous ++
        pairs .sum previous previous ++ pairs .fn previous previous, modes⟩

def rank : CompareTy → Nat
  | .var _ | .unit | .credit => 0
  | .prod a b | .sum a b | .fn a b => max (rank a) (rank b) + 1
  | .join a b | .meet a b => max (rank a) (rank b)
  | .modal a _ => rank a

end ModalityInference.ComparisonRankedBasis
