import ModalityInference.ComparisonTypes
import ModalityInference.SchemePreparation

/-! Comparison uses the same scope-preserving source freshening and target
skolemization as ordinary scheme preparation. Only reconstructed type images
use the internal comparison language. -/
namespace ModalityInference.ComparisonPreparation

abbrev Prepared := SchemePreparation.Prepared
abbrev prepare := SchemePreparation.prepare

def reconstruct (p : Prepared) (action : CompareSubstitution) : CompareSubstitution :=
  { types := p.sourceRenaming.types.map fun (n, a) => (n, action.ty a)
    modes := p.sourceRenaming.modes.map fun (n, m) => (n, m.subst action.mode) }

end ModalityInference.ComparisonPreparation
