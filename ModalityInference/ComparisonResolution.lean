import ModalityInference.CompactCNF
import ModalityInference.CNFPropagation

/-! Incremental resolution retains unaffected clauses and minimizes only the
new resolvents. Callers may normalize their initial clauses once. -/
namespace ModalityInference.ComparisonResolution

def eliminate (clauses : CNF) (v : Nat) : CNF :=
  let lower := CNFPropagation.lower clauses v
  let upper := CNFPropagation.upper clauses v
  lower.foldr (fun l rest =>
    upper.foldr (fun u rest => CompactCNF.insert (CompactCNF.canonical (l ++ u)) rest) rest)
    (CNFPropagation.unaffected clauses v)

end ModalityInference.ComparisonResolution
