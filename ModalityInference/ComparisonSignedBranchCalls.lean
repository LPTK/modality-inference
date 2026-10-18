import ModalityInference.ComparisonSignedBranchImages
import ModalityInference.ComparisonSignedObservation

/-! Calls retain their observer route while resolving the source binder to the
fixed key of that route's structural basis. No shape valuation is enumerated. -/
namespace ModalityInference.ComparisonSignedBranchCalls
open ComparisonSignedEndpoints ComparisonSignedBranchImages ComparisonSignedObservation

def resolve (table : List Entry) (layout : ComparisonStructuralLayout.Layout)
    (call : Call) : Option Call := do
  let node ← nodeAt layout call.route
  let key ← locate call.name node.shape table
  return ⟨key,call.route⟩

def clause (table : List Entry) (layout : ComparisonStructuralLayout.Layout)
    (source : CompiledClause) : Option CompiledClause := do
  let literals ← source.literals.mapM fun (call,sign)=>do
    return (←resolve table layout call,sign)
  return ⟨source.guard,literals⟩

def compile (table : List Entry) (layout : ComparisonStructuralLayout.Layout)
    (sources : List CompiledClause) : Option (List CompiledClause) :=
  sources.mapM (clause table layout)

end ModalityInference.ComparisonSignedBranchCalls
