import ModalityInference.ComparisonObserverRangeEncoding

/-! Reindex a finite observer description on chosen type and mode names.
The Boolean coordinates, constructor edges, and admitted ranges are retained. -/
namespace ModalityInference.ComparisonObserverMachineRestriction

open ComparisonObserverMachineCheck

def restrict {State : Type} (types : List TypeVar) (modes : List ModVar)
    (types' : List TypeVar) (modes' : List ModVar) (d : Description State) : Description State where
  atoms := types'.map (atomValue types d)
  modes := modes'.map (modeValue modes d)
  coordinate := d.coordinate
  unitValue := d.unitValue
  creditValue := d.creditValue
  branch := d.branch
  range := d.range

end ModalityInference.ComparisonObserverMachineRestriction
