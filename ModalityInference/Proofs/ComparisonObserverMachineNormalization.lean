import ModalityInference.ComparisonObserverMachineEncoding

/-! Normalization is exact when the machine arrays already have the requested
lengths. -/
namespace ModalityInference.ComparisonObserverMachineEncoding

private theorem map_getD_range {α : Type*} (xs : List α) (fallback : α) :
    (List.range xs.length).map (fun i => xs[i]?.getD fallback) = xs := by
  apply List.ext_getElem (by simp)
  exact fun i _ hi => by simp [hi]

theorem normalize_eq_of_lengths {count : Nat} (typeCount modeCount : Nat) (d : Description count)
    (ht : d.atoms.length = typeCount) (hm : d.modes.length = modeCount) :
    normalize typeCount modeCount d = d := by
  simp only [normalize, ← ht, ← hm, map_getD_range]

end ModalityInference.ComparisonObserverMachineEncoding
