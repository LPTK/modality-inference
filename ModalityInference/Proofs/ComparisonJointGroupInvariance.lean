import ModalityInference.Proofs.ComparisonJointGroup

/-! State-coordinate independence and finite input support of actual group compilation. -/
namespace ModalityInference.ComparisonJointGroup

open ComparisonPropagation ComparisonControls

theorem leafValue_congr {heads : List TypeVar} {names : List Nat} {c : Coordinate}
    {parameters : Nat → Bool} {left right : Fin (4 * names.length) → Bool}
    (h : ∀ i, left (state c i) = right (state c i)) (v : TypeVar) :
    leafValue heads names c parameters left v = leafValue heads names c parameters right v := by
  cases v with
  | rigid n => rfl
  | flex n =>
    cases hi : index names n <;> simp [leafValue, hi, h]

theorem atomValue_congr {heads : List TypeVar} {names : List Nat} {c : Coordinate}
    {parameters : Nat → Bool} {left right : Fin (4 * names.length) → Bool}
    (h : ∀ i, left (state c i) = right (state c i)) (a : ComparisonGroups.Atom) :
    atomValue heads names c parameters left a = atomValue heads names c parameters right a := by
  simp only [atomValue, leafValue_congr h]

theorem coordinateHolds_congr {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {c : Coordinate} {parameters : Nat → Bool} {left right : Fin (4 * g.leaves.length) → Bool}
    (h : ∀ i, left (state c i) = right (state c i)) :
    CoordinateHolds assumptions required g c parameters left ↔
      CoordinateHolds assumptions required g c parameters right := by
  simp only [CoordinateHolds, atomValue_congr h]

theorem coordinate_congr {fuel : Nat} {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {c : Coordinate} {result : CNF} (hc : coordinate fuel assumptions required g c = .success result)
    {parameters : Nat → Bool} {left right : Fin (4 * g.leaves.length) → Bool}
    (h : ∀ i, left (state c i) = right (state c i)) :
    CNFHolds (ComparisonJointEncoding.valuation left parameters) result ↔
      CNFHolds (ComparisonJointEncoding.valuation right parameters) result := by
  rw [coordinate_correct hc, coordinate_correct hc]
  exact coordinateHolds_congr h

theorem sandwich_congr {a b : Coordinate} {parameters : Nat → Bool}
    {left right : Fin (4 * count) → Bool}
    (ha : ∀ i, left (state a i) = right (state a i))
    (hb : ∀ i, left (state b i) = right (state b i)) :
    CNFHolds (ComparisonJointEncoding.valuation left parameters) (sandwich a b count) ↔
      CNFHolds (ComparisonJointEncoding.valuation right parameters) (sandwich a b count) := by
  simp only [sandwich_correct, ha, hb]

theorem prepare_coordinates {fuel : Nat} {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {result : Input} (h : prepare fuel assumptions required g = .success result) :
    ∃ locality affinity uniqueness,
      coordinate fuel assumptions required g .unaffected = .success result.nominal ∧
      coordinate fuel assumptions required g .locality = .success locality ∧
      coordinate fuel assumptions required g .affinity = .success affinity ∧
      coordinate fuel assumptions required g .uniqueness = .success uniqueness ∧
      CompactCNF.toCNF fuel true
        (.imp (boundsModeFormula assumptions) (boundsModeFormula required)) = .success result.scalar ∧
      result.locality = locality ++ sandwich .locality .unaffected g.leaves.length ∧
      result.other = affinity ++ uniqueness ++ sandwich .affinity .unaffected g.leaves.length ++
        sandwich .unaffected .uniqueness g.leaves.length := by
  unfold prepare at h
  simp only [bind, pure, RunResult.bind] at h
  split at h <;> try contradiction
  rename_i nominal hn
  split at h <;> try contradiction
  rename_i locality hl
  split at h <;> try contradiction
  rename_i affinity hf
  split at h <;> try contradiction
  rename_i uniqueness hu
  split at h <;> try contradiction
  rename_i scalar hs
  cases h
  exact ⟨locality, affinity, uniqueness, hn, hl, hf, hu, hs, rfl, rfl⟩

theorem prepare_nominal_congr {fuel : Nat} {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {result : Input} (hc : prepare fuel assumptions required g = .success result)
    {parameters : Nat → Bool} {left right : Fin (4 * g.leaves.length) → Bool}
    (h : ∀ i, left (state .unaffected i) = right (state .unaffected i)) :
    CNFHolds (ComparisonJointEncoding.valuation left parameters) result.nominal ↔
      CNFHolds (ComparisonJointEncoding.valuation right parameters) result.nominal := by
  obtain ⟨_, _, _, hn, _⟩ := prepare_coordinates hc
  exact coordinate_congr hn h

theorem prepare_locality_congr {fuel : Nat} {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {result : Input} (hc : prepare fuel assumptions required g = .success result)
    {parameters : Nat → Bool} {left right : Fin (4 * g.leaves.length) → Bool}
    (hp : ∀ i, left (state .unaffected i) = right (state .unaffected i))
    (hl : ∀ i, left (state .locality i) = right (state .locality i)) :
    CNFHolds (ComparisonJointEncoding.valuation left parameters) result.locality ↔
      CNFHolds (ComparisonJointEncoding.valuation right parameters) result.locality := by
  obtain ⟨_, _, _, _, hlc, _, _, _, hle, _⟩ := prepare_coordinates hc
  rw [hle, cnfHolds_append, cnfHolds_append, coordinate_congr hlc hl, sandwich_congr hl hp]

theorem prepare_other_congr {fuel : Nat} {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {result : Input} (hc : prepare fuel assumptions required g = .success result)
    {parameters : Nat → Bool} {left right : Fin (4 * g.leaves.length) → Bool}
    (hp : ∀ i, left (state .unaffected i) = right (state .unaffected i))
    (hf : ∀ i, left (state .affinity i) = right (state .affinity i))
    (hu : ∀ i, left (state .uniqueness i) = right (state .uniqueness i)) :
    CNFHolds (ComparisonJointEncoding.valuation left parameters) result.other ↔
      CNFHolds (ComparisonJointEncoding.valuation right parameters) result.other := by
  obtain ⟨_, _, _, _, _, hfc, huc, _, _, hoe⟩ := prepare_coordinates hc
  simp only [hoe, cnfHolds_append, coordinate_congr hfc hf, coordinate_congr huc hu,
    sandwich_congr hf hp, sandwich_congr hp hu]

end ModalityInference.ComparisonJointGroup
