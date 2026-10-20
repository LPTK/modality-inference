import ModalityInference.Proofs.ComparisonRankedModes
import ModalityInference.Proofs.ComparisonObserverMachineEncoding

/-! Every finite observer machine has a separated route-world presentation.
The basis observations occupy nominal fields disjoint from the machine fields
and scalar inputs, so their exact aliases can be supplied simultaneously. -/
namespace ModalityInference.ComparisonRankedModes

open ComparisonControls ComparisonStructuralLayout ComparisonSignedObservation
  ComparisonObserverMachineFormula

private theorem layout_injective : Function.Injective ComparisonLayoutWorlds.decode := by
  intro u v h
  change (if (ComparisonLayoutWorlds.location u).2 % 4 = 2 then
      (ComparisonLayoutWorlds.routeCode (ComparisonLayoutWorlds.location u).1 + 1,
        (ComparisonLayoutWorlds.location u).2 / 4) else (0, u)) =
    (if (ComparisonLayoutWorlds.location v).2 % 4 = 2 then
      (ComparisonLayoutWorlds.routeCode (ComparisonLayoutWorlds.location v).1 + 1,
        (ComparisonLayoutWorlds.location v).2 / 4) else (0, v)) at h
  by_cases hu : (ComparisonLayoutWorlds.location u).2 % 4 = 2 <;>
    by_cases hv : (ComparisonLayoutWorlds.location v).2 % 4 = 2 <;>
    simp only [hu, hv, if_true, if_false] at h
  · have hr := ComparisonLayoutWorlds.routeCode_injective
      (Nat.add_right_cancel (congrArg Prod.fst h))
    have hs : (ComparisonLayoutWorlds.location u).2 =
        (ComparisonLayoutWorlds.location v).2 := by
      have hh := congrArg Prod.snd h
      dsimp at hh
      omega
    exact (ComparisonLayoutWorlds.location_inverse u).symm.trans
      ((congrArg₂ routeAtom hr (congrArg localAtom hs)).trans
        (ComparisonLayoutWorlds.location_inverse v))
  · have hh := congrArg Prod.fst h
    dsimp at hh
    omega
  · have hh := congrArg Prod.fst h
    dsimp at hh
    omega
  · exact congrArg Prod.snd h

theorem raw_id_surjective (flat : Nat → Bool) :
    ∃ world : Nat → Nat → Bool, raw id world = flat := by
  let world := fun point atom =>
    Function.extend ComparisonLayoutWorlds.decode flat (fun _ => false) (point, atom)
  refine ⟨world, funext fun v => ?_⟩
  change ComparisonWorldClauses.shared id id _ (world _) _ = _
  simp only [ComparisonWorldClauses.shared, ite_self, id_eq]
  exact layout_injective.extend_apply flat (fun _ => false) v

private def payload {count}
    (d : ComparisonObserverMachineCheck.Description (Fin count)) (field index : Nat) : Bool :=
  match field with
  | 0 => d.atoms[index]?.getD d.unitValue
  | 1 => if index = 0 then (coordinateBits d.coordinate).1 else (coordinateBits d.coordinate).2
  | 2 => if index = 0 then d.unitValue else d.creditValue
  | 3 => (d.branch (ComparisonObserverMachineEncoding.constructor index)).left
  | 4 => decide (index = (d.branch .prod).next.val)
  | 5 => decide (index = (d.branch .sum).next.val)
  | 6 => decide (index = (d.branch .fn).next.val)
  | 7 => d.range (index != 0)
  | _ => false

private def flat {count} (types : List TypeVar) (names : List ModVar)
    (basis : Basis) (data : Fin count → ComparisonObserverMachineCheck.Description (Fin count))
    (u : Nat) : Bool :=
  let loc := ComparisonLayoutWorlds.location u
  if h : loc.1.length < count then
    let i : Fin count := ⟨loc.1.length, h⟩
    match loc.2 % 4 with
    | 0 => ComparisonObserverMachine.value (ComparisonObserverMachineCheck.nodes types names data)
        (basis.types[loc.2 / 4]?.getD .unit) i
    | 2 => if SymbolicModes.atomVariable (loc.2 / 4) ∈ names then
        encodeModes (ComparisonObserverMachineCheck.modeValue names (data i)) (loc.2 / 4)
      else false
    | 3 => payload (data i) (Nat.unpair (loc.2 / 4)).1 (Nat.unpair (loc.2 / 4)).2
    | _ => false
  else false

private theorem flat_choice {count} (types : List TypeVar) (names : List ModVar)
    (basis : Basis) (data : Fin count → ComparisonObserverMachineCheck.Description (Fin count))
    (i : Fin count) (field index : Nat) :
    flat types names basis data (routeAtom (route i) (choiceAtom (Nat.pair field index))) =
      payload (data i) field index := by
  have h : (4 * Nat.pair field index + 3) / 4 = Nat.pair field index := by omega
  simp [flat, choiceAtom, route, h, Nat.unpair_pair, i.isLt]

private theorem flat_scalar {count} (types : List TypeVar) (names : List ModVar)
    (basis : Basis) (data : Fin count → ComparisonObserverMachineCheck.Description (Fin count))
    (i : Fin count) (index : Nat) :
    flat types names basis data (routeAtom (route i) (ComparisonStructuralLayout.modeAtom index)) =
      (if SymbolicModes.atomVariable index ∈ names then
        encodeModes (ComparisonObserverMachineCheck.modeValue names (data i)) index else false) := by
  have h : (4 * index + 2) / 4 = index := by omega
  simp [flat, ComparisonStructuralLayout.modeAtom, route, h, i.isLt]

private theorem flat_basis {count} (types : List TypeVar) (names : List ModVar)
    (basis : Basis) (data : Fin count → ComparisonObserverMachineCheck.Description (Fin count))
    (i : Fin count) (index : Nat) :
    flat types names basis data (routeAtom (route i) (basisAtom index)) =
      ComparisonObserverMachine.value (ComparisonObserverMachineCheck.nodes types names data)
        (basis.types[index]?.getD .unit) i := by
  simp [flat, basisAtom, route, i.isLt]

private def canonical {count} (types : List TypeVar) (names : List ModVar)
    (d : ComparisonObserverMachineCheck.Description (Fin count)) :
    ComparisonObserverMachineCheck.Description (Fin count) :=
  { d with
    atoms := (List.range types.length).map (fun j => d.atoms[j]?.getD d.unitValue)
    modes := names.map (ComparisonObserverMachineCheck.modeValue names d) }

private theorem canonical_atom {count} (types : List TypeVar) (names : List ModVar)
    (d : ComparisonObserverMachineCheck.Description (Fin count)) :
    ComparisonObserverMachineCheck.atomValue types (canonical types names d) =
      ComparisonObserverMachineCheck.atomValue types d :=
  ComparisonObserverMachineEncoding.normalize_atoms types names.length d

private theorem canonical_mode {count} (types : List TypeVar) (names : List ModVar)
    (d : ComparisonObserverMachineCheck.Description (Fin count)) :
    ComparisonObserverMachineCheck.modeValue names (canonical types names d) =
      ComparisonObserverMachineCheck.modeValue names d := by
  funext v
  by_cases hv : v ∈ names
  · have hi := List.idxOf_lt_length_of_mem hv
    have he : names[names.idxOf v]? = some v := by
      rw [List.getElem?_eq_getElem hi]
      congr 1
      simpa only [List.idxOf, beq_iff_eq] using
        (List.findIdx_getElem (xs := names) (p := (· == v)) (w := hi))
    simp [ComparisonObserverMachineCheck.modeValue, canonical, hv,
      List.getElem?_map, he]
  · simp [ComparisonObserverMachineCheck.modeValue, hv]

private theorem canonical_nodes {count} (types : List TypeVar) (names : List ModVar)
    (data : Fin count → ComparisonObserverMachineCheck.Description (Fin count)) :
    ComparisonObserverMachineCheck.nodes types names (fun i => canonical types names (data i)) =
      ComparisonObserverMachineCheck.nodes types names data := by
  funext i
  have ha : ComparisonObserverMachineCheck.action names (canonical types names (data i)) =
      ComparisonObserverMachineCheck.action names (data i) := by
    funext m x
    simp only [ComparisonObserverMachineCheck.action, canonical_mode]
    rfl
  simp only [ComparisonObserverMachineCheck.nodes, canonical_atom, ha]
  rfl

private theorem canonical_check {count} (Δ : Bounds) (types : List TypeVar) (names : List ModVar)
    (data : Fin count → ComparisonObserverMachineCheck.Description (Fin count)) :
    ComparisonObserverMachineCheck.check Δ types names (fun i => canonical types names (data i)) =
      ComparisonObserverMachineCheck.check Δ types names data := by
  unfold ComparisonObserverMachineCheck.check
  congr 1
  funext i
  simp only [ComparisonObserverMachineCheck.checkNode, ComparisonObserverMachineCheck.scalarOK,
    ComparisonObserverMachineCheck.sameInputs, ComparisonObserverMachineCheck.pairOK,
    ComparisonObserverMachineCheck.closedRange, ComparisonObserverMachineCheck.branchRange,
    ComparisonObserverMachineCheck.functionRange, ComparisonObserverMachineCheck.declared,
    canonical_mode, canonical_atom, canonical_nodes]
  rfl

private theorem fields_decode {count} (types : List TypeVar) (names : List ModVar)
    (basis : Basis) (data : Fin count → ComparisonObserverMachineCheck.Description (Fin count))
    (i : Fin count) :
    decode (fields types names count) (flat types names basis data) i =
      canonical types names (data i) := by
  have hs (v : ModVar) (hv : v ∈ names) :
      scalar (scalarField i v 0, scalarField i v 1, scalarField i v 2)
        (flat types names basis data) =
      ComparisonObserverMachineCheck.modeValue names (data i) v := by
    simp only [scalar, scalarField, BoolExpr.eval, flat_scalar,
      ComparisonControls.atomVariable_atomIndex v 0 (by decide),
      ComparisonControls.atomVariable_atomIndex v 1 (by decide),
      ComparisonControls.atomVariable_atomIndex v 2 (by decide), hv, if_true]
    exact congrFun (projectedModes_encodeModes
      (ComparisonObserverMachineCheck.modeValue names (data i))) v
  have hm := List.map_congr_left hs
  have hn (k : Constructor) :
      firstTrue i (fun j : Fin count => payload (data i) (4 + constructorCode k) j)
        (List.finRange count) = ((data i).branch k).next := by
    cases k <;> simpa only [constructorCode, payload, Fin.val_inj] using
      ComparisonObserverMachineEncoding.firstTrue_eq i ((data i).branch _).next
        (List.finRange count) (List.mem_finRange _)
  have hl (k : Constructor) :
      ComparisonObserverMachineEncoding.constructor (constructorCode k) = k := by
    cases k <;> rfl
  simp only [decode, fields, List.map_map, Function.comp_def, hm,
    nominal, BoolExpr.eval, flat_choice, hn]
  simp [payload, hl, canonical]
  funext b
  cases b <;> rfl

/-- Nominal machine fields, exact basis observations, and route-local scalar
worlds are jointly realizable. Unnamed scalar inputs are false, so projecting
the shared modality strategy to the retained names preserves these worlds. -/
theorem machine_world {count} (Δ : Bounds) (types : List TypeVar) (names : List ModVar)
    (basis : Basis) (data : Fin count → ComparisonObserverMachineCheck.Description (Fin count)) :
    ∃ world : Nat → Nat → Bool,
      ComparisonObserverMachineCheck.nodes types names
        (decode (fields types names count) (raw id world)) =
        ComparisonObserverMachineCheck.nodes types names data ∧
      (query Δ types names (fields types names count)).eval (raw id world) =
        ComparisonObserverMachineCheck.check Δ types names data ∧
      (aliases types names count basis).eval (raw id world) = true ∧
      ∀ i : Fin count, ∀ u, SymbolicModes.atomVariable u ∉ names →
        localWorld world i u = false := by
  obtain ⟨world, hw⟩ := raw_id_surjective (flat types names basis data)
  have hd : decode (fields types names count) (raw id world) =
      fun i => canonical types names (data i) := by
    rw [hw]
    exact funext (fields_decode types names basis data)
  have hn : ComparisonObserverMachineCheck.nodes types names
      (decode (fields types names count) (raw id world)) =
      ComparisonObserverMachineCheck.nodes types names data := by
    rw [hd, canonical_nodes]
  refine ⟨world, hn, ?_, ?_, ?_⟩
  · rw [query_eval, hd, canonical_check]
  · apply (aliases_correct types names count basis _).mpr
    intro i index hi
    rw [value_eval, hn, hw, flat_basis, List.getElem?_eq_getElem hi]
    rfl
  · intro i u hu
    have he : raw id world (routeAtom (route i) (ComparisonStructuralLayout.modeAtom u)) =
        localWorld world i u := by
      simp [raw, ComparisonSignedPoints.raw, localWorld]
    rw [hw, flat_scalar, if_neg hu] at he
    exact he.symm

end ModalityInference.ComparisonRankedModes
