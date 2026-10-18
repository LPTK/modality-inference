import ModalityInference.ComparisonObserverMachineEncoding
import ModalityInference.Proofs.ComparisonObserverMachineFormula

/-! The fixed input layout represents every finite certificate. Truncation and
padding preserve the actual name lookups, including their inhabited defaults. -/
namespace ModalityInference.ComparisonObserverMachineEncoding

open ComparisonControls ComparisonStructuralLayout ComparisonObserverMachine
  ComparisonObserverMachineFormula

abbrev Description (count : Nat) := ComparisonObserverMachineCheck.Description (Fin count)

def normalize {count} (typeCount modeCount : Nat) (d : Description count) : Description count :=
  { d with
    atoms := (List.range typeCount).map (fun j => d.atoms[j]?.getD d.unitValue)
    modes := (List.range modeCount).map (fun j => d.modes[j]?.getD Mode.identity) }

def payload {count} (d : Description count) (field index : Nat) : Bool :=
  match field with
  | 0 => d.atoms[index]?.getD d.unitValue
  | 1 =>
    let m := d.modes[(Nat.unpair index).1]?.getD Mode.identity
    match (Nat.unpair index).2 with | 0 => m.isLocal | 1 => m.once | _ => m.unique
  | 2 => if index = 0 then (coordinateBits d.coordinate).1 else (coordinateBits d.coordinate).2
  | 3 => if index = 0 then d.unitValue else d.creditValue
  | 4 => (d.branch (constructor index)).left
  | 5 => decide ((Nat.unpair index).2 = (d.branch (constructor (Nat.unpair index).1)).next.val)
  | 6 => d.range (index != 0)
  | _ => false

def encode {count} (data : Fin count → Description count) (u : Nat) : Bool :=
  let state := (Nat.unpair u).1
  let field := Nat.unpair (Nat.unpair u).2
  if h : state < count then payload (data ⟨state,h⟩) field.1 field.2 else false

@[simp] theorem encode_slot {count} (data : Fin count → Description count) (i : Fin count) (field index : Nat) :
    encode data (slot i field index) = payload (data i) field index := by
  simp [encode, slot, Nat.unpair_pair, i.isLt]

@[simp] theorem constructor_code (k : Constructor) : constructor (code k) = k := by cases k <;> rfl

@[simp] theorem coordinate_bits (c : Coordinate) :
    coordinate (coordinateBits c).1 (coordinateBits c).2 = c := by cases c <;> rfl

theorem firstTrue_eq {α} [DecidableEq α] (fallback target : α) (xs : List α)
    (ht : target ∈ xs) : firstTrue fallback (fun x => decide (x=target)) xs = target := by
  induction xs with
  | nil => simp at ht
  | cons x xs ih =>
    by_cases hx : x = target
    · simp [firstTrue, hx]
    · have ht' : target ∈ xs := by simpa [Ne.symm hx] using ht
      simpa [firstTrue, hx] using ih ht'

theorem allocate_decode {count} (typeCount modeCount : Nat) (data : Fin count → Description count) (i : Fin count) :
    ComparisonObserverMachineFormula.decode (allocate typeCount modeCount count) (encode data) i =
      normalize typeCount modeCount (data i) := by
  simp only [ComparisonObserverMachineFormula.decode, allocate, List.map_map, Function.comp_def,
    BoolExpr.eval, encode_slot, payload, Nat.unpair_pair, Nat.reduceEqDiff, ↓reduceIte,
    coordinate_bits, constructor_code, Fin.val_inj]
  simp [scalar, BoolExpr.eval, encode_slot, payload, Nat.unpair_pair, normalize,
    firstTrue_eq]
  funext x
  cases x <;> rfl

@[simp] theorem normalize_atom {count} (types : List TypeVar) (modeCount : Nat)
    (d : Description count) (v : TypeVar) :
    ComparisonObserverMachineCheck.atomValue types (normalize types.length modeCount d) v =
      ComparisonObserverMachineCheck.atomValue types d v := by
  by_cases hv : v ∈ types
  · simp [ComparisonObserverMachineCheck.atomValue, normalize, hv,
      List.getElem?_map, List.getElem?_range (List.idxOf_lt_length_of_mem hv)]
  · simp [ComparisonObserverMachineCheck.atomValue, normalize, hv]

@[simp] theorem normalize_mode {count} (names : List ModVar) (typeCount : Nat)
    (d : Description count) (v : ModVar) :
    ComparisonObserverMachineCheck.modeValue names (normalize typeCount names.length d) v =
      ComparisonObserverMachineCheck.modeValue names d v := by
  by_cases hv : v ∈ names
  · simp [ComparisonObserverMachineCheck.modeValue, normalize, hv,
      List.getElem?_map, List.getElem?_range (List.idxOf_lt_length_of_mem hv)]
  · simp [ComparisonObserverMachineCheck.modeValue, hv]

@[simp] theorem normalize_atoms {count} (types : List TypeVar) (modeCount : Nat) (d : Description count) :
    ComparisonObserverMachineCheck.atomValue types (normalize types.length modeCount d) =
      ComparisonObserverMachineCheck.atomValue types d := funext (normalize_atom types modeCount d)

@[simp] theorem normalize_modes {count} (names : List ModVar) (typeCount : Nat) (d : Description count) :
    ComparisonObserverMachineCheck.modeValue names (normalize typeCount names.length d) =
      ComparisonObserverMachineCheck.modeValue names d := funext (normalize_mode names typeCount d)

@[simp] theorem normalize_action {count} (names : List ModVar) (typeCount : Nat) (d : Description count) :
    ComparisonObserverMachineCheck.action names (normalize typeCount names.length d) =
      ComparisonObserverMachineCheck.action names d := by
  funext m x
  simp only [ComparisonObserverMachineCheck.action, normalize_modes]
  rfl

@[simp] theorem normalize_nodes {count} (types : List TypeVar) (names : List ModVar)
    (data : Fin count → Description count) :
    ComparisonObserverMachineCheck.nodes types names (fun i => normalize types.length names.length (data i)) =
      ComparisonObserverMachineCheck.nodes types names data := by
  funext i
  simp only [ComparisonObserverMachineCheck.nodes, normalize_atoms, normalize_action]
  rfl

@[simp] theorem normalize_checkNode {count} (Δ : Bounds) (types : List TypeVar) (names : List ModVar)
    (data : Fin count → Description count) (i : Fin count) :
    ComparisonObserverMachineCheck.checkNode Δ types names
        (fun j => normalize types.length names.length (data j)) i =
      ComparisonObserverMachineCheck.checkNode Δ types names data i := by
  simp only [ComparisonObserverMachineCheck.checkNode, ComparisonObserverMachineCheck.scalarOK,
    ComparisonObserverMachineCheck.sameInputs, ComparisonObserverMachineCheck.pairOK,
    ComparisonObserverMachineCheck.closedRange, ComparisonObserverMachineCheck.branchRange,
    ComparisonObserverMachineCheck.functionRange, ComparisonObserverMachineCheck.declared,
    normalize_mode, normalize_modes, normalize_atom, normalize_nodes]
  rfl

@[simp] theorem normalize_check {count} (Δ : Bounds) (types : List TypeVar) (names : List ModVar)
    (data : Fin count → Description count) :
    ComparisonObserverMachineCheck.check Δ types names
        (fun i => normalize types.length names.length (data i)) =
      ComparisonObserverMachineCheck.check Δ types names data := by
  unfold ComparisonObserverMachineCheck.check
  exact congrArg (List.all (List.finRange count)) (funext (normalize_checkNode Δ types names data))

theorem query_eval (Δ : Bounds) (types : List TypeVar) (names : List ModVar)
    (count : Nat) (world : Nat → Bool) :
    (query Δ types names count).eval world =
      ComparisonObserverMachineCheck.check Δ types names (decode types names count world) :=
  ComparisonObserverMachineFormula.query_eval _ _ _ _ _

/-- Every finite certificate is representable in the fixed layout, without
length, uniqueness or consistency premises. Unused entries are truncated and
missing entries retain the checker's exact defaults. -/
theorem query_encode {count} (Δ : Bounds) (types : List TypeVar) (names : List ModVar)
    (data : Fin count → Description count) :
    (query Δ types names count).eval (encode data) =
      ComparisonObserverMachineCheck.check Δ types names data := by
  rw [query_eval]
  have hd : decode types names count (encode data) =
      fun i => normalize types.length names.length (data i) :=
    funext (allocate_decode types.length names.length data)
  rw [hd, normalize_check]

theorem encode_nodes {count} (types : List TypeVar) (names : List ModVar)
    (data : Fin count → Description count) :
    ComparisonObserverMachineCheck.nodes types names (decode types names count (encode data)) =
      ComparisonObserverMachineCheck.nodes types names data := by
  have hd : decode types names count (encode data) =
      fun i => normalize types.length names.length (data i) :=
    funext (allocate_decode types.length names.length data)
  rw [hd, normalize_nodes]

/-- The symbolic query and concrete finite certificates have exactly the same
models. This equivalence does not assert existence of a bounded certificate. -/
theorem query_satisfiable (Δ : Bounds) (types : List TypeVar) (names : List ModVar) (count : Nat) :
    (∃world, (query Δ types names count).eval world = true) ↔
      ∃data : Fin count → Description count, ComparisonObserverMachineCheck.check Δ types names data = true := by
  constructor
  · rintro ⟨world,hw⟩
    exact ⟨decode types names count world,(query_eval Δ types names count world) ▸ hw⟩
  · rintro ⟨data,hd⟩
    exact ⟨encode data,(query_encode Δ types names data).trans hd⟩

theorem observation_eval (types : List TypeVar) (names : List ModVar) (count : Nat)
    (a : CompareTy) (i : Fin count) (world : Nat → Bool) :
    (observation types names count a i).eval world =
      ComparisonObserverMachine.value
        (ComparisonObserverMachineCheck.nodes types names (decode types names count world)) a i :=
  ComparisonObserverMachineFormula.value_eval _ _ _ _ _ _

theorem observation_encode {count} (types : List TypeVar) (names : List ModVar)
    (data : Fin count → Description count) (a : CompareTy) (i : Fin count) :
    (observation types names count a i).eval (encode data) =
      ComparisonObserverMachine.value (ComparisonObserverMachineCheck.nodes types names data) a i := by
  rw [observation_eval, encode_nodes]

private theorem any_map_eval {α} (xs : List α) (f : α → BoolExpr) (world : Nat → Bool) :
    (BoolExpr.any (xs.map f)).eval world = xs.any (fun x => (f x).eval world) := by
  induction xs <;> simp_all [BoolExpr.any, BoolExpr.eval]

theorem counterexample_eval (Δ : Bounds) (types : List TypeVar) (names : List ModVar)
    (count : Nat) (a b : CompareTy) (world : Nat → Bool) :
    (counterexample Δ types names count a b).eval world = true ↔
      ComparisonObserverMachineCheck.check Δ types names (decode types names count world) = true ∧
      ∃i, ComparisonObserverMachine.value
          (ComparisonObserverMachineCheck.nodes types names (decode types names count world)) a i = true ∧
        ComparisonObserverMachine.value
          (ComparisonObserverMachineCheck.nodes types names (decode types names count world)) b i = false := by
  simp only [counterexample, BoolExpr.eval, Bool.and_eq_true, query_eval, any_map_eval,
    List.any_eq_true, List.mem_finRange, true_and, BoolExpr.eval, Bool.or_false,
    observation_eval]
  simp

theorem counterexample_satisfiable (Δ : Bounds) (types : List TypeVar) (names : List ModVar)
    (count : Nat) (a b : CompareTy) :
    (∃world, (counterexample Δ types names count a b).eval world = true) ↔
      ∃data : Fin count → Description count, ComparisonObserverMachineCheck.check Δ types names data = true ∧
        ∃i, ComparisonObserverMachine.value (ComparisonObserverMachineCheck.nodes types names data) a i = true ∧
          ComparisonObserverMachine.value (ComparisonObserverMachineCheck.nodes types names data) b i = false := by
  constructor
  · rintro ⟨world,hw⟩
    exact ⟨decode types names count world,(counterexample_eval Δ types names count a b world).mp hw⟩
  · rintro ⟨data,hd,i,ha,hb⟩
    refine ⟨encode data,(counterexample_eval Δ types names count a b (encode data)).mpr ?_⟩
    have hc : ComparisonObserverMachineCheck.check Δ types names
        (decode types names count (encode data)) = true := by
      rw [←query_eval,query_encode]
      exact hd
    exact ⟨hc,i,(encode_nodes types names data) ▸ ha,(encode_nodes types names data) ▸ hb⟩

theorem counterexample_sound {Δ types names count a b world}
    (hΔ : Bounds.TypeBoundsDefined Δ) (ha : CompareTy.DefinedUnder a Δ) (hb : CompareTy.DefinedUnder b Δ)
    (h : (counterexample Δ types names count a b).eval world = true) : ¬AlgebraSubtype Δ a b := by
  obtain ⟨hc,i,hia,hib⟩ := (counterexample_eval Δ types names count a b world).mp h
  intro hab
  have hle := ComparisonObserverMachineCheck.checked_subtype hc hΔ ha hb hab i
  simp [Bool.le_iff_imp,hia,hib] at hle

end ModalityInference.ComparisonObserverMachineEncoding
