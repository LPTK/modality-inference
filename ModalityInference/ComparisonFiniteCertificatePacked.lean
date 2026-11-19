import ModalityInference.ComparisonFiniteCertificateCanonical
import ModalityInference.ComparisonFiniteCertificateBounds
import ModalityInference.ComparisonObserverMachineFormula
import Mathlib.Data.List.OfFn

/-! Finite arrays and indices for comparison certificates. Syntax keys are
indices into fixed input lists; no certificate or Boolean valuation is searched. -/
namespace ModalityInference.ComparisonFiniteCertificate.Packed

open ComparisonFiniteControlEncoding ComparisonObserverMachineCheck
  ComparisonObserverMachine ComparisonStructuralLayout ComparisonControls
  ComparisonFiniteCertificateBounds

structure BoundedList (α : Type) (bound : Nat) where
  length : Fin (bound + 1)
  values : Fin length.val → α

namespace BoundedList

def toList {α bound} (xs : BoundedList α bound) : List α := List.ofFn xs.values

def encode {α β : Type} {bound : Nat} (xs : List α) (h : xs.length ≤ bound)
    (f : (x : α) → x ∈ xs → β) : BoundedList β bound where
  length := ⟨xs.length,Nat.lt_succ_iff.mpr h⟩
  values i := f xs[i] (List.getElem_mem i.isLt)

end BoundedList

def keyIndex {α : Type} [DecidableEq α] (keys : List α) (a : α) (ha : a ∈ keys) :
    Fin keys.length := ⟨keys.idxOf a,List.idxOf_lt_length_iff.mpr ha⟩

def constructorIndex : Constructor → Fin 3
  | .prod => 0 | .sum => 1 | .fn => 2

def indexConstructor (i : Fin 3) : Constructor :=
  if i = 0 then .prod else if i = 1 then .sum else .fn

structure MachineData (types modes states : Nat) where
  atoms : Fin types → Bool
  modes : Fin modes → Bool × Bool × Bool
  coordinate : Bool × Bool
  unitValue : Bool
  creditValue : Bool
  branch : Fin 3 → Bool × Fin states
  range : Bool → Bool

def MachineData.decode {types modes states} (d : MachineData types modes states) :
    Description (Fin states) where
  atoms := List.ofFn d.atoms
  modes := List.ofFn fun i => ⟨(d.modes i).1,(d.modes i).2.1,(d.modes i).2.2⟩
  coordinate := ComparisonObserverMachineFormula.coordinate d.coordinate.1 d.coordinate.2
  unitValue := d.unitValue
  creditValue := d.creditValue
  branch k := ⟨(d.branch (constructorIndex k)).1,(d.branch (constructorIndex k)).2⟩
  range := d.range

def MachineData.encode {types modes states} (d : Description (Fin states))
    (ht : d.atoms.length = types) (hm : d.modes.length = modes) : MachineData types modes states where
  atoms i := d.atoms[i.val]'(ht ▸ i.isLt)
  modes i := let m := d.modes[i.val]'(hm ▸ i.isLt); (m.isLocal,m.once,m.unique)
  coordinate := coordinateBits d.coordinate
  unitValue := d.unitValue
  creditValue := d.creditValue
  branch k := ((d.branch (indexConstructor k)).left,(d.branch (indexConstructor k)).next)
  range := d.range

abbrev PackedRow (controls tags : Nat) := Fin controls × Fin tags × Fin tags × Fin tags

def decodeRow {Δ names tags} (r : PackedRow (labels Δ names).length tags) :
    ComparisonExecutableTables.Row (Code Δ names) (Fin tags) :=
  ⟨⟨r.1⟩,r.2.1,r.2.2.1,r.2.2.2⟩

def encodeRow {Δ names tags} (r : ComparisonExecutableTables.Row (Code Δ names) (Fin tags)) :
    PackedRow (labels Δ names).length tags := (r.index.index,r.left,r.right,r.result)

abbrev Rows (Δ : Bounds) (names : List ModVar) (tags : Nat) :=
  BoundedList (PackedRow (labels Δ names).length tags) (rowBound Δ names tags)

def Rows.decode {Δ names tags} (rs : Rows Δ names tags) := rs.toList.map decodeRow

def Rows.encode {Δ names tags} (rs : List (ComparisonExecutableTables.Row (Code Δ names) (Fin tags)))
    (h : rs.length ≤ rowBound Δ names tags) : Rows Δ names tags :=
  BoundedList.encode rs h fun r _ => encodeRow r

structure Payload (Δ : Bounds) (names : List ModVar) (queries : List CompareTy)
    (states tags observations : Nat) where
  machine : Fin states → MachineData (inputTypes Δ queries).length names.length states
  embed : Fin tags → Fin observations → Bool
  prodRows : Rows Δ names tags
  sumRows : Rows Δ names tags
  fnRows : Rows Δ names tags
  prodLiterals : BoundedList (Fin (retainedPrefixes Δ queries).length × Rows Δ names tags)
    (retainedPrefixes Δ queries).length
  sumLiterals : BoundedList (Fin (retainedPrefixes Δ queries).length × Rows Δ names tags)
    (retainedPrefixes Δ queries).length
  frozen : BoundedList (Fin (retainedFrozen Δ queries).length × Coordinates Δ names observations)
    (retainedFrozen Δ queries).length
  defined : ComparisonObserverRangeEncoding.Bits states → Coordinates Δ names observations

def Payload.decode {Δ names queries states tags observations}
    (p : Payload Δ names queries states tags observations) : Candidate Δ names where
  states := states
  tags := tags
  observations := observations
  types := inputTypes Δ queries
  modes := names
  machine i := (p.machine i).decode
  embed := p.embed
  prodRows := p.prodRows.decode
  sumRows := p.sumRows.decode
  fnRows := p.fnRows.decode
  prodLiterals := p.prodLiterals.toList.map fun r => ((retainedPrefixes Δ queries)[r.1],r.2.decode)
  sumLiterals := p.sumLiterals.toList.map fun r => ((retainedPrefixes Δ queries)[r.1],r.2.decode)
  frozen := p.frozen.toList.map fun r => ((retainedFrozen Δ queries)[r.1],r.2)
  defined := p.defined

def Payload.encode {Δ names queries} (C : Candidate Δ names) (h : CanonicalFor queries C) :
    Payload Δ names queries C.states C.tags C.observations where
  machine i := MachineData.encode (C.machine i) (h.atoms_length i) (h.mode_values_length i)
  embed := C.embed
  prodRows := Rows.encode C.prodRows h.prodRows_length
  sumRows := Rows.encode C.sumRows h.sumRows_length
  fnRows := Rows.encode C.fnRows h.fnRows_length
  prodLiterals := BoundedList.encode C.prodLiterals h.prodLiterals_length fun r hr =>
    (keyIndex (retainedPrefixes Δ queries) r.1 (h.prodLiterals_keys r hr),
      Rows.encode r.2 (h.prodLiteralRows_length r hr))
  sumLiterals := BoundedList.encode C.sumLiterals h.sumLiterals_length fun r hr =>
    (keyIndex (retainedPrefixes Δ queries) r.1 (h.sumLiterals_keys r hr),
      Rows.encode r.2 (h.sumLiteralRows_length r hr))
  frozen := BoundedList.encode C.frozen h.frozen_length fun r hr =>
    (keyIndex (retainedFrozen Δ queries) r.1 (h.frozen_keys r hr),r.2)
  defined := C.defined

def endpoints (raw : List Ty) (queries : List CompareTy) : List CompareTy :=
  raw.map CompareTy.ofTy ++ queries

def inputNames (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) : List ModVar :=
  (Δ.modeVariables ++ (endpoints raw queries).flatMap ComparisonObserverBoundary.modeList).dedup

structure Header (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) where
  names : BoundedList (Fin (inputNames Δ raw queries).length) (nameBound Δ raw queries)
  states : Fin (stateBound Δ raw queries + 1)
  tags : Fin (tagsBound Δ raw queries + 1)
  observations : Fin (observationsBound Δ raw queries + 1)

def Header.decodeNames {Δ raw queries} (h : Header Δ raw queries) : List ModVar :=
  h.names.toList.map fun i => (inputNames Δ raw queries)[i]

def Header.encode {Δ names raw queries} (C : Candidate Δ names) (h : WithinDimensions raw queries C)
    (hs : ∀ v ∈ names, v ∈ inputNames Δ raw queries) :
    Header Δ raw queries where
  names := BoundedList.encode names h.1 fun v hv =>
    keyIndex (inputNames Δ raw queries) v (hs v hv)
  states := ⟨C.states,Nat.lt_succ_iff.mpr h.2.2.1⟩
  tags := ⟨C.tags,Nat.lt_succ_iff.mpr h.2.2.2.1⟩
  observations := ⟨C.observations,Nat.lt_succ_iff.mpr h.2.2.2.2⟩

structure Certificate (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) where
  header : Header Δ raw queries
  payload : Payload Δ header.decodeNames (endpoints raw queries)
    header.states.val header.tags.val header.observations.val

def Certificate.decode {Δ raw queries} (p : Certificate Δ raw queries) : Candidate Δ p.header.decodeNames :=
  p.payload.decode

def Certificate.check {Δ raw queries} (p : Certificate Δ raw queries) : Bool := p.decode.check

def Certificate.separates {Δ raw queries} (p : Certificate Δ raw queries) (a b : CompareTy) : Bool :=
  p.decode.separates a b

end ModalityInference.ComparisonFiniteCertificate.Packed
