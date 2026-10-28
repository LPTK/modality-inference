import ModalityInference.ComparisonFiniteCertificate

/-! Tag and observation padding for finite comparison certificates. Added
tags are unused by every constructor row and embed to bottom; added observation
coordinates are false throughout the interpreter. -/
namespace ModalityInference.ComparisonFiniteCertificate

open ComparisonExecutableTables

namespace Padding

def tagRow {M : Type} {old size : Nat} (h : old ≤ size) (r : Row M (Fin old)) : Row M (Fin size) :=
  ⟨r.index,r.left.castLE h,r.right.castLE h,r.result.castLE h⟩

def tagEmbed {O : Type} {old size : Nat} (embed : Fin old → O → Bool)
    (a : Fin size) : O → Bool :=
  if ha : a.val < old then embed ⟨a.val,ha⟩ else fun _ => false

def zeroExtend {old size : Nat} (x : Fin old → Bool) (i : Fin size) : Bool :=
  if hi : i.val < old then x ⟨i.val,hi⟩ else false

def coordinates {Δ names old size} (x : Coordinates Δ names old) : Coordinates Δ names size :=
  fun m => zeroExtend (x m)

end Padding

def Candidate.padTags {Δ : Bounds} {names : List ModVar} (C : Candidate Δ names)
    {tags : Nat} (h : C.tags ≤ tags) : Candidate Δ names :=
  { C with
    tags := tags
    embed := Padding.tagEmbed C.embed
    prodRows := C.prodRows.map (Padding.tagRow h)
    sumRows := C.sumRows.map (Padding.tagRow h)
    fnRows := C.fnRows.map (Padding.tagRow h)
    prodLiterals := C.prodLiterals.map fun r => (r.1,r.2.map (Padding.tagRow h))
    sumLiterals := C.sumLiterals.map fun r => (r.1,r.2.map (Padding.tagRow h)) }

def Candidate.padObservations {Δ : Bounds} {names : List ModVar} (C : Candidate Δ names)
    {observations : Nat} (_ : C.observations ≤ observations) : Candidate Δ names :=
  { C with
    observations := observations
    embed a := Padding.zeroExtend (C.embed a)
    frozen := C.frozen.map fun r => (r.1,Padding.coordinates r.2)
    defined x := Padding.coordinates (C.defined x) }

end ModalityInference.ComparisonFiniteCertificate
