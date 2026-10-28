import ModalityInference.ComparisonObserverRangeEncoding

/-! Binary addresses for finite observer vectors, with coordinate zero stored
as the least significant bit. -/
namespace ModalityInference.ComparisonObserverBitsCode

open ComparisonObserverRangeEncoding

def bitsCode : {n : Nat} → Bits n → Nat
  | 0, _ => 0
  | _ + 1, x => (if x 0 then 1 else 0) + 2 * bitsCode (fun i => x i.succ)

def decodeBits : (n : Nat) → Nat → Bits n
  | 0, _ => Fin.elim0
  | n + 1, k => Fin.cases (decide (k % 2 = 1)) (decodeBits n (k / 2))

end ModalityInference.ComparisonObserverBitsCode
