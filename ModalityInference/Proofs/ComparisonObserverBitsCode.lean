import ModalityInference.ComparisonObserverBitsCode

/-! Binary vector addresses decode exactly and fit in the finite address space. -/
namespace ModalityInference.ComparisonObserverBitsCode

open ComparisonObserverRangeEncoding

@[simp] theorem decodeBits_code {n : Nat} (x : Bits n) : decodeBits n (bitsCode x) = x := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    cases hx : x 0 <;> simp [bitsCode, decodeBits, hx, ih, Nat.add_div] <;>
      exact funext (fun i => Fin.cases hx.symm (fun _ => rfl) i)

theorem bitsCode_injective (n : Nat) : Function.Injective (@bitsCode n) :=
  fun x y h => (decodeBits_code x).symm.trans
    ((congrArg (decodeBits n) h).trans (decodeBits_code y))

theorem bitsCode_lt {n : Nat} (x : Bits n) : bitsCode x < 2 ^ n := by
  induction n with
  | zero => simp [bitsCode]
  | succ n ih =>
    have ht := ih (fun i => x i.succ)
    simp only [bitsCode, pow_succ]
    split <;> omega

end ModalityInference.ComparisonObserverBitsCode
