import ModalityInference.ComparisonFiniteCertificateFormulaEncoding
import ModalityInference.Proofs.ComparisonFiniteCertificateFormula
import ModalityInference.Proofs.ComparisonFiniteCertificateDense
import ModalityInference.Proofs.ComparisonObserverBitsCode
import ModalityInference.Proofs.ComparisonObserverMachineEncoding
import ModalityInference.Proofs.ComparisonObserverMachineNormalization
import ModalityInference.Proofs.ComparisonRankedDecision

/-! The fixed field layout covers dense certificates exactly. Satisfying
assignments retain the original validator and semantic separation guarantees. -/
namespace ModalityInference.ComparisonFiniteCertificateFormulaEncoding

open ComparisonFiniteCertificate ComparisonFiniteCertificateFormula
  ComparisonFiniteControlEncoding ComparisonExecutableTables

@[simp] theorem readPair_address {left right} (value : Fin left → Fin right → Bool)
    (a : Fin left) (b : Fin right) : readPair value (Nat.pair a.val b.val) = value a b := by
  simp only [readPair, Nat.unpair_pair, a.isLt, b.isLt, dite_true]

@[simp] theorem readRow_address {Δ names tags} (value : Row (Code Δ names) (Fin tags) → Bool)
    (r : Row (Code Δ names) (Fin tags)) : readRow value (rowAddress r) = value r := by
  simp only [readRow, rowAddress, Nat.unpair_pair, r.index.index.isLt, r.left.isLt, r.right.isLt, r.result.isLt, dite_true]

@[simp] theorem readVector_address {Δ names observations} (value : Coordinates Δ names observations)
    (m : Code Δ names) (o : Fin observations) : readVector value (vectorAddress m o) = value m o := by
  exact readPair_address (fun m o => value ⟨m⟩ o) m.index o

@[simp] theorem readLiteral_address {Δ names tags} (keys : List ModExpr)
    (value : ModExpr → List (Row (Code Δ names) (Fin tags))) (i : Fin keys.length)
    (r : Row (Code Δ names) (Fin tags)) :
    readLiteral keys value (Nat.pair i.val (rowAddress r)) = decide (r ∈ value keys[i]) := by
  simp only [readLiteral, Nat.unpair_pair, List.getElem?_eq_getElem i.isLt, readRow_address]
  rfl

@[simp] theorem readFrozen_address {Δ names observations} (keys : List CompareTy)
    (value : CompareTy → Coordinates Δ names observations) (i : Fin keys.length)
    (m : Code Δ names) (o : Fin observations) :
    readFrozen keys value (Nat.pair i.val (vectorAddress m o)) = value keys[i] m o := by
  simp only [readFrozen, Nat.unpair_pair, List.getElem?_eq_getElem i.isLt, readVector_address]
  rfl

variable {Δ : Bounds} {names : List ModVar} (C : Candidate Δ names) (queries : List CompareTy)

theorem machine_decode
    (hat : ∀ i, (C.machine i).atoms.length = (inputTypes Δ queries).length)
    (hmo : ∀ i, (C.machine i).modes.length = names.length) :
    ComparisonObserverMachineFormula.decode
      (allocate Δ names queries C.states C.tags C.observations).machine (encode C queries) = C.machine := by
  simp only [allocate, ComparisonRankedDecision.decode_mapFields, Function.comp_def,
    encode, address, Nat.unpair_pair]
  exact funext fun i => (ComparisonObserverMachineEncoding.allocate_decode _ _ C.machine i).trans
    (ComparisonObserverMachineEncoding.normalize_eq_of_lengths _ _ _ (hat i) (hmo i))

theorem vector_decode_frozen (i : Fin (retainedFrozen Δ queries).length) :
    ComparisonExecutableAgreementFormula.decode (encode C queries) (vector 7 i.val) =
      C.data.frozenValue (retainedFrozen Δ queries)[i] := by
  funext m o
  simp only [ComparisonExecutableAgreementFormula.decode, vector, BoolExpr.eval, encode,
    address, Nat.unpair_pair, readFrozen_address]

theorem vector_decode_defined (x : ComparisonObserverRangeEncoding.Bits C.states) :
    ComparisonExecutableAgreementFormula.decode (encode C queries)
      (vector 8 (ComparisonObserverBitsCode.bitsCode x)) = C.defined x := by
  funext m o
  simp only [ComparisonExecutableAgreementFormula.decode, vector, BoolExpr.eval, encode,
    address, Nat.unpair_pair, ComparisonObserverBitsCode.decodeBits_code, readVector_address]

theorem ofFn_get {α β : Type*} (xs : List α) (f : α → β) :
    (List.ofFn fun i : Fin xs.length => f xs[i]) = xs.map f := by
  simpa only [List.map_ofFn, Function.comp_def] using congrArg (List.map f) (List.ofFn_getElem xs)

theorem allocate_decode (ht : C.types = inputTypes Δ queries) (hm : C.modes = names)
    (hat : ∀ i, (C.machine i).atoms.length = (inputTypes Δ queries).length)
    (hmo : ∀ i, (C.machine i).modes.length = names.length) :
    (allocate Δ names queries C.states C.tags C.observations).decode
      (inputTypes Δ queries) names (encode C queries) = C.densify queries := by
  simp only [Fields.decode, Candidate.densify, machine_decode C queries hat hmo]
  simp only [allocate, selection, literal, BoolExpr.eval, encode, address,
    Nat.unpair_pair, ComparisonExecutableTableFormula.selected, canonicalRows, rows,
    readPair_address, readRow_address, readLiteral_address, List.map_ofFn, Function.comp_def,
    vector_decode_frozen, vector_decode_defined, ht, hm]
  congr 1
  · exact ofFn_get (retainedPrefixes Δ queries) (fun p => (p,canonicalRows (C.prodAt (some p))))
  · exact ofFn_get (retainedPrefixes Δ queries) (fun p => (p,canonicalRows (C.sumAt (some p))))
  · exact ofFn_get (retainedFrozen Δ queries) (fun a => (a,C.data.frozenValue a))

theorem query_encode (ht : C.types = inputTypes Δ queries) (hm : C.modes = names)
    (hat : ∀ i, (C.machine i).atoms.length = (inputTypes Δ queries).length)
    (hmo : ∀ i, (C.machine i).modes.length = names.length) {a b : CompareTy}
    (ha : a ∈ queries) (hb : b ∈ queries) (h : C.separates a b = true) :
    (query Δ names queries C.states C.tags C.observations a b).eval (encode C queries) = true := by
  simpa only [query, Fields.separates_eval, allocate_decode C queries ht hm hat hmo] using
    C.densify_separates queries ha hb h

theorem query_sound {states tags observations : Nat} {a b : CompareTy} {world : Nat → Bool}
    (h : (query Δ names queries states tags observations a b).eval world = true) :
    ¬ AlgebraSubtype Δ a b :=
  (allocate Δ names queries states tags observations).separates_sound
    (inputTypes Δ queries) names world h

end ModalityInference.ComparisonFiniteCertificateFormulaEncoding
