import ModalityInference.ComparisonFiniteCertificatePacked
import ModalityInference.Proofs.ComparisonFiniteCertificateCanonical
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Prod

/-! Packing a canonical certificate preserves its full decoded data, including
duplicate lookup keys and their order. Every packed field has a finite domain. -/
namespace ModalityInference.ComparisonFiniteCertificate.Packed

open ComparisonFiniteControlEncoding ComparisonObserverMachineCheck
  ComparisonObserverMachine ComparisonStructuralLayout ComparisonControls
  ComparisonFiniteCertificateBounds

theorem BoundedList.decode_encode {α β : Type} {bound : Nat} (xs : List α)
    (h : xs.length ≤ bound) (f : (x : α) → x ∈ xs → β) (g : β → α)
    (hf : ∀ x hx, g (f x hx) = x) : (encode xs h f).toList.map g = xs := by
  simp only [toList, encode, List.map_ofFn]
  simpa only [Function.comp_def, hf] using List.ofFn_getElem xs

theorem keyIndex_get {α : Type} [DecidableEq α] (keys : List α) (a : α) (ha : a ∈ keys) :
    keys[keyIndex keys a ha] = a := List.getElem_idxOf _

theorem indexConstructor_index (k : Constructor) : indexConstructor (constructorIndex k) = k := by
  cases k <;> rfl

theorem MachineData.decode_encode {types modes states} (d : Description (Fin states))
    (ht : d.atoms.length = types) (hm : d.modes.length = modes) :
    (encode d ht hm).decode = d := by
  subst types
  subst modes
  simp only [decode, encode, List.ofFn_getElem, indexConstructor_index]
  have hc : ComparisonObserverMachineFormula.coordinate
      (coordinateBits d.coordinate).1 (coordinateBits d.coordinate).2 = d.coordinate := by
    cases d.coordinate <;> rfl
  rw [hc]

theorem decodeRow_encodeRow {Δ names tags}
    (r : ComparisonExecutableTables.Row (Code Δ names) (Fin tags)) :
    decodeRow (encodeRow r) = r := by cases r; rfl

theorem Rows.decode_encode {Δ names tags}
    (rs : List (ComparisonExecutableTables.Row (Code Δ names) (Fin tags)))
    (h : rs.length ≤ rowBound Δ names tags) : (encode rs h).decode = rs :=
  BoundedList.decode_encode rs h _ _ (fun r _ => decodeRow_encodeRow r)

theorem Payload.decode_encode {Δ names queries} (C : Candidate Δ names) (h : CanonicalFor queries C) :
    (encode C h).decode = C := by
  simp only [decode, encode, MachineData.decode_encode, Rows.decode_encode]
  congr 1
  · exact h.types_eq.symm
  · exact h.modes_eq.symm
  all_goals apply BoundedList.decode_encode
  all_goals intro r hr
  all_goals simp only [keyIndex_get, Rows.decode_encode, Prod.mk.eta]

theorem mem_inputNames (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) (v : ModVar) :
    v ∈ inputNames Δ raw queries ↔ v ∈ inputModes Δ raw queries := by
  simp only [inputNames, List.mem_dedup, List.mem_append, List.mem_flatMap,
    Bounds.mem_modeVariables, ComparisonObserverBoundary.mem_modeList,
    inputModes, Finset.mem_union, ComparisonObserverBoundary.mem_allModes, endpoints]

theorem Header.decodeNames_encode {Δ names raw queries} (C : Candidate Δ names)
    (h : WithinDimensions raw queries C) (hs : ∀ v ∈ names, v ∈ inputNames Δ raw queries) :
    (encode C h hs).decodeNames = names :=
  BoundedList.decode_encode names h.1 _ _ (fun v hv => keyIndex_get _ v (hs v hv))

def Payload.renameNames {Δ names names' queries states tags observations}
    (h : names = names') (p : Payload Δ names queries states tags observations) :
    Payload Δ names' queries states tags observations := h ▸ p

theorem Payload.decode_renameNames {Δ names names' queries states tags observations}
    (h : names = names') (p : Payload Δ names queries states tags observations) :
    HEq (p.renameNames h).decode p.decode := by cases h; rfl

theorem Payload.check_renameNames {Δ names names' queries states tags observations}
    (h : names = names') (p : Payload Δ names queries states tags observations) :
    (p.renameNames h).decode.check = p.decode.check := by cases h; rfl

theorem Payload.separates_renameNames {Δ names names' queries states tags observations}
    (h : names = names') (p : Payload Δ names queries states tags observations) (a b : CompareTy) :
    (p.renameNames h).decode.separates a b = p.decode.separates a b := by cases h; rfl

def Certificate.encode {Δ names raw queries} (C : Candidate Δ names)
    (hd : WithinDimensions raw queries C) (hc : CanonicalFor (endpoints raw queries) C) :
    Certificate Δ raw queries :=
  let hs := fun v hv => (mem_inputNames Δ raw queries v).mpr (hd.2.1 (List.mem_toFinset.mpr hv))
  { header := Header.encode C hd hs
    payload := (Payload.encode C hc).renameNames (Header.decodeNames_encode C hd hs).symm }

theorem Certificate.decode_encode {Δ names raw queries} (C : Candidate Δ names)
    (hd : WithinDimensions raw queries C) (hc : CanonicalFor (endpoints raw queries) C) :
    HEq (encode C hd hc).decode C := by
  exact (Payload.decode_renameNames _ _).trans (heq_of_eq (Payload.decode_encode C hc))

theorem Certificate.check_encode {Δ names raw queries} (C : Candidate Δ names)
    (hd : WithinDimensions raw queries C) (hc : CanonicalFor (endpoints raw queries) C) :
    (encode C hd hc).check = C.check := by
  simp only [check, decode, encode, Payload.check_renameNames, Payload.decode_encode]

theorem Certificate.separates_encode {Δ names raw queries} (C : Candidate Δ names)
    (hd : WithinDimensions raw queries C) (hc : CanonicalFor (endpoints raw queries) C) (a b : CompareTy) :
    (encode C hd hc).separates a b = C.separates a b := by
  simp only [separates, decode, encode, Payload.separates_renameNames, Payload.decode_encode]

theorem BoundedList.length_toList {α bound} (xs : BoundedList α bound) : xs.toList.length ≤ bound := by
  simpa only [toList, List.length_ofFn] using Nat.le_of_lt_succ xs.length.isLt

theorem Rows.length_decode {Δ names tags} (rs : Rows Δ names tags) :
    rs.decode.length ≤ rowBound Δ names tags := by
  simpa only [decode, List.length_map] using rs.length_toList

theorem Payload.decode_canonicalFor {Δ names queries states tags observations}
    (p : Payload Δ names queries states tags observations) : CanonicalFor queries p.decode := by
  refine ⟨rfl,rfl,?_,?_,p.prodRows.length_decode,p.sumRows.length_decode,p.fnRows.length_decode,
    ?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact fun _ => List.length_ofFn
  · exact fun _ => List.length_ofFn
  · simpa only [decode, List.length_map] using p.prodLiterals.length_toList
  · simpa only [decode, List.length_map] using p.sumLiterals.length_toList
  · intro row hr
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
    exact r.2.length_decode
  · intro row hr
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
    exact r.2.length_decode
  · intro row hr
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
    exact List.getElem_mem r.1.isLt
  · intro row hr
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
    exact List.getElem_mem r.1.isLt
  · simpa only [decode, List.length_map] using p.frozen.length_toList
  · intro row hr
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
    exact List.getElem_mem r.1.isLt

theorem Certificate.decode_canonicalFor {Δ raw queries} (p : Certificate Δ raw queries) :
    CanonicalFor (endpoints raw queries) p.decode := p.payload.decode_canonicalFor

theorem Certificate.decode_withinDimensions {Δ raw queries} (p : Certificate Δ raw queries) :
    WithinDimensions raw queries p.decode := by
  refine ⟨?_,?_,Nat.le_of_lt_succ p.header.states.isLt,
    Nat.le_of_lt_succ p.header.tags.isLt,Nat.le_of_lt_succ p.header.observations.isLt⟩
  · simpa only [Header.decodeNames, List.length_map] using p.header.names.length_toList
  · intro v hv
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    exact (mem_inputNames Δ raw queries _).mp (List.getElem_mem i.isLt)

theorem exists_certificate_iff (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) (a b : CompareTy) :
    (∃ names, ∃ C : Candidate Δ names,
      WithinDimensions raw queries C ∧ CanonicalFor (endpoints raw queries) C ∧ C.separates a b = true) ↔
    ∃ p : Certificate Δ raw queries, p.separates a b = true := by
  constructor
  · rintro ⟨names,C,hd,hc,hs⟩
    exact ⟨Certificate.encode C hd hc,(Certificate.separates_encode C hd hc a b).trans hs⟩
  · rintro ⟨p,hp⟩
    exact ⟨_,p.decode,p.decode_withinDimensions,p.decode_canonicalFor,hp⟩

instance {α : Type} [Finite α] (bound : Nat) : Finite (BoundedList α bound) :=
  Finite.of_surjective
    (fun p : (n : Fin (bound + 1)) × (Fin n.val → α) => (⟨p.1,p.2⟩ : BoundedList α bound))
    (fun ⟨n,v⟩ => ⟨⟨n,v⟩,rfl⟩)

instance (types modes states : Nat) : Finite (MachineData types modes states) := by
  apply Finite.of_injective (fun d : MachineData types modes states =>
    (d.atoms,d.modes,d.coordinate,d.unitValue,d.creditValue,d.branch,d.range))
  intro a b h
  cases a
  cases b
  simpa only [MachineData.mk.injEq, Prod.mk.injEq] using h

instance (Δ : Bounds) (names : List ModVar) (queries : List CompareTy)
    (states tags observations : Nat) : Finite (Payload Δ names queries states tags observations) := by
  apply Finite.of_injective (fun p : Payload Δ names queries states tags observations =>
    (p.machine,p.embed,p.prodRows,p.sumRows,p.fnRows,p.prodLiterals,p.sumLiterals,p.frozen,p.defined))
  intro a b h
  cases a
  cases b
  simpa only [Payload.mk.injEq, Prod.mk.injEq] using h

instance (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) : Finite (Header Δ raw queries) := by
  apply Finite.of_injective (fun h : Header Δ raw queries => (h.names,h.states,h.tags,h.observations))
  intro a b h
  cases a
  cases b
  simpa only [Header.mk.injEq, Prod.mk.injEq] using h

instance (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) : Finite (Certificate Δ raw queries) :=
  Finite.of_surjective
    (fun p : (h : Header Δ raw queries) × Payload Δ h.decodeNames (endpoints raw queries)
      h.states.val h.tags.val h.observations.val => (⟨p.1,p.2⟩ : Certificate Δ raw queries))
    (fun ⟨h,p⟩ => ⟨⟨h,p⟩,rfl⟩)

end ModalityInference.ComparisonFiniteCertificate.Packed
