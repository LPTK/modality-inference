import ModalityInference.ComparisonFiniteCertificateDense
import ModalityInference.Proofs.ComparisonFiniteCertificateRows
import ModalityInference.Proofs.ComparisonFiniteCertificateRestriction

/-! Completing input-key tables preserves accepted certificates and the
evaluations supported by the original bounds and supplied endpoints. -/
namespace ModalityInference.ComparisonFiniteCertificate

open ComparisonExecutableSyntax ComparisonFiniteControlEncoding ComparisonExecutableTables

theorem dense_find {α β : Type*} [DecidableEq α] (keys : List α) (value : α → β) (key : α) :
    (keys.map fun a => (a,value a)).find? (fun row => decide (row.1 = key)) =
      if key ∈ keys then some (key,value key) else none := by
  induction keys with
  | nil => rfl
  | cons a keys ih =>
    by_cases h : a = key
    · simp only [h, List.map_cons, List.find?_cons, decide_true, List.mem_cons_self, if_pos]
    · simp only [List.map_cons, List.find?_cons, h, decide_false,
        List.mem_cons, Ne.symm h, false_or, ih]

theorem find_outside_keys {α β : Type*} [DecidableEq α] (keys : List α) (rows : List (α × β))
    (hkeys : ∀ row ∈ rows, row.1 ∈ keys) {key : α} (hk : key ∉ keys) :
    rows.find? (fun row => decide (row.1 = key)) = none := by
  cases hf : rows.find? (fun row => decide (row.1 = key)) with
  | none => rfl
  | some row =>
    exact False.elim (hk ((of_decide_eq_true (List.find?_some
      (p := fun row : α × β => decide (row.1 = key)) hf)) ▸
        hkeys row (List.mem_of_find?_eq_some hf)))

theorem dense_literalRows {Δ : Bounds} {names : List ModVar} {tags : Nat}
    (keys : List ModExpr) (ordinary : List (Row (Code Δ names) (Fin tags)))
    (literals : List (ModExpr × List (Row (Code Δ names) (Fin tags))))
    (hkeys : ∀ row ∈ literals, row.1 ∈ keys) (p : Option ModExpr) :
    literalRows (canonicalRows ordinary)
      (keys.map fun m => (m, canonicalRows (literalRows ordinary literals (some m)))) p =
        canonicalRows (literalRows ordinary literals p) := by
  cases p with
  | none => rfl
  | some p =>
    by_cases hp : p ∈ keys
    · simp only [literalRows, dense_find, hp, if_pos, Option.map_some, Option.getD_some]
    · simp only [literalRows, dense_find, hp, if_false, find_outside_keys keys literals hkeys hp,
        Option.map_none, Option.getD_none, canonicalRows_nil]

theorem dense_frozenValue {M V : Type*} (E : Data M V) (keys : List CompareTy)
    (hkeys : ∀ row ∈ E.frozen, row.1 ∈ keys) (a : CompareTy) :
    (((keys.map fun key => (key,E.frozenValue key)).find?
      (fun row => decide (row.1 = a))).map Prod.snd).getD E.bottom = E.frozenValue a := by
  by_cases ha : a ∈ keys
  · simp only [dense_find, ha, if_pos, Option.map_some, Option.getD_some]
  · simp only [dense_find, ha, if_false, Option.map_none, Option.getD_none, Data.frozenValue,
      find_outside_keys keys E.frozen hkeys ha]

namespace Candidate

variable {Δ : Bounds} {names : List ModVar} (C : Candidate Δ names) (queries : List CompareTy)

theorem densify_pair (rows : List (Row (Code Δ names) (Fin C.tags))) :
    (C.densify queries).pair (canonicalRows rows) = C.pair rows :=
  C.canonicalizeRows_pair rows

theorem densify_function : (C.densify queries).function = C.function := C.canonicalizeRows_function

theorem densify_prodAt {p : ModExpr} (hp : p ∈ retainedPrefixes Δ queries) :
    (C.densify queries).prodAt (some p) = canonicalRows (C.prodAt (some p)) := by
  simp only [prodAt, densify, literalRows, dense_find, hp, if_pos, Option.map_some, Option.getD_some]

theorem densify_sumAt {p : ModExpr} (hp : p ∈ retainedPrefixes Δ queries) :
    (C.densify queries).sumAt (some p) = canonicalRows (C.sumAt (some p)) := by
  simp only [sumAt, densify, literalRows, dense_find, hp, if_pos, Option.map_some, Option.getD_some]

theorem densify_frozenValue {a : CompareTy} (ha : a ∈ retainedFrozen Δ queries) :
    (C.densify queries).data.frozenValue a = C.data.frozenValue a := by
  simp only [Data.frozenValue, data, densify, dense_find, ha, if_pos, Option.map_some, Option.getD_some]

theorem densify_agreement :
    AccessAgreement (C.densify queries).data C.data (queryAccesses Δ (queryPairs queries)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, C.densify_function queries, rfl, rfl, rfl, rfl, rfl,
    fun _ h => C.densify_frozenValue queries (frozen_mem_frozenKeys h)⟩
  · exact fun p hp => match p, hp with
    | none, _ => C.densify_pair queries C.prodRows
    | some p, hp => (congrArg (C.densify queries).pair
        (C.densify_prodAt queries (prod_mem_literalPrefixes hp))).trans (C.densify_pair queries _)
  · exact fun p hp => match p, hp with
    | none, _ => C.densify_pair queries C.sumRows
    | some p, hp => (congrArg (C.densify queries).pair
        (C.densify_sumAt queries (sum_mem_literalPrefixes hp))).trans (C.densify_pair queries _)

theorem densify_eval_eq {a : CompareTy} {p : Option ModExpr}
    (ha : (a,p) ∈ boundQueries Δ ++ queryPairs queries) :
    (C.densify queries).data.eval a p = C.data.eval a p :=
  (C.densify_agreement queries).eval_eq a p (accesses_subset_accessList _ ha)

theorem densify_operations : (C.densify queries).operations = C.operations :=
  C.canonicalizeRows_operations

theorem densify_embeddingCheck : (C.densify queries).embeddingCheck = C.embeddingCheck :=
  C.canonicalizeRows_embeddingCheck

omit queries in
theorem frozenValue_monotoneCheck (h : C.structureCheck = true) (a : CompareTy) :
    C.monotoneCheck (C.data.frozenValue a) = true := by
  simp only [Data.frozenValue, data]
  cases hf : C.frozen.find? (fun row => decide (row.1 = a)) with
  | none => exact (C.monotoneCheck_correct _).mpr (fun _ _ _ => le_rfl)
  | some row => exact C.frozen_valid h (List.mem_of_find?_eq_some hf)

theorem densify_tablesCheck (h : C.structureCheck = true) :
    (C.densify queries).tablesCheck = true := by
  simp only [tablesCheck, densify, canonicalRows_check, List.all_map, Function.comp_def,
    List.all_eq_true, Bool.and_eq_true, and_assoc]
  exact ⟨(C.table_checks h).1, (C.table_checks h).2.1, C.fn_valid h,
    fun p _ => C.prodAt_valid h (some p), fun p _ => C.sumAt_valid h (some p)⟩

theorem densify_frozenCheck (h : C.structureCheck = true) :
    (C.densify queries).frozen.all (fun row => (C.densify queries).monotoneCheck row.2) = true := by
  simpa only [densify, List.all_map, Function.comp_def, List.all_eq_true] using
    (fun a (_ : a ∈ retainedFrozen Δ queries) => C.frozenValue_monotoneCheck h a)

theorem densify_structureCheck (h : C.structureCheck = true) :
    (C.densify queries).structureCheck = true := by
  have ht := C.densify_tablesCheck queries h
  have hf := C.densify_frozenCheck queries h
  simp only [structureCheck, Bool.and_eq_true] at h ⊢
  exact ⟨⟨⟨h.1.1.1, ht⟩, (C.densify_embeddingCheck queries).trans h.1.2⟩, hf⟩

theorem densify_boundsCheck : (C.densify queries).boundsCheck = C.boundsCheck := by
  apply Bool.eq_iff_iff.mpr
  simp only [boundsCheck, List.all_eq_true]
  apply forall_congr' fun c => imp_congr_right fun hc => ?_
  cases c with
  | sub a b =>
    simp only [Data.evalRaw,
      C.densify_eval_eq queries (List.mem_append_left _ (boundQueries_left hc)),
      C.densify_eval_eq queries (List.mem_append_left _ (boundQueries_right hc))]
    rfl
  | mode | defined | equal | equiv => rfl

theorem densify_check (h : C.check = true) : (C.densify queries).check = true :=
  Bool.and_eq_true_iff.mpr ⟨C.densify_structureCheck queries (Bool.and_eq_true_iff.mp h).1,
    (C.densify_boundsCheck queries).trans (Bool.and_eq_true_iff.mp h).2⟩

theorem densify_endpoint_eval {a : CompareTy} (ha : a ∈ queries) :
    (C.densify queries).data.eval a none = C.data.eval a none :=
  C.densify_eval_eq queries (List.mem_append_right _ (List.mem_map.mpr ⟨a,ha,rfl⟩))

theorem densify_separates {a b : CompareTy} (ha : a ∈ queries) (hb : b ∈ queries)
    (h : C.separates a b = true) : (C.densify queries).separates a b = true := by
  simp only [separates, Bool.and_eq_true] at h ⊢
  simpa only [C.densify_endpoint_eval queries ha, C.densify_endpoint_eval queries hb] using
    And.intro (C.densify_check queries h.1) h.2

theorem densify_prodAt_all (h : CanonicalFor queries C) (p : Option ModExpr) :
    (C.densify queries).prodAt p = canonicalRows (C.prodAt p) :=
  dense_literalRows (retainedPrefixes Δ queries) C.prodRows C.prodLiterals h.prodLiterals_keys p

theorem densify_sumAt_all (h : CanonicalFor queries C) (p : Option ModExpr) :
    (C.densify queries).sumAt p = canonicalRows (C.sumAt p) :=
  dense_literalRows (retainedPrefixes Δ queries) C.sumRows C.sumLiterals h.sumLiterals_keys p

theorem densify_frozenValue_all (h : CanonicalFor queries C) (a : CompareTy) :
    (C.densify queries).data.frozenValue a = C.data.frozenValue a :=
  dense_frozenValue C.data (retainedFrozen Δ queries) h.frozen_keys a

theorem densify_agreement_all (h : CanonicalFor queries C) (keys : List Access) :
    AccessAgreement (C.densify queries).data C.data keys :=
  ⟨rfl, rfl, rfl,
    (fun p _ => (congrArg (C.densify queries).pair (C.densify_prodAt_all queries h p)).trans
      (C.densify_pair queries _)),
    (fun p _ => (congrArg (C.densify queries).pair (C.densify_sumAt_all queries h p)).trans
      (C.densify_pair queries _)),
    C.densify_function queries, rfl, rfl, rfl, rfl, rfl,
    fun a _ => C.densify_frozenValue_all queries h a⟩

theorem densify_eval_all (h : CanonicalFor queries C) (a : CompareTy) (p : Option ModExpr) :
    (C.densify queries).data.eval a p = C.data.eval a p :=
  (C.densify_agreement_all queries h _).eval_eq a p (fun _ ha => ha)

end Candidate
end ModalityInference.ComparisonFiniteCertificate
