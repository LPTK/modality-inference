import ModalityInference.ComparisonFiniteCertificateRestriction
import ModalityInference.Proofs.ComparisonExecutableSyntaxSupport

/-! Restriction to query-derived keys preserves every supplied evaluation and
the original bound checks. Retained rows keep their checked invariants. -/
namespace ModalityInference.ComparisonFiniteCertificate

open ComparisonExecutableSyntax

theorem boundQueries_left {Δ : Bounds} {a b : Ty} (h : .sub a b ∈ Δ) :
    (.ofTy a, none) ∈ boundQueries Δ :=
  List.mem_flatMap.mpr ⟨.sub a b, h, by simp⟩

theorem boundQueries_right {Δ : Bounds} {a b : Ty} (h : .sub a b ∈ Δ) :
    (.ofTy b, none) ∈ boundQueries Δ :=
  List.mem_flatMap.mpr ⟨.sub a b, h, by simp⟩

namespace Candidate

variable {Δ : Bounds} {names : List ModVar} (C : Candidate Δ names)
  (queries : List (CompareTy × Option ModExpr))

theorem restrictQueries_agreement :
    AccessAgreement (C.restrictQueries queries).data C.data (queryAccesses Δ queries) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · intro p hp
    cases p with
    | none => rfl
    | some p =>
      simp only [data, prodAt, restrictQueries, literalRows,
        selectRows_find _ _ (prod_mem_literalPrefixes hp)]
      rfl
  · intro p hp
    cases p with
    | none => rfl
    | some p =>
      simp only [data, sumAt, restrictQueries, literalRows,
        selectRows_find _ _ (sum_mem_literalPrefixes hp)]
      rfl
  · intro a ha
    simp only [Data.frozenValue, data, restrictQueries,
      selectRows_find _ _ (frozen_mem_frozenKeys ha)]

theorem restrictQueries_eval_eq {a : CompareTy} {p : Option ModExpr}
    (ha : (a,p) ∈ boundQueries Δ ++ queries) :
    (C.restrictQueries queries).data.eval a p = C.data.eval a p :=
  (C.restrictQueries_agreement queries).eval_eq a p (accesses_subset_accessList _ ha)

theorem restrictQueries_prodLiterals_length_le :
    (C.restrictQueries queries).prodLiterals.length ≤
      (literalPrefixes (queryAccesses Δ queries)).length := selectRows_length_le _ _

theorem restrictQueries_sumLiterals_length_le :
    (C.restrictQueries queries).sumLiterals.length ≤
      (literalPrefixes (queryAccesses Δ queries)).length := selectRows_length_le _ _

theorem restrictQueries_frozen_length_le :
    (C.restrictQueries queries).frozen.length ≤
      (frozenKeys (queryAccesses Δ queries)).length := selectRows_length_le _ _

theorem restrictQueries_prodLiterals_key_mem {row}
    (hrow : row ∈ (C.restrictQueries queries).prodLiterals) :
    row.1 ∈ literalPrefixes (queryAccesses Δ queries) := selectRows_key_mem _ _ hrow

theorem restrictQueries_sumLiterals_key_mem {row}
    (hrow : row ∈ (C.restrictQueries queries).sumLiterals) :
    row.1 ∈ literalPrefixes (queryAccesses Δ queries) := selectRows_key_mem _ _ hrow

theorem restrictQueries_frozen_key_mem {row}
    (hrow : row ∈ (C.restrictQueries queries).frozen) :
    row.1 ∈ frozenKeys (queryAccesses Δ queries) := selectRows_key_mem _ _ hrow

theorem restrictQueries_boundsCheck :
    (C.restrictQueries queries).boundsCheck = C.boundsCheck := by
  apply Bool.eq_iff_iff.mpr
  simp only [boundsCheck, List.all_eq_true]
  apply forall_congr' fun c => imp_congr_right fun hc => ?_
  cases c with
  | sub a b =>
    have ha := C.restrictQueries_eval_eq queries (List.mem_append_left _ (boundQueries_left hc))
    have hb := C.restrictQueries_eval_eq queries (List.mem_append_left _ (boundQueries_right hc))
    simp only [Data.evalRaw, ha, hb]
    rfl
  | mode | defined | equal | equiv => rfl

theorem restrictQueries_tablesCheck (h : C.tablesCheck = true) :
    (C.restrictQueries queries).tablesCheck = true := by
  simp only [tablesCheck, Bool.and_eq_true] at h ⊢
  refine ⟨⟨h.1.1, ?_⟩, ?_⟩
  · exact List.all_eq_true.mpr fun row hrow =>
      List.all_eq_true.mp h.1.2 row (selectRows_subset _ _ hrow)
  · exact List.all_eq_true.mpr fun row hrow =>
      List.all_eq_true.mp h.2 row (selectRows_subset _ _ hrow)

theorem restrictQueries_structureCheck (h : C.structureCheck = true) :
    (C.restrictQueries queries).structureCheck = true := by
  simp only [structureCheck, Bool.and_eq_true] at h ⊢
  refine ⟨⟨⟨h.1.1.1, C.restrictQueries_tablesCheck queries h.1.1.2⟩, h.1.2⟩, ?_⟩
  exact List.all_eq_true.mpr fun row hrow =>
    List.all_eq_true.mp h.2 row (selectRows_subset _ _ hrow)

theorem restrictQueries_check (h : C.check = true) :
    (C.restrictQueries queries).check = true := by
  simp only [check, Bool.and_eq_true] at h ⊢
  exact ⟨C.restrictQueries_structureCheck queries h.1,
    (C.restrictQueries_boundsCheck queries).trans h.2⟩

theorem restrictQueries_separates {a b : CompareTy}
    (ha : (a,none) ∈ queries) (hb : (b,none) ∈ queries) (h : C.separates a b = true) :
    (C.restrictQueries queries).separates a b = true := by
  simp only [separates, Bool.and_eq_true] at h ⊢
  refine ⟨C.restrictQueries_check queries h.1, ?_⟩
  rw [C.restrictQueries_eval_eq queries (List.mem_append_right _ ha),
    C.restrictQueries_eval_eq queries (List.mem_append_right _ hb)]
  exact h.2

end Candidate
end ModalityInference.ComparisonFiniteCertificate
