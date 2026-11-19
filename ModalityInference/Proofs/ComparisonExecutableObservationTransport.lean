import ModalityInference.Proofs.ComparisonExecutableCoordinates
import ModalityInference.Proofs.ComparisonRelativeSyntax

/-! Renaming tags and observations preserves the entire syntax interpretation.
This allows finite semantic carriers to be represented by ordinary indices. -/
namespace ModalityInference.ComparisonExecutableObservationTransport

open ComparisonRelativeSyntax ComparisonRelativeCoordinates ComparisonRawCarrierSuffix
  ComparisonExecutableTableTransport

noncomputable section

variable {Δ : Bounds} {M A B O Q : Type*} [PartialOrder M] [CommMonoid M]
  {embed : A → O → Bool} (S : Model Δ M A O embed) (ea : B ≃ A) (eo : Q ≃ O)

def transport : Model Δ M B Q (fun b => pull eo (embed (ea b))) where
  mul_mono := S.mul_mono
  prodTable p := ComparisonExecutableTableTransport.transport (S.prodTable p) (Equiv.refl M) ea eo
  prod_order p := S.prod_order p
  sumTable p := ComparisonExecutableTableTransport.transport (S.sumTable p) (Equiv.refl M) ea eo
  sum_order p := S.sum_order p
  fnTable := ComparisonExecutableTableTransport.transport S.fnTable (Equiv.refl M) ea eo
  fn_order := S.fn_order
  fn_post := S.fn_post
  controls := S.controls
  atom v := coordinates (OrderIso.refl M) eo (S.atom v)
  unit := coordinates (OrderIso.refl M) eo S.unit
  credit := coordinates (OrderIso.refl M) eo S.credit
  frozen := S.frozen.map fun row => (row.1,coordinates (OrderIso.refl M) eo row.2)

theorem frozenValue (a : CompareTy) :
    (transport S ea eo).frozenValue a = coordinates (OrderIso.refl M) eo (S.frozenValue a) := by
  simp only [Model.frozenValue,transport,List.find?_map,Function.comp_def]
  cases S.frozen.find? (fun row => decide (row.1 = a)) <;> rfl

theorem denote (a : CompareTy) (p : Option ModExpr) :
    (transport S ea eo).denote a p = coordinates (OrderIso.refl M) eo (S.denote a p) := by
  induction a generalizing p with
  | modal a m ih =>
    cases p with
    | some p => exact ih (some (.compose m p))
    | none =>
      simp only [Model.denote,ih]
      exact (coordinates_shift S.mul_mono S.mul_mono (OrderIso.refl M) (fun _ _ => rfl) eo
        (S.controls.toFun (normalize Δ m).control (control_total Δ m))
        (S.denote a (normalize Δ m).literal)).symm
  | var v => cases p <;> first | rfl | exact frozenValue S ea eo _
  | unit => cases p <;> first | rfl | exact frozenValue S ea eo _
  | credit => cases p <;> first | rfl | exact frozenValue S ea eo _
  | prod a b iha ihb =>
    simpa only [Model.denote,iha,ihb] using coordinates_pair (S.prodTable p) (S.prod_order p)
      (OrderIso.refl M) ea eo (S.denote a p) (S.denote b p)
  | sum a b iha ihb =>
    simpa only [Model.denote,iha,ihb] using coordinates_pair (S.sumTable p) (S.sum_order p)
      (OrderIso.refl M) ea eo (S.denote a p) (S.denote b p)
  | fn a b iha ihb =>
    cases p with
    | some p => exact frozenValue S ea eo _
    | none =>
      simpa only [Model.denote,iha,ihb] using coordinates_fn S.fnTable S.fn_order
        (OrderIso.refl M) rfl ea eo (S.denote a none) (S.denote b none)
  | join a b iha ihb =>
    cases p with
    | some p => exact frozenValue S ea eo _
    | none =>
      simpa only [Model.denote,iha,ihb] using
        (map_sup (coordinates (OrderIso.refl M) eo) (S.denote a none) (S.denote b none)).symm
  | meet a b iha ihb =>
    cases p with
    | some p => exact frozenValue S ea eo _
    | none =>
      simpa only [Model.denote,iha,ihb] using
        (map_inf (coordinates (OrderIso.refl M) eo) (S.denote a none) (S.denote b none)).symm

theorem related_iff (a b : CompareTy) : (transport S ea eo).Related a b ↔ S.Related a b := by
  change (transport S ea eo).denote a none ≤ (transport S ea eo).denote b none ↔ _
  rw [denote,denote]
  exact coordinates_le_iff (OrderIso.refl M) eo _ _

end
end ModalityInference.ComparisonExecutableObservationTransport
