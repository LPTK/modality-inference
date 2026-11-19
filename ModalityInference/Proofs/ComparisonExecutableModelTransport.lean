import ModalityInference.Proofs.ComparisonExecutableCoordinates
import ModalityInference.Proofs.ComparisonRelativeSyntax

/-! A complete syntax model can be renamed along an ordered monoid equivalence.
Literal prefixes and frozen-key selection remain unchanged. -/
namespace ModalityInference.ComparisonExecutableModelTransport

open ComparisonRelativeSyntax ComparisonRelativeCoordinates ComparisonRawCarrierSuffix
  ComparisonExecutableTableTransport

noncomputable section

variable {Δ : Bounds} {M N A O : Type*}
  [PartialOrder M] [CommMonoid M] [PartialOrder N] [CommMonoid N]
  {embed : A → O → Bool} (S : Model Δ M A O embed)
  (em : N ≃o M) (hone : em 1 = 1) (hmul : ∀ m n, em (m * n) = em m * em n)

def mul_mono (S : Model Δ M A O embed) (em : N ≃o M)
    (hmul : ∀ m n, em (m * n) = em m * em n) : ∀ n : N, Monotone (n * ·) :=
  fun n _ _ h => em.le_iff_le.mp (by simpa only [hmul] using S.mul_mono (em n) (em.monotone h))

def controls (S : Model Δ M A O embed) (em : N ≃o M)
    (hone : em 1 = 1) (hmul : ∀ m n, em (m * n) = em m * em n) :
    ControlMap Δ N (fun m n => S.fnTable.le (em m) (em n)) where
  toFun m hm := em.symm (S.controls.toFun m hm)
  epsilon := em.injective (by
    simpa only [OrderIso.apply_symm_apply,S.controls.epsilon] using hone.symm)
  compose m n hm hn := em.injective (by
    simpa only [OrderIso.apply_symm_apply,hmul] using S.controls.compose m n hm hn)
  submode h := em.symm.monotone (S.controls.submode h)
  fnorder h := by simpa only [OrderIso.apply_symm_apply] using S.controls.fnorder h

def transport : Model Δ N A O embed where
  mul_mono := mul_mono S em hmul
  prodTable p := ComparisonExecutableTableTransport.transport (S.prodTable p)
    em.toEquiv (Equiv.refl A) (Equiv.refl O)
  prod_order p {_ _} h := S.prod_order p (em.monotone h)
  sumTable p := ComparisonExecutableTableTransport.transport (S.sumTable p)
    em.toEquiv (Equiv.refl A) (Equiv.refl O)
  sum_order p {_ _} h := S.sum_order p (em.monotone h)
  fnTable := ComparisonExecutableTableTransport.transport S.fnTable
    em.toEquiv (Equiv.refl A) (Equiv.refl O)
  fn_order {_ _} h := S.fn_order (em.monotone h)
  fn_post {m n} h r := by
    change S.fnTable.le (em (m * r)) (em (n * r))
    simpa only [hmul] using S.fn_post h (em r)
  controls := controls S em hone hmul
  atom v := coordinates em (Equiv.refl O) (S.atom v)
  unit := coordinates em (Equiv.refl O) S.unit
  credit := coordinates em (Equiv.refl O) S.credit
  frozen := S.frozen.map fun row => (row.1,coordinates em (Equiv.refl O) row.2)

theorem frozenValue (a : CompareTy) :
    (transport S em hone hmul).frozenValue a =
      coordinates em (Equiv.refl O) (S.frozenValue a) := by
  simp only [Model.frozenValue,transport,List.find?_map,Function.comp_def]
  cases S.frozen.find? (fun row => decide (row.1 = a)) <;> rfl

theorem denote (a : CompareTy) (p : Option ModExpr) :
    (transport S em hone hmul).denote a p =
      coordinates em (Equiv.refl O) (S.denote a p) := by
  induction a generalizing p with
  | modal a m ih =>
    cases p with
    | some p => exact ih (some (.compose m p))
    | none =>
      simp only [Model.denote,ih]
      simpa only [OrderIso.apply_symm_apply] using
        (coordinates_shift S.mul_mono (mul_mono S em hmul) em hmul (Equiv.refl O)
          (em.symm (S.controls.toFun (normalize Δ m).control (control_total Δ m)))
          (S.denote a (normalize Δ m).literal)).symm
  | var v => cases p <;> first | rfl | exact frozenValue S em hone hmul _
  | unit => cases p <;> first | rfl | exact frozenValue S em hone hmul _
  | credit => cases p <;> first | rfl | exact frozenValue S em hone hmul _
  | prod a b iha ihb =>
    simpa only [Model.denote,iha,ihb] using coordinates_pair (S.prodTable p) (S.prod_order p)
      em (Equiv.refl A) (Equiv.refl O) (S.denote a p) (S.denote b p)
  | sum a b iha ihb =>
    simpa only [Model.denote,iha,ihb] using coordinates_pair (S.sumTable p) (S.sum_order p)
      em (Equiv.refl A) (Equiv.refl O) (S.denote a p) (S.denote b p)
  | fn a b iha ihb =>
    cases p with
    | some p => exact frozenValue S em hone hmul _
    | none =>
      simpa only [Model.denote,iha,ihb] using coordinates_fn S.fnTable S.fn_order
        em hone (Equiv.refl A) (Equiv.refl O) (S.denote a none) (S.denote b none)
  | join a b iha ihb =>
    cases p with
    | some p => exact frozenValue S em hone hmul _
    | none =>
      simpa only [Model.denote,iha,ihb] using
        (map_sup (coordinates em (Equiv.refl O)) (S.denote a none) (S.denote b none)).symm
  | meet a b iha ihb =>
    cases p with
    | some p => exact frozenValue S em hone hmul _
    | none =>
      simpa only [Model.denote,iha,ihb] using
        (map_inf (coordinates em (Equiv.refl O)) (S.denote a none) (S.denote b none)).symm

theorem denote_le_iff (a b : CompareTy) (p q : Option ModExpr) :
    (transport S em hone hmul).denote a p ≤ (transport S em hone hmul).denote b q ↔
      S.denote a p ≤ S.denote b q := by
  simp only [denote,coordinates_le_iff]

theorem related_iff (a b : CompareTy) :
    (transport S em hone hmul).Related a b ↔ S.Related a b :=
  denote_le_iff S em hone hmul a b none none

@[simp] theorem controls_apply (m : ModExpr) (hm : Entails Δ (.defined m)) :
    (transport S em hone hmul).controls.toFun m hm = em.symm (S.controls.toFun m hm) := rfl

end
end ModalityInference.ComparisonExecutableModelTransport
