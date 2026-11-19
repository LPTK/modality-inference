import ModalityInference.Proofs.ComparisonRawCarrierInterpretation
import ModalityInference.Proofs.ComparisonRawCarrierMaps

/-! Structural transport through carrier ideals. Finite covers are factored
using carrier joins and meets, without distributing over partial operands. -/
namespace ModalityInference.ComparisonRawCarrierRestriction

open ComparisonRawCarrierIdeals

noncomputable section
attribute [local instance] Classical.propDecidable

theorem modal_lower_iff {Δ K a m t} (hm : Entails Δ (.defined m)) :
    (denote Δ K (.modal a m)).lower.mem t ↔
      ∃ b, (denote Δ K a).lower.mem b ∧ Derivation Δ K t (.modal b m) := by
  simpa only [denote,if_pos hm,LowerIdeal.extend,modalMap] using
    (denote Δ K a).lower.extend_iff (core Δ K) (modalMap Δ K m hm) t

theorem modal_upper_iff {Δ K a m t} (hm : Entails Δ (.defined m)) :
    (denote Δ K (.modal a m)).upper.mem t ↔
      ∃ b, (denote Δ K a).upper.mem b ∧ Derivation Δ K (.modal b m) t := by
  simpa only [denote,if_pos hm,UpperIdeal.extend,modalMap] using
    (denote Δ K a).upper.extend_iff (core Δ K) (modalMap Δ K m hm) t

theorem modal_lower_mem {Δ K a m t} (hm : Entails Δ (.defined m))
    (ht : (denote Δ K a).lower.mem t) : (denote Δ K (.modal a m)).lower.mem (.modal t m) :=
  (modal_lower_iff hm).mpr ⟨t,ht,.refl
    ((carrier_modal_total hm).mpr ((denote Δ K a).lower.carrier ht))
    ((denote Δ K a).lower.shaped (a := t) ht)⟩

theorem modal_upper_mem {Δ K a m t} (hm : Entails Δ (.defined m))
    (ht : (denote Δ K a).upper.mem t) : (denote Δ K (.modal a m)).upper.mem (.modal t m) :=
  (modal_upper_iff hm).mpr ⟨t,ht,.refl
    ((carrier_modal_total hm).mpr ((denote Δ K a).upper.carrier ht))
    ((denote Δ K a).upper.shaped (a := t) ht)⟩

theorem prod_lower_factor {Δ K a b t} (ht : (denote Δ K (.prod a b)).lower.mem t) :
    ∃ x y, (denote Δ K a).lower.mem x ∧ (denote Δ K b).lower.mem y ∧
      Derivation Δ K t (.prod x y) :=
  LowerClosure.factor₂ (core Δ K) ((denote Δ K a).lower.family (core Δ K))
    ((denote Δ K b).lower.family (core Δ K)) (prodMap Δ K) ht

theorem prod_upper_factor {Δ K a b t} (ht : (denote Δ K (.prod a b)).upper.mem t) :
    ∃ x y, (denote Δ K a).upper.mem x ∧ (denote Δ K b).upper.mem y ∧
      Derivation Δ K (.prod x y) t :=
  UpperClosure.factor₂ (core Δ K) (p := false) (q := false) ((denote Δ K a).upper.family (core Δ K))
    ((denote Δ K b).upper.family (core Δ K)) (prodMap Δ K) ht

theorem prod_lower_mem {Δ K a b x y}
    (hx : (denote Δ K a).lower.mem x) (hy : (denote Δ K b).lower.mem y) :
    (denote Δ K (.prod a b)).lower.mem (.prod x y) :=
  .base (carrier_prod.mpr ⟨(denote Δ K a).lower.carrier hx,(denote Δ K b).lower.carrier hy⟩)
    ⟨(denote Δ K a).lower.shaped hx,(denote Δ K b).lower.shaped hy⟩ ⟨x,y,hx,hy,rfl⟩

theorem prod_upper_mem {Δ K a b x y}
    (hx : (denote Δ K a).upper.mem x) (hy : (denote Δ K b).upper.mem y) :
    (denote Δ K (.prod a b)).upper.mem (.prod x y) :=
  .base (carrier_prod.mpr ⟨(denote Δ K a).upper.carrier hx,(denote Δ K b).upper.carrier hy⟩)
    ⟨(denote Δ K a).upper.shaped hx,(denote Δ K b).upper.shaped hy⟩ ⟨x,y,hx,hy,rfl⟩

theorem sum_lower_factor {Δ K a b t} (ht : (denote Δ K (.sum a b)).lower.mem t) :
    ∃ x y, (denote Δ K a).lower.mem x ∧ (denote Δ K b).lower.mem y ∧
      Derivation Δ K t (.sum x y) :=
  LowerClosure.factor₂ (core Δ K) ((denote Δ K a).lower.family (core Δ K))
    ((denote Δ K b).lower.family (core Δ K)) (sumMap Δ K) ht

theorem sum_upper_factor {Δ K a b t} (ht : (denote Δ K (.sum a b)).upper.mem t) :
    ∃ x y, (denote Δ K a).upper.mem x ∧ (denote Δ K b).upper.mem y ∧
      Derivation Δ K (.sum x y) t :=
  UpperClosure.factor₂ (core Δ K) (p := false) (q := false) ((denote Δ K a).upper.family (core Δ K))
    ((denote Δ K b).upper.family (core Δ K)) (sumMap Δ K) ht

theorem sum_lower_mem {Δ K a b x y}
    (hx : (denote Δ K a).lower.mem x) (hy : (denote Δ K b).lower.mem y) :
    (denote Δ K (.sum a b)).lower.mem (.sum x y) :=
  .base (carrier_sum.mpr ⟨(denote Δ K a).lower.carrier hx,(denote Δ K b).lower.carrier hy⟩)
    ⟨(denote Δ K a).lower.shaped hx,(denote Δ K b).lower.shaped hy⟩ ⟨x,y,hx,hy,rfl⟩

theorem sum_upper_mem {Δ K a b x y}
    (hx : (denote Δ K a).upper.mem x) (hy : (denote Δ K b).upper.mem y) :
    (denote Δ K (.sum a b)).upper.mem (.sum x y) :=
  .base (carrier_sum.mpr ⟨(denote Δ K a).upper.carrier hx,(denote Δ K b).upper.carrier hy⟩)
    ⟨(denote Δ K a).upper.shaped hx,(denote Δ K b).upper.shaped hy⟩ ⟨x,y,hx,hy,rfl⟩

theorem Related.prod_total {Δ K a b c d m} (hm : Entails Δ (.defined m))
    (hac : Related Δ K (.modal a m) (.modal c m))
    (hbd : Related Δ K (.modal b m) (.modal d m)) :
    Related Δ K (.modal (.prod a b) m) (.modal (.prod c d) m) := by
  constructor
  · intro t ht
    obtain ⟨p,hp,htp⟩ := (modal_lower_iff hm).mp ht
    obtain ⟨x,y,hx,hy,hpxy⟩ := prod_lower_factor hp
    obtain ⟨u,hu,hxu⟩ := (modal_lower_iff hm).mp (hac.1 _ (modal_lower_mem hm hx))
    obtain ⟨v,hv,hyv⟩ := (modal_lower_iff hm).mp (hbd.1 _ (modal_lower_mem hm hy))
    exact (denote Δ K (.modal (.prod c d) m)).lower.lower
      (htp.trans ((hpxy.congr (.refl hm)).trans (.prod hxu hyv)))
      (modal_lower_mem hm (prod_lower_mem hu hv))
  · intro t ht
    obtain ⟨p,hp,hpt⟩ := (modal_upper_iff hm).mp ht
    obtain ⟨x,y,hx,hy,hxyp⟩ := prod_upper_factor hp
    obtain ⟨u,hu,hux⟩ := (modal_upper_iff hm).mp (hac.2 _ (modal_upper_mem hm hx))
    obtain ⟨v,hv,hvy⟩ := (modal_upper_iff hm).mp (hbd.2 _ (modal_upper_mem hm hy))
    exact (denote Δ K (.modal (.prod a b) m)).upper.upper
      ((Derivation.prod hux hvy).trans ((hxyp.congr (.refl hm)).trans hpt))
      (modal_upper_mem hm (prod_upper_mem hu hv))

theorem Related.sum_total {Δ K a b c d m} (hm : Entails Δ (.defined m))
    (hac : Related Δ K (.modal a m) (.modal c m))
    (hbd : Related Δ K (.modal b m) (.modal d m)) :
    Related Δ K (.modal (.sum a b) m) (.modal (.sum c d) m) := by
  constructor
  · intro t ht
    obtain ⟨p,hp,htp⟩ := (modal_lower_iff hm).mp ht
    obtain ⟨x,y,hx,hy,hpxy⟩ := sum_lower_factor hp
    obtain ⟨u,hu,hxu⟩ := (modal_lower_iff hm).mp (hac.1 _ (modal_lower_mem hm hx))
    obtain ⟨v,hv,hyv⟩ := (modal_lower_iff hm).mp (hbd.1 _ (modal_lower_mem hm hy))
    exact (denote Δ K (.modal (.sum c d) m)).lower.lower
      (htp.trans ((hpxy.congr (.refl hm)).trans (.sum hxu hyv)))
      (modal_lower_mem hm (sum_lower_mem hu hv))
  · intro t ht
    obtain ⟨p,hp,hpt⟩ := (modal_upper_iff hm).mp ht
    obtain ⟨x,y,hx,hy,hxyp⟩ := sum_upper_factor hp
    obtain ⟨u,hu,hux⟩ := (modal_upper_iff hm).mp (hac.2 _ (modal_upper_mem hm hx))
    obtain ⟨v,hv,hvy⟩ := (modal_upper_iff hm).mp (hbd.2 _ (modal_upper_mem hm hy))
    exact (denote Δ K (.modal (.sum a b) m)).upper.upper
      ((Derivation.sum hux hvy).trans ((hxyp.congr (.refl hm)).trans hpt))
      (modal_upper_mem hm (sum_upper_mem hu hv))

theorem fn_lower_factor {Δ K a b t} (ht : (denote Δ K (.fn a b)).lower.mem t) :
    ∃ x y, (denote Δ K a).upper.mem x ∧ (denote Δ K b).lower.mem y ∧
      Derivation Δ K t (.fn x y) :=
  LowerClosure.factor₂ (core Δ K) ((denote Δ K a).upper.family (core Δ K))
    ((denote Δ K b).lower.family (core Δ K)) (fnMap Δ K) ht

theorem fn_upper_factor {Δ K a b t} (ht : (denote Δ K (.fn a b)).upper.mem t) :
    ∃ x y, (denote Δ K a).lower.mem x ∧ (denote Δ K b).upper.mem y ∧
      Derivation Δ K (.fn x y) t :=
  UpperClosure.factor₂ (core Δ K) (p := true) (q := false)
    ((denote Δ K a).lower.family (core Δ K))
    ((denote Δ K b).upper.family (core Δ K)) (fnMap Δ K) ht

theorem fn_lower_mem {Δ K a b x y}
    (hx : (denote Δ K a).upper.mem x) (hy : (denote Δ K b).lower.mem y) :
    (denote Δ K (.fn a b)).lower.mem (.fn x y) :=
  .base (carrier_fn.mpr ⟨(denote Δ K a).upper.carrier hx,(denote Δ K b).lower.carrier hy⟩)
    ⟨(denote Δ K a).upper.shaped hx,(denote Δ K b).lower.shaped hy⟩ ⟨x,y,hx,hy,rfl⟩

theorem fn_upper_mem {Δ K a b x y}
    (hx : (denote Δ K a).lower.mem x) (hy : (denote Δ K b).upper.mem y) :
    (denote Δ K (.fn a b)).upper.mem (.fn x y) :=
  .base (carrier_fn.mpr ⟨(denote Δ K a).lower.carrier hx,(denote Δ K b).upper.carrier hy⟩)
    ⟨(denote Δ K a).lower.shaped hx,(denote Δ K b).upper.shaped hy⟩ ⟨x,y,hx,hy,rfl⟩

theorem Related.fn {Δ K a b c d m n}
    (hca : Related Δ K c a) (hbd : Related Δ K b d)
    (hmn : Submode Δ m (.compose n .top)) :
    Related Δ K (.modal (.fn a b) m) (.modal (.fn c d) n) := by
  have hm := hmn.defined.1
  have hn := (Entails.defined_compose_iff.mp hmn.defined.2).1
  constructor
  · intro t ht
    obtain ⟨p,hp,htp⟩ := (modal_lower_iff hm).mp ht
    obtain ⟨x,y,hx,hy,hpxy⟩ := fn_lower_factor hp
    have hxx := Derivation.refl ((denote Δ K a).upper.carrier hx) ((denote Δ K a).upper.shaped hx)
    have hyy := Derivation.refl ((denote Δ K b).lower.carrier hy) ((denote Δ K b).lower.shaped hy)
    exact (denote Δ K (.modal (.fn c d) n)).lower.lower
      (htp.trans ((hpxy.congr (.refl hm)).trans (.fn hxx hyy hmn)))
      (modal_lower_mem hn (fn_lower_mem (hca.2 _ hx) (hbd.1 _ hy)))
  · intro t ht
    obtain ⟨p,hp,hpt⟩ := (modal_upper_iff hn).mp ht
    obtain ⟨x,y,hx,hy,hxyp⟩ := fn_upper_factor hp
    have hxx := Derivation.refl ((denote Δ K c).lower.carrier hx) ((denote Δ K c).lower.shaped hx)
    have hyy := Derivation.refl ((denote Δ K d).upper.carrier hy) ((denote Δ K d).upper.shaped hy)
    exact (denote Δ K (.modal (.fn a b) m)).upper.upper
      ((Derivation.fn hxx hyy hmn).trans ((hxyp.congr (.refl hn)).trans hpt))
      (modal_upper_mem hm (fn_upper_mem (hca.1 _ hx) (hbd.2 _ hy)))

theorem Related.congr {Δ K a b m n}
    (hab : Related Δ K a b) (hmn : Submode Δ m n) :
    Related Δ K (.modal a m) (.modal b n) := by
  have hm := hmn.defined.1
  have hn := hmn.defined.2
  constructor
  · intro t ht
    obtain ⟨x,hx,htx⟩ := (modal_lower_iff hm).mp ht
    have hxx := Derivation.refl ((denote Δ K a).lower.carrier hx) ((denote Δ K a).lower.shaped hx)
    exact (denote Δ K (.modal b n)).lower.lower (htx.trans (.congr hxx hmn))
      (modal_lower_mem hn (hab.1 _ hx))
  · intro t ht
    obtain ⟨x,hx,hxt⟩ := (modal_upper_iff hn).mp ht
    have hxx := Derivation.refl ((denote Δ K b).upper.carrier hx) ((denote Δ K b).upper.shaped hx)
    exact (denote Δ K (.modal a m)).upper.upper ((Derivation.congr hxx hmn).trans hxt)
      (modal_upper_mem hm (hab.2 _ hx))

end
end ModalityInference.ComparisonRawCarrierRestriction
