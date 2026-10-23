import ModalityInference.Proofs.ComparisonRawHeadSupport
import ModalityInference.Proofs.ComparisonRawHeadFunctions
import ModalityInference.Proofs.ComparisonRawCarrierSuffix
import ModalityInference.Proofs.ComparisonRawCarrierInterpretation

/-! An interpretation over whole partial heads. Constructor tables are sparse;
literal partial prefixes remain syntactic, while the outer total action is an
ordered coordinate. -/
namespace ModalityInference.ComparisonRawHeadRestriction

open ComparisonRawCarrierIdeals ComparisonRawCarrierSuffix
open ComparisonPartialStructuredCapsule
open ComparisonRawCarrierRestriction (TotalIndex lowerInter upperInter)

noncomputable section
attribute [local instance] Classical.propDecidable

structure Interpretation (Δ : Bounds) (H : Set CompareTy) where
  lower : LowerIdeal (core Δ H)
  upper : UpperIdeal (core Δ H)

namespace Interpretation

def principal (Δ : Bounds) (H : Set CompareTy) (a : CompareTy) : Interpretation Δ H :=
  ⟨.principal (core Δ H) a, .principal (core Δ H) a⟩

def Le {Δ H} (S T : Interpretation Δ H) : Prop :=
  (∀ a, S.lower.mem a → T.lower.mem a) ∧ (∀ a, T.upper.mem a → S.upper.mem a)

theorem Le.refl {Δ H} (S : Interpretation Δ H) : S.Le S := ⟨fun _ h => h, fun _ h => h⟩

theorem Le.trans {Δ H S T U} (h : @Le Δ H S T) (h' : T.Le U) : S.Le U :=
  ⟨fun _ ha => h'.1 _ (h.1 _ ha), fun _ ha => h.2 _ (h'.2 _ ha)⟩

def join {Δ H} (S T : Interpretation Δ H) : Interpretation Δ H :=
  ⟨.closure (core Δ H) (fun a => S.lower.mem a ∨ T.lower.mem a),
    upperInter S.upper T.upper⟩

def meet {Δ H} (S T : Interpretation Δ H) : Interpretation Δ H :=
  ⟨lowerInter S.lower T.lower,
    .closure (core Δ H) (fun a => S.upper.mem a ∨ T.upper.mem a)⟩

theorem join_mono {Δ H S S' T T'} (hS : @Le Δ H S S') (hT : T.Le T') :
    (S.join T).Le (S'.join T') := by
  constructor
  · intro a ha
    apply LowerClosure.lift (core Δ H) ha (S'.join T').lower
    intro a ha hc hs
    exact .base hc hs (ha.elim (fun h => Or.inl (hS.1 _ h)) (fun h => Or.inr (hT.1 _ h)))
  · intro a ha
    exact ⟨hS.2 _ ha.1,hT.2 _ ha.2⟩

theorem meet_mono {Δ H S S' T T'} (hS : @Le Δ H S S') (hT : T.Le T') :
    (S.meet T).Le (S'.meet T') := by
  constructor
  · intro a ha
    exact ⟨hS.1 _ ha.1,hT.1 _ ha.2⟩
  · intro a ha
    apply UpperClosure.lift (core Δ H) ha (S.meet T).upper
    intro a ha hc hs
    exact .base hc hs (ha.elim (fun h => Or.inl (hS.2 _ h)) (fun h => Or.inr (hT.2 _ h)))

theorem principal_mono {Δ H a b} (h : Derivation Δ H a b) :
    (principal Δ H a).Le (principal Δ H b) :=
  ⟨fun _ ha => ha.trans h,fun _ hb => h.trans hb⟩

theorem principal_modal_mono {Δ H a m n} (h : Submode Δ m n) :
    (principal Δ H (.modal a m)).Le (principal Δ H (.modal a n)) := by
  constructor
  · intro c hc
    exact hc.trans ((Derivation.refl ((carrier_modal_total h.defined.1).mp hc.carriers.2)
      hc.shaped.2).congr h)
  · intro c hc
    exact ((Derivation.refl ((carrier_modal_total h.defined.2).mp hc.carriers.1)
      hc.shaped.1).congr h).trans hc

end Interpretation

abbrev Coordinate (Δ : Bounds) := {s : Normalized // Entails Δ (.defined s.control)}

def Coordinate.index {Δ} (s : Coordinate Δ) : TotalIndex Δ := ⟨s.val.control,s.property⟩

def Coordinate.prepend {Δ} (s : Coordinate Δ) (m : ModExpr) : Coordinate Δ :=
  ⟨s.val.prepend Δ m,Normalized.prepend_control_total s.property m⟩

def identityCoordinate (Δ : Bounds) : Coordinate Δ :=
  ⟨⟨none,.epsilon⟩,fun _ _ => rfl⟩

def totalCoordinate {Δ} (m : TotalIndex Δ) : Coordinate Δ := ⟨⟨none,m.val⟩,m.property⟩

def denote (Δ : Bounds) (H : Set CompareTy) : CompareTy → Coordinate Δ → Interpretation Δ H
  | .modal a m, s => denote Δ H a (s.prepend m)
  | .prod a b, s =>
      let T := indexedProdTable Δ H s.val.literal
      ⟨T.lower s.index (denote Δ H a s).lower.mem (denote Δ H b s).lower.mem,
       T.upper s.index (denote Δ H a s).upper.mem (denote Δ H b s).upper.mem⟩
  | .sum a b, s =>
      let T := indexedSumTable Δ H s.val.literal
      ⟨T.lower s.index (denote Δ H a s).lower.mem (denote Δ H b s).lower.mem,
       T.upper s.index (denote Δ H a s).upper.mem (denote Δ H b s).upper.mem⟩
  | .fn a b, s =>
      match s.val.literal with
      | none =>
          let T := indexedFnTable Δ H
          ⟨T.lower s.index (denote Δ H a (identityCoordinate Δ)).upper.mem
              (denote Δ H b (identityCoordinate Δ)).lower.mem,
           T.upper s.index (denote Δ H a (identityCoordinate Δ)).lower.mem
              (denote Δ H b (identityCoordinate Δ)).upper.mem⟩
      | some p => Interpretation.principal Δ H (.modal (.modal (.fn a b) p) s.val.control)
  | .join a b, s =>
      match s.val.literal with
      | none => (denote Δ H a s).join (denote Δ H b s)
      | some p => Interpretation.principal Δ H (.modal (.modal (.join a b) p) s.val.control)
  | .meet a b, s =>
      match s.val.literal with
      | none => (denote Δ H a s).meet (denote Δ H b s)
      | some p => Interpretation.principal Δ H (.modal (.modal (.meet a b) p) s.val.control)
  | a, s => Interpretation.principal Δ H (.modal (Suffix.apply s.val.literal a) s.val.control)

theorem denote_mono {Δ H a} {s t : Coordinate Δ}
    (h : Normalized.Below Δ s.val t.val) : (denote Δ H a s).Le (denote Δ H a t) := by
  induction a generalizing s t with
  | modal a m ih => exact ih (s := s.prepend m) (t := t.prepend m) (h.prepend m)
  | prod a b ia ib =>
      have ha := ia h
      have hb := ib h
      rcases s with ⟨⟨p,m⟩,hm⟩
      rcases t with ⟨⟨q,n⟩,hn⟩
      obtain ⟨hp,hmn⟩ := h
      cases hp
      exact ⟨fun _ hc => (indexedProdTable Δ H p).lower_mono
          (m := ⟨m,hm⟩) (n := ⟨n,hn⟩) hmn ha.1 hb.1 hc,
        fun _ hc => (indexedProdTable Δ H p).upper_mono
          (m := ⟨m,hm⟩) (n := ⟨n,hn⟩) hmn ha.2 hb.2 hc⟩
  | sum a b ia ib =>
      have ha := ia h
      have hb := ib h
      rcases s with ⟨⟨p,m⟩,hm⟩
      rcases t with ⟨⟨q,n⟩,hn⟩
      obtain ⟨hp,hmn⟩ := h
      cases hp
      exact ⟨fun _ hc => (indexedSumTable Δ H p).lower_mono
          (m := ⟨m,hm⟩) (n := ⟨n,hn⟩) hmn ha.1 hb.1 hc,
        fun _ hc => (indexedSumTable Δ H p).upper_mono
          (m := ⟨m,hm⟩) (n := ⟨n,hn⟩) hmn ha.2 hb.2 hc⟩
  | fn a b ia ib =>
      rcases s with ⟨⟨p,m⟩,hm⟩
      rcases t with ⟨⟨q,n⟩,hn⟩
      obtain ⟨hp,hmn⟩ := h
      cases hp
      cases p with
      | none =>
          have hr : (indexedFnTable Δ H).le ⟨m,hm⟩ ⟨n,hn⟩ :=
            hmn.trans ((indexedFnTable Δ H).refl ⟨n,hn⟩)
          exact ⟨fun _ hc => (indexedFnTable Δ H).lower_mono hr (fun _ h => h) (fun _ h => h) hc,
            fun _ hc => (indexedFnTable Δ H).upper_mono hr (fun _ h => h) (fun _ h => h) hc⟩
      | some p => exact Interpretation.principal_modal_mono hmn
  | join a b ia ib =>
      have ha := ia h
      have hb := ib h
      rcases s with ⟨⟨p,m⟩,hm⟩
      rcases t with ⟨⟨q,n⟩,hn⟩
      obtain ⟨hp,hmn⟩ := h
      cases hp
      cases p with
      | none => exact Interpretation.join_mono ha hb
      | some p => exact Interpretation.principal_modal_mono hmn
  | meet a b ia ib =>
      have ha := ia h
      have hb := ib h
      rcases s with ⟨⟨p,m⟩,hm⟩
      rcases t with ⟨⟨q,n⟩,hn⟩
      obtain ⟨hp,hmn⟩ := h
      cases hp
      cases p with
      | none => exact Interpretation.meet_mono ha hb
      | some p => exact Interpretation.principal_modal_mono hmn
  | var | unit | credit =>
      rcases s with ⟨⟨p,m⟩,hm⟩
      rcases t with ⟨⟨q,n⟩,hn⟩
      obtain ⟨hp,hmn⟩ := h
      cases hp
      exact Interpretation.principal_modal_mono hmn

def Related (Δ : Bounds) (H : Set CompareTy) (a b : CompareTy) : Prop :=
  ∀ m : TotalIndex Δ, (denote Δ H a (totalCoordinate m)).Le (denote Δ H b (totalCoordinate m))

theorem Related.refl {Δ H a} : Related Δ H a a := fun _ => Interpretation.Le.refl _

theorem Related.trans {Δ H a b c} (h : Related Δ H a b) (h' : Related Δ H b c) :
    Related Δ H a c := fun m => (h m).trans (h' m)

theorem Related.prod {Δ H a b c d m}
    (hac : Related Δ H (.modal a m) (.modal c m))
    (hbd : Related Δ H (.modal b m) (.modal d m)) :
    Related Δ H (.modal (.prod a b) m) (.modal (.prod c d) m) := by
  intro r
  have ha := hac r
  have hb := hbd r
  let s := (totalCoordinate r).prepend m
  let T := indexedProdTable Δ H s.val.literal
  exact ⟨fun _ hc => T.lower_mono (T.refl s.index) ha.1 hb.1 hc,
    fun _ hc => T.upper_mono (T.refl s.index) ha.2 hb.2 hc⟩

theorem Related.sum {Δ H a b c d m}
    (hac : Related Δ H (.modal a m) (.modal c m))
    (hbd : Related Δ H (.modal b m) (.modal d m)) :
    Related Δ H (.modal (.sum a b) m) (.modal (.sum c d) m) := by
  intro r
  have ha := hac r
  have hb := hbd r
  let s := (totalCoordinate r).prepend m
  let T := indexedSumTable Δ H s.val.literal
  exact ⟨fun _ hc => T.lower_mono (T.refl s.index) ha.1 hb.1 hc,
    fun _ hc => T.upper_mono (T.refl s.index) ha.2 hb.2 hc⟩

theorem Related.compose {Δ H a m n} :
    Related Δ H (.modal (.modal a m) n) (.modal a (.compose m n)) := by
  intro r
  exact denote_mono (s := ((totalCoordinate r).prepend n).prepend m)
    (t := (totalCoordinate r).prepend (.compose m n))
    ((totalCoordinate r).val.prepend_compose rfl r.property m n).2

theorem Related.composeRev {Δ H a m n} :
    Related Δ H (.modal a (.compose m n)) (.modal (.modal a m) n) := by
  intro r
  exact denote_mono (s := (totalCoordinate r).prepend (.compose m n))
    (t := ((totalCoordinate r).prepend n).prepend m)
    ((totalCoordinate r).val.prepend_compose rfl r.property m n).1

theorem Coordinate.prepend_total {Δ} {m : ModExpr} (hm : Entails Δ (.defined m))
    (r : TotalIndex Δ) : (totalCoordinate r).prepend m =
      totalCoordinate ⟨.compose m r.val,Entails.defined_compose_iff.mpr ⟨hm,r.property⟩⟩ := by
  apply Subtype.ext
  simp only [Coordinate.prepend, totalCoordinate, Normalized.prepend, normalize_total hm]

private theorem submode_append_total {Δ m n r} (h : Submode Δ m n)
    (hr : Entails Δ (.defined r)) : Submode Δ (.compose m r) (.compose n r) := by
  apply Submode.valid
  intro η hη
  obtain ⟨x,y,hx,hy,hxy⟩ := h.denote hη
  obtain ⟨z,hz⟩ := Option.isSome_iff_exists.mp (hr η hη)
  exact ⟨x.compose z,y.compose z,by simp [ModExpr.eval,hx,hz],
    by simp [ModExpr.eval,hy,hz],Mode.compose_le_right z hxy⟩

theorem Related.congr {Δ H a b m n} (h : Related Δ H a b) (hmn : Submode Δ m n) :
    Related Δ H (.modal a m) (.modal b n) := by
  intro r
  simp only [denote, Coordinate.prepend_total hmn.defined.1,
    Coordinate.prepend_total hmn.defined.2]
  exact (h ⟨.compose m r.val,Entails.defined_compose_iff.mpr ⟨hmn.defined.1,r.property⟩⟩).trans
    (denote_mono ⟨rfl,submode_append_total hmn r.property⟩)

private theorem identity_controls {Δ} (r : TotalIndex Δ) :
    Submode Δ (.compose .epsilon r.val) r.val ∧
      Submode Δ r.val (.compose .epsilon r.val) := by
  constructor <;> apply Submode.valid <;> intro η hη
  all_goals
    obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp (r.property η hη)
    exact ⟨x,x,by simp [ModExpr.eval,ModExpr.epsilon,hx],
      by simp [ModExpr.eval,ModExpr.epsilon,hx],Mode.le_refl x⟩

theorem Related.identity {Δ H a} : Related Δ H (.modal a .epsilon) a := by
  intro r
  simp only [denote, Coordinate.prepend_total (m := .epsilon) (fun _ _ => rfl)]
  exact denote_mono ⟨rfl,(identity_controls r).1⟩

theorem Related.identityRev {Δ H a} : Related Δ H a (.modal a .epsilon) := by
  intro r
  simp only [denote, Coordinate.prepend_total (m := .epsilon) (fun _ _ => rfl)]
  exact denote_mono ⟨rfl,(identity_controls r).2⟩

end
end ModalityInference.ComparisonRawHeadRestriction
