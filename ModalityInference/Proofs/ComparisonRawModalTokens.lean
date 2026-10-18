import ModalityInference.Proofs.ComparisonRawModeTransport
import ModalityInference.Proofs.ComparisonDefinedPreparation

/-! Partial composition factors admit an exact syntax-port representation.
The encoding preserves the same admissible witness, raw scalar guards, and
partial target. It gives a finite input alphabet, not a bound on proof depth. -/

namespace ModalityInference.ComparisonRawModalTokens

open ComparisonRawModeTransport

/-- A syntactically injective port whose evaluation is always undefined.
Its payload is an identifier; its variables cannot affect the result. -/
def token (m : ModExpr) : ModExpr := .leftResidual .epsilon (.meet .bottom m)

@[simp] theorem token_eval (m : ModExpr) (η : ModVar → Option Mode) :
    (token m).eval η = none := by
  cases h : m.eval η <;>
    simp [token,ModExpr.eval,ModExpr.epsilon,ModExpr.bottom,h,Mode.meet,
      Mode.identity,Mode.bottom,Mode.leftResidual]

theorem token_injective : Function.Injective token := by
  intro a b h
  simpa only [token,ModExpr.leftResidual.injEq,ModExpr.meet.injEq,true_and] using h

/-- Remove exactly one port tag, without rewriting its literal payload. -/
def untag (m : ModExpr) : ModExpr :=
  match m with
  | .leftResidual e (.meet b x) => if e = .epsilon ∧ b = .bottom then x else m
  | _ => m

@[simp] theorem untag_token (m : ModExpr) : untag (token m) = m := by
  simp [untag,token]

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Only root composition is traversed. Partial non-composition factors are
opaque syntactic ports; all guarded factors are retained verbatim. -/
def encode (Δ : Bounds) : ModExpr → ModExpr
  | .compose m n => .compose (encode Δ m) (encode Δ n)
  | m => if Entails Δ (.defined m) then m else token m

def decode (Δ : Bounds) : ModExpr → ModExpr
  | .compose m n => .compose (decode Δ m) (decode Δ n)
  | m => if Entails Δ (.defined m) then m else untag m

theorem encode_total {Δ m} (hm : Entails Δ (.defined m)) : encode Δ m = m := by
  induction m with
  | compose m n ihm ihn =>
    have hh := Entails.defined_compose_iff.mp hm
    simp only [encode,ihm hh.1,ihn hh.2]
  | _ => exact if_pos hm

/-- The encoding separates guarded actions from genuinely partial syntax:
every non-total encoded label is nowhere defined, independently of valuation. -/
theorem encode_partial {Δ m} (hm : ¬Entails Δ (.defined m))
    (η : ModVar → Option Mode) : (encode Δ m).eval η = none := by
  induction m with
  | compose m n ihm ihn =>
    by_cases hleft : Entails Δ (.defined m)
    · have hright : ¬Entails Δ (.defined n) := fun h =>
        hm (Entails.defined_compose_iff.mpr ⟨hleft,h⟩)
      simp only [encode,ModExpr.eval,ihn hright]
      cases (encode Δ m).eval η <;> rfl
    · simp only [encode,ModExpr.eval,ihm hleft,bind,Option.bind_none]
  | _ => simp only [encode,if_neg hm,token_eval]

theorem encode_dichotomy (Δ : Bounds) (m : ModExpr) :
    (Entails Δ (.defined m) ∧ encode Δ m = m) ∨
      (¬Entails Δ (.defined m) ∧ ∀ η, (encode Δ m).eval η = none) := by
  by_cases hm : Entails Δ (.defined m)
  · exact .inl ⟨hm,encode_total hm⟩
  · exact .inr ⟨hm,encode_partial hm⟩

theorem decode_total {Δ m} (hm : Entails Δ (.defined m)) : decode Δ m = m := by
  induction m with
  | compose m n ihm ihn =>
    have hh := Entails.defined_compose_iff.mp hm
    simp only [decode,ihm hh.1,ihn hh.2]
  | _ => exact if_pos hm

theorem encode_relabeling (Δ : Bounds) : Relabeling Δ (encode Δ) :=
  ⟨fun _ _ => rfl,fun _ => encode_total⟩

theorem decode_relabeling (Δ : Bounds) : Relabeling Δ (decode Δ) :=
  ⟨fun _ _ => rfl,fun _ => decode_total⟩

theorem token_not_total {Δ m} (hm : ¬Entails Δ (.defined m)) :
    ¬Entails Δ (.defined (token m)) := by
  intro ht
  apply hm
  intro η hη
  have hf := ht η hη
  simp only [ModExpr.WellFormed,token_eval,Option.isSome_none,Bool.false_eq_true] at hf

theorem decode_token {Δ m} (hm : ¬Entails Δ (.defined m)) : decode Δ (token m) = m := by
  change (if Entails Δ (.defined (token m)) then token m else untag (token m)) = m
  rw [if_neg (token_not_total hm),untag_token]

@[simp] theorem decode_encode (Δ : Bounds) (m : ModExpr) : decode Δ (encode Δ m) = m := by
  induction m with
  | compose m n ihm ihn => simp only [encode,decode,ihm,ihn]
  | _ =>
    unfold encode
    split
    · next hm => exact decode_total hm
    · next hm =>
      exact decode_token hm

@[simp] theorem type_roundtrip (Δ : Bounds) (a : CompareTy) :
    type (decode Δ) (type (encode Δ) a) = a := by
  induction a <;> simp_all only [type,decode_encode]

@[simp] theorem public_roundtrip (Δ : Bounds) (a : Ty) :
    publicType (decode Δ) (publicType (encode Δ) a) = a := by
  induction a <;> simp_all only [publicType,decode_encode]

@[simp] theorem constraint_roundtrip (Δ : Bounds) (c : Constraint) :
    constraint (decode Δ) (constraint (encode Δ) c) = c := by
  cases c <;> simp only [constraint,public_roundtrip]

@[simp] theorem context_roundtrip (Δ : Bounds) :
    context (decode Δ) (context (encode Δ) Δ) = Δ := by
  simp [context,List.map_map,Function.comp_def]

theorem decode_encoded_relabeling (Δ : Bounds) :
    Relabeling (context (encode Δ) Δ) (decode Δ) :=
  ⟨fun _ _ => rfl,fun _ hm => decode_total ((context_mode_defined _ _ _).mp hm)⟩

/-- Full algebraic comparison is invariant under the port encoding, including
raw partial declared edges and all identity/composition rules. -/
theorem algebra_iff (Δ : Bounds) (a b : CompareTy) :
    AlgebraSubtype (context (encode Δ) Δ) (type (encode Δ) a) (type (encode Δ) b) ↔
      AlgebraSubtype Δ a b := by
  constructor
  · intro h
    simpa only [context_roundtrip,type_roundtrip] using (decode_encoded_relabeling Δ).algebra h
  · exact (encode_relabeling Δ).algebra

theorem algebra_defined_iff {Δ a b} (ha : CompareTy.DefinedUnder a Δ)
    (hb : CompareTy.DefinedUnder b Δ) :
    AlgebraSubtype (context (encode Δ) Δ) a b ↔ AlgebraSubtype Δ a b := by
  simpa only [(encode_relabeling Δ).type_fixed ha,(encode_relabeling Δ).type_fixed hb]
    using algebra_iff Δ a b

theorem submode_iff (Δ : Bounds) (m n : ModExpr) :
    Submode (context (encode Δ) Δ) m n ↔ Submode Δ m n := by
  constructor
  · intro h
    exact .valid fun _ hη => h.denote ((context_models _ _ _).mpr hη)
  · exact submode_context

/-- Source guards retain their original syntax and truth. Port encoding adds
no definedness requirement to a raw declared bound. -/
theorem entails_iff (Δ : Bounds) (c : CompareConstraint) :
    AlgebraEntails (context (encode Δ) Δ) c ↔ AlgebraEntails Δ c := by
  cases c with
  | sub a b =>
    simp only [AlgebraEntails,context_defined]
    constructor
    · rintro ⟨h,ha,hb⟩; exact ⟨(algebra_defined_iff ha hb).mp h,ha,hb⟩
    · rintro ⟨h,ha,hb⟩; exact ⟨(algebra_defined_iff ha hb).mpr h,ha,hb⟩
  | mode m n => exact submode_iff Δ m n
  | defined m => exact context_mode_defined _ _ _
  | equal v a =>
    have hv : CompareTy.DefinedUnder (.var v) Δ := by
      simp [CompareTy.DefinedUnder,CompareTy.wellFormedBounds,ModeModels]
    simp only [AlgebraEntails,context_defined]
    constructor
    · rintro ⟨hl,hu,ha⟩
      exact ⟨(algebra_defined_iff hv ha).mp hl,(algebra_defined_iff ha hv).mp hu,ha⟩
    · rintro ⟨hl,hu,ha⟩
      exact ⟨(algebra_defined_iff hv ha).mpr hl,(algebra_defined_iff ha hv).mpr hu,ha⟩
  | equiv a b =>
    simp only [AlgebraEntails,context_defined]
    constructor
    · rintro ⟨hl,hu,ha,hb⟩
      exact ⟨(algebra_defined_iff ha hb).mp hl,(algebra_defined_iff hb ha).mp hu,ha,hb⟩
    · rintro ⟨hl,hu,ha,hb⟩
      exact ⟨(algebra_defined_iff ha hb).mpr hl,(algebra_defined_iff hb ha).mpr hu,ha,hb⟩



open ComparisonRawModalRestriction in
theorem encode_allowed {Δ kept m} (h : AllowedMode Δ kept m) :
    AllowedMode Δ (kept.map token) (encode Δ m) := by
  induction m with
  | compose m n ihm ihn =>
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact ihm (fun r hr => h r (List.mem_append_left _ hr)) q hq
    · exact ihn (fun r hr => h r (List.mem_append_right _ hr)) q hq
  | _ =>
    unfold encode
    split
    · next hm =>
      intro q hq
      simp only [factors,List.mem_singleton] at hq
      subst q
      exact .inl hm
    · next hm =>
      intro q hq
      simp only [token,factors,List.mem_singleton] at hq
      subst q
      exact .inr (List.mem_map.mpr ⟨_,(h _ (by simp [factors])).resolve_left hm,rfl⟩)

open ComparisonRawModalRestriction in
theorem type_encoded_allowed {Δ kept a} (h : Allowed Δ kept a) :
    Allowed (context (encode Δ) Δ) (kept.map token) (type (encode Δ) a) := by
  have hs : Allowed Δ (kept.map token) (type (encode Δ) a) := by
    induction a with
    | var | unit | credit => simp [Allowed,type,typeFactors]
    | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb
    | join a b iha ihb | meet a b iha ihb =>
      have hh : Allowed Δ kept a ∧ Allowed Δ kept b := by
        simpa only [allowed_prod,allowed_sum,allowed_fn,allowed_join,allowed_meet] using h
      simpa only [type,allowed_prod,allowed_sum,allowed_fn,allowed_join,allowed_meet] using
        And.intro (iha hh.1) (ihb hh.2)
    | modal a m ih =>
      have hh := allowed_modal.mp h
      exact allowed_modal.mpr ⟨ih hh.1,encode_allowed hh.2⟩
  intro q hq
  exact (hs q hq).imp ((context_mode_defined _ _ _).mpr) id

open ComparisonRawModalRestriction in
/-- The encoded raw boundary contains only guarded labels or one of finitely
many input-port tokens. -/
theorem encoded_boundary_allowed (Δ : Bounds) (endpoints : List CompareTy) :
    ∀ q ∈ boundaryFactors (context (encode Δ) Δ) (endpoints.map (type (encode Δ))),
      Entails (context (encode Δ) Δ) (.defined q) ∨
        q ∈ (boundaryFactors Δ endpoints).map token := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · obtain ⟨c,hc,hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    cases d with
    | sub a b =>
      have hc := boundary_covers Δ endpoints a b hd
      have ha : Allowed Δ (boundaryFactors Δ endpoints) (.ofTy a) := fun q hq => .inr (hc.1 q hq)
      have hb : Allowed Δ (boundaryFactors Δ endpoints) (.ofTy b) := fun q hq => .inr (hc.2 q hq)
      rcases List.mem_append.mp hq with hq | hq
      · exact type_encoded_allowed ha q (by simpa only [type_ofTy] using hq)
      · exact type_encoded_allowed hb q (by simpa only [type_ofTy] using hq)
    | mode | defined | equal | equiv => simp [constraint] at hq
  · obtain ⟨a,ha,hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact type_encoded_allowed (boundary_allowed hb) q hq

open ComparisonRawModalRestriction in
theorem Derivation.support {Δ first second a b}
    (hs : ∀ q ∈ first, Entails Δ (.defined q) ∨ q ∈ second)
    (h : Derivation Δ first a b) : Derivation Δ second a b := by
  have ha {a} (h : Allowed Δ first a) : Allowed Δ second a := by
    intro q hq
    rcases h q hq with ht | hk
    · exact .inl ht
    · exact hs q hk
  induction h with
  | atom h1 h2 h => exact .atom (ha h1) (ha h2) h
  | trans _ _ iha ihb => exact .trans iha ihb
  | congr _ hm ih => exact .congr ih hm
  | prod _ _ iha ihb => exact .prod iha ihb
  | sum _ _ iha ihb => exact .sum iha ihb
  | fn _ _ hm iha ihb => exact .fn iha ihb hm
  | joinLeast _ _ iha ihb => exact .joinLeast iha ihb
  | meetGreatest _ _ iha ihb => exact .meetGreatest iha ihb
  | clamp hab hat hm _ _ ihb iht => exact .clamp hab hat hm ihb iht
  | clampRev hab hat hm _ _ ihb iht => exact .clampRev hab hat hm ihb iht

open ComparisonRawModalRestriction in
/-- Comparison from any defined source to a possibly partial target admits an
exact proof over finite input ports. No source-witness syntax is added to the
port alphabet. -/
theorem token_derivation_iff {Δ : Bounds} {a : CompareTy} (ha : a.DefinedUnder Δ)
    (b : CompareTy) :
    Derivation (context (encode Δ) Δ) ((boundaryFactors Δ [b]).map token)
      a (type (encode Δ) b) ↔ AlgebraSubtype Δ a b := by
  constructor
  · intro h
    apply (algebra_iff Δ a b).mp
    simpa only [(encode_relabeling Δ).type_fixed ha] using h.subtype
  · intro h
    have he := (algebra_iff Δ a b).mpr h
    rw [(encode_relabeling Δ).type_fixed ha] at he
    have hda : a.DefinedUnder (context (encode Δ) Δ) := (context_defined _ _ _).mpr ha
    have hd := (derivation_iff (boundary_covers (context (encode Δ) Δ)
      ([b].map (type (encode Δ)))) (.of_defined hda)
      (boundary_allowed (by simp))).mpr he
    exact Derivation.support (encoded_boundary_allowed Δ [b]) hd

/-- The source and its shared quantified images are not changed by abstraction. -/
def prepared (p : SchemePreparation.Prepared) : SchemePreparation.Prepared :=
  {p with assumptions := context (encode p.assumptions) p.assumptions
          targetType := publicType (encode p.assumptions) p.targetType}

theorem prepared_witness_iff (p : SchemePreparation.Prepared) (σ : CompareSubstitution) :
    ComparisonPreparation.PreparedWitnessUnder (prepared p) σ ↔
      ComparisonPreparation.PreparedWitnessUnder p σ := by
  unfold ComparisonPreparation.PreparedWitnessUnder ComparisonPreparation.PreparedWitness
  simp only [prepared,context_defined]
  have hs : CompareSubstitution.WellShaped (context (encode p.assumptions) p.assumptions) σ ↔
      CompareSubstitution.WellShaped p.assumptions σ := by
    simp only [CompareSubstitution.WellShaped,context_shaped]
  have hg : AlgebraEntailsAll (context (encode p.assumptions) p.assumptions) (σ.bounds p.sourceBounds) ↔
      AlgebraEntailsAll p.assumptions (σ.bounds p.sourceBounds) := by
    simp only [AlgebraEntailsAll,entails_iff]
  have hw : σ.WellFormedUnder (context (encode p.assumptions) p.assumptions) ↔
      σ.WellFormedUnder p.assumptions := by
    exact ⟨fun h => h.of_models (fun _ => (context_models _ _ _).mpr),
      fun h => h.of_models (fun _ => (context_models _ _ _).mp)⟩
  constructor
  · rintro ⟨⟨hd,hshape,hguards,ht⟩,himages,hbody⟩
    refine ⟨⟨hd,hs.mp hshape,hg.mp hguards,?_⟩,hw.mp himages,hbody⟩
    apply (algebra_iff p.assumptions _ _).mp
    simpa only [type_ofTy,(encode_relabeling _).type_fixed hbody] using ht
  · rintro ⟨⟨hd,hshape,hguards,ht⟩,himages,hbody⟩
    refine ⟨⟨hd,hs.mpr hshape,hg.mpr hguards,?_⟩,hw.mpr himages,hbody⟩
    simpa only [type_ofTy,(encode_relabeling _).type_fixed hbody] using
      (algebra_iff p.assumptions _ _).mpr ht

end
end ModalityInference.ComparisonRawModalTokens
