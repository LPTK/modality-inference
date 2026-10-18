import ModalityInference.Proofs.ComparisonDeclaredBoundary
import ModalityInference.Proofs.SymbolicInversion

namespace ModalityInference.ComparisonDeclaredBoundary

/-- A comparison segment without a declared edge at its outermost constructor.
The comparisons of constructor children retain the full declared relation. -/
inductive Segment (Δ : Bounds) : Ty → Ty → Prop where
  | refl {a} : Segment Δ a a
  | trans {a b c} : Segment Δ a b → Segment Δ b c → Segment Δ a c
  | identity {a} : Segment Δ (.modal a .epsilon) a
  | identityRev {a} : Segment Δ a (.modal a .epsilon)
  | compose {a m n} : Segment Δ (.modal (.modal a m) n) (.modal a (.compose m n))
  | composeRev {a m n} : Segment Δ (.modal a (.compose m n)) (.modal (.modal a m) n)
  | congr {a b m n} : Segment Δ a b → Submode Δ m n →
      Segment Δ (.modal a m) (.modal b n)
  | prod {a b c d m} : Subtype Δ (.modal a m) (.modal c m) →
      Subtype Δ (.modal b m) (.modal d m) →
      Segment Δ (.modal (.prod a b) m) (.modal (.prod c d) m)
  | sum {a b c d m} : Subtype Δ (.modal a m) (.modal c m) →
      Subtype Δ (.modal b m) (.modal d m) →
      Segment Δ (.modal (.sum a b) m) (.modal (.sum c d) m)
  | fn {a b c d m n} : Subtype Δ c a → Subtype Δ b d →
      Submode Δ m (.compose n .top) →
      Segment Δ (.modal (.fn a b) m) (.modal (.fn c d) n)

theorem Segment.subtype {Δ : Bounds} {s t : Ty} (h : Segment Δ s t) : Subtype Δ s t := by
  induction h with
  | refl => exact .refl
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | identity => exact .identity
  | identityRev => exact .identityRev
  | compose => exact .compose
  | composeRev => exact .composeRev
  | congr _ hm ih => exact .congr ih hm
  | prod ha hb => exact .prod ha hb
  | sum ha hb => exact .sum ha hb
  | fn ha hb hm => exact .fn ha hb hm

theorem Segment.root_eq {Δ : Bounds} {s t : Ty} (h : Segment Δ s t) : root s = root t := by
  induction h with
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congr _ _ ih => exact ih
  | _ => rfl

/-- Cut at the first whole declared edge encountered by the outer constructor. -/
theorem first_bound_cut {Δ : Bounds} {s t : Ty} (h : Subtype Δ s t) :
    Segment Δ s t ∨ ∃a b q, Constraint.sub a b ∈ Δ ∧
      Entails Δ (.defined q) ∧ Segment Δ s (.modal a q) ∧
      Subtype Δ (.modal b q) t := by
  induction h with
  | refl => exact .inl .refl
  | trans hab hbc iha ihb =>
    rcases iha with hseg | ⟨a,b,q,hb,hq,hl,hu⟩
    · rcases ihb with hseg' | ⟨a,b,q,hb,hq,hl,hu⟩
      · exact .inl (.trans hseg hseg')
      · exact .inr ⟨a,b,q,hb,hq,.trans hseg hl,hu⟩
    · exact .inr ⟨a,b,q,hb,hq,hl,.trans hu hbc⟩
  | bound hb => exact .inr ⟨_,_,.epsilon,hb,(fun _ _ => rfl),.identityRev,.identity⟩
  | identity => exact .inl .identity
  | identityRev => exact .inl .identityRev
  | compose => exact .inl .compose
  | composeRev => exact .inl .composeRev
  | @congr s t m n hab hmode ih =>
    rcases ih with hseg | ⟨a,b,q,hb,hq,hl,hu⟩
    · exact .inl (.congr hseg hmode)
    · refine .inr ⟨a,b,.compose q m,hb,?_,?_,?_⟩
      · exact Entails.defined_compose_iff.mpr ⟨hq,hmode.defined.1⟩
      · exact .trans (.congr hl (.refl hmode.defined.1)) .compose
      · exact .trans .composeRev (.congr hu hmode)
  | prod ha hb iha ihb => exact .inl (.prod ha hb)
  | sum ha hb iha ihb => exact .inl (.sum ha hb)
  | fn ha hb hm iha ihb => exact .inl (.fn ha hb hm)

/-- The dual cut retains the final whole declared edge before the target constructor. -/
theorem last_bound_cut {Δ : Bounds} {s t : Ty} (h : Subtype Δ s t) :
    Segment Δ s t ∨ ∃a b q, Constraint.sub a b ∈ Δ ∧
      Entails Δ (.defined q) ∧ Subtype Δ s (.modal a q) ∧
      Segment Δ (.modal b q) t := by
  induction h with
  | refl => exact .inl .refl
  | trans hab hbc iha ihb =>
    rcases ihb with hseg | ⟨a,b,q,hb,hq,hl,hu⟩
    · rcases iha with hseg' | ⟨a,b,q,hb,hq,hl,hu⟩
      · exact .inl (.trans hseg' hseg)
      · exact .inr ⟨a,b,q,hb,hq,hl,.trans hu hseg⟩
    · exact .inr ⟨a,b,q,hb,hq,.trans hab hl,hu⟩
  | bound hb => exact .inr ⟨_,_,.epsilon,hb,(fun _ _ => rfl),.identityRev,.identity⟩
  | identity => exact .inl .identity
  | identityRev => exact .inl .identityRev
  | compose => exact .inl .compose
  | composeRev => exact .inl .composeRev
  | @congr s t m n hab hmode ih =>
    rcases ih with hseg | ⟨a,b,q,hb,hq,hl,hu⟩
    · exact .inl (.congr hseg hmode)
    · refine .inr ⟨a,b,.compose q n,hb,?_,?_,?_⟩
      · exact Entails.defined_compose_iff.mpr ⟨hq,hmode.defined.2⟩
      · exact .trans (.congr hl hmode) .compose
      · exact .trans .composeRev (.congr hu (.refl hmode.defined.2))
  | prod ha hb iha ihb => exact .inl (.prod ha hb)
  | sum ha hb iha ihb => exact .inl (.sum ha hb)
  | fn ha hb hm iha ihb => exact .inl (.fn ha hb hm)

theorem Segment.pairChild {Δ : Bounds} {s t : Ty} (h : Segment Δ s t)
    (hs : root s = .prod ∨ root s = .sum) (right : Bool) :
    Subtype Δ (SymbolicInversion.pairChild right s) (SymbolicInversion.pairChild right t) := by
  induction h with
  | refl => exact .refl
  | trans h₁ h₂ ih₁ ih₂ =>
    exact .trans (ih₁ hs) (ih₂ (by rwa [← h₁.root_eq]))
  | identity => exact .identity
  | identityRev => exact .identityRev
  | compose => exact .compose
  | composeRev => exact .composeRev
  | congr h hm ih => exact .congr (ih hs) hm
  | prod h₁ h₂ | sum h₁ h₂ => cases right <;> first | exact h₁ | exact h₂
  | fn h₁ h₂ hm => simp [root] at hs

theorem Segment.fnChild {Δ : Bounds} {s t : Ty} (h : Segment Δ s t)
    (hs : root s = .fn) (domain : Bool) :
    if domain then Subtype Δ (SymbolicInversion.fnChild domain t) (SymbolicInversion.fnChild domain s)
    else Subtype Δ (SymbolicInversion.fnChild domain s) (SymbolicInversion.fnChild domain t) := by
  induction h with
  | refl => cases domain <;> exact .refl
  | trans h₁ h₂ ih₁ ih₂ =>
    have hh := ih₂ (h₁.root_eq.symm.trans hs)
    cases domain
    · exact .trans (ih₁ hs) hh
    · exact .trans hh (ih₁ hs)
  | identity | identityRev | compose | composeRev => cases domain <;> exact .refl
  | congr h hm ih => exact ih hs
  | prod h₁ h₂ | sum h₁ h₂ => simp [root] at hs
  | fn h₁ h₂ hm => cases domain <;> first | exact h₁ | exact h₂

theorem Segment.tag_eq {Δ : Bounds} {s t : Ty} (h : Segment Δ s t) :
    SymbolicInversion.tag s = SymbolicInversion.tag t := by
  induction h with
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congr _ _ ih => exact ih
  | _ => rfl

open ComparisonStructuralProjection in
/-- The scalar action of a segment is independent of its constructor children. -/
theorem Segment.root_value_order {Δ : Bounds} {s t : Ty} (h : Segment Δ s t)
    {kind : Nat} (hs : SymbolicInversion.tag s = kind)
    {η : ModVar → Mode} (hη : ModeModels Δ η) :
    rootOrder kind (rootValue η (.ofTy s)) (rootValue η (.ofTy t)) := by
  induction h with
  | refl => exact rootOrder_refl _ _
  | trans h₁ h₂ ih₁ ih₂ =>
    exact rootOrder_trans (ih₁ hs) (ih₂ (h₁.tag_eq.symm.trans hs))
  | identity | identityRev =>
    simpa only [CompareTy.ofTy, rootValue, rootExpr, ModExpr.complete, ModExpr.epsilon,
      Mode.compose_identity] using rootOrder_refl kind (rootValue η _)
  | compose | composeRev =>
    simp only [CompareTy.ofTy, rootValue, rootExpr, ModExpr.complete, Mode.compose_assoc]
    exact rootOrder_refl _ _
  | congr h hm ih => exact rootOrder_compose (ih hs) (submode_complete_modes hm hη)
  | prod h₁ h₂ | sum h₁ h₂ => exact rootOrder_refl _ _
  | fn hca hbd hm =>
    have hh := submode_complete_modes hm hη
    have he : kind = 5 := hs.symm
    subst kind
    simpa only [rootOrder, if_true, rootValue, rootExpr, CompareTy.ofTy, ModExpr.complete,
      ModExpr.epsilon, ModExpr.top, Mode.identity_compose, Mode.compose_assoc, Mode.compose_self] using
      Mode.compose_le_right Mode.top hh

open ComparisonStructuralProjection in
theorem Segment.outer_mode {Δ : Bounds} {s t : Ty} (h : Segment Δ s t)
    (hs : s.DefinedUnder Δ) (ht : t.DefinedUnder Δ) (hf : SymbolicInversion.tag s ≠ 5) :
    Submode Δ s.outer.2 t.outer.2 := by
  apply Submode.valid
  intro η hη
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp
    ((TypeExpr.definedUnder_modal.mp ((s.outer_definedUnder Δ).mpr hs)).2 η hη)
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp
    ((TypeExpr.definedUnder_modal.mp ((t.outer_definedUnder Δ).mpr ht)).2 η hη)
  refine ⟨m,n,hm,hn,?_⟩
  have hh := h.root_value_order rfl hη
  simpa only [rootOrder, hf, if_false, rootValue, SymbolicInversion.rootExpr_ofTy,
    ModExpr.complete_of_eval hm, ModExpr.complete_of_eval hn] using hh

open ComparisonStructuralProjection in
theorem Segment.outer_fn_mode {Δ : Bounds} {s t : Ty} (h : Segment Δ s t)
    (hs : s.DefinedUnder Δ) (ht : t.DefinedUnder Δ) (hf : SymbolicInversion.tag s = 5) :
    Submode Δ s.outer.2 (.compose t.outer.2 .top) := by
  apply Submode.valid
  intro η hη
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp
    ((TypeExpr.definedUnder_modal.mp ((s.outer_definedUnder Δ).mpr hs)).2 η hη)
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp
    ((TypeExpr.definedUnder_modal.mp ((t.outer_definedUnder Δ).mpr ht)).2 η hη)
  refine ⟨m,n.compose Mode.top,hm,?_,?_⟩
  · simp only [ModExpr.eval, hn, ModExpr.top, bind, pure, Option.bind_some]
  · have hh := h.root_value_order hf hη
    simp only [rootOrder, if_true, rootValue, SymbolicInversion.rootExpr_ofTy,
      ModExpr.complete_of_eval hm, ModExpr.complete_of_eval hn] at hh
    simpa only [Mode.le_iff, Mode.compose, Mode.top, Bool.and_false, Bool.and_true,
      Bool.false_eq_true, IsEmpty.forall_iff, and_true] using hh

end ModalityInference.ComparisonDeclaredBoundary
