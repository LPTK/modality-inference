import ModalityInference.Proofs.ComparisonDefinedCovers

/-! Raw declared bounds need not establish annotation definedness. This
restriction preserves their exact endpoints and the full comparison algebra,
while confining partial composition factors throughout a derivation to a finite
input alphabet. Total factors remain guarded by the original bounds. -/

namespace ModalityInference.ComparisonRawModalRestriction

/-- Root composition factors; non-composition syntax remains literal. -/
def factors : ModExpr → List ModExpr
  | .compose a b => factors a ++ factors b
  | m => [m]

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Erase only partial factors absent from the protected input boundary. -/
def mode (Δ : Bounds) (kept : List ModExpr) : ModExpr → ModExpr
  | .compose a b => .compose (mode Δ kept a) (mode Δ kept b)
  | m => if Entails Δ (.defined m) ∨ m ∈ kept then m else .epsilon

@[simp] theorem mode_compose (Δ : Bounds) (kept : List ModExpr) (m n : ModExpr) :
    mode Δ kept (.compose m n) = .compose (mode Δ kept m) (mode Δ kept n) := rfl

theorem mode_defined {Δ kept m} (hm : Entails Δ (.defined m)) : mode Δ kept m = m := by
  induction m with
  | compose a b iha ihb =>
    have hd := Entails.defined_compose_iff.mp hm
    simp only [mode_compose, iha hd.1, ihb hd.2]
  | _ => simp only [mode, if_pos (Or.inl hm)]

@[simp] theorem mode_epsilon (Δ : Bounds) (kept : List ModExpr) :
    mode Δ kept .epsilon = .epsilon := mode_defined (fun _ _ => rfl)

theorem mode_fixed {Δ kept m} (hm : ∀ q ∈ factors m, q ∈ kept) : mode Δ kept m = m := by
  induction m with
  | compose a b iha ihb =>
    rw [mode_compose, iha (fun q hq => hm q (List.mem_append_left _ hq)),
      ihb (fun q hq => hm q (List.mem_append_right _ hq))]
  | _ => exact if_pos (.inr (hm _ (by simp [factors])))

def AllowedMode (Δ : Bounds) (kept : List ModExpr) (m : ModExpr) : Prop :=
  ∀ q ∈ factors m, Entails Δ (.defined q) ∨ q ∈ kept

theorem mode_allowed (Δ : Bounds) (kept : List ModExpr) (m : ModExpr) :
    AllowedMode Δ kept (mode Δ kept m) := by
  induction m with
  | compose a b iha ihb =>
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact iha q hq
    · exact ihb q hq
  | _ =>
    unfold mode
    split
    · next hm =>
      intro q hq
      simp only [factors,List.mem_singleton] at hq
      exact hq ▸ hm
    · intro q hq
      have he : q = .epsilon := by simpa [ModExpr.epsilon,factors] using hq
      subst q
      exact .inl (fun _ _ => rfl)

def ty (Δ : Bounds) (kept : List ModExpr) : CompareTy → CompareTy
  | .var v => .var v
  | .unit => .unit
  | .credit => .credit
  | .prod a b => .prod (ty Δ kept a) (ty Δ kept b)
  | .sum a b => .sum (ty Δ kept a) (ty Δ kept b)
  | .fn a b => .fn (ty Δ kept a) (ty Δ kept b)
  | .modal a m => .modal (ty Δ kept a) (mode Δ kept m)
  | .join a b => .join (ty Δ kept a) (ty Δ kept b)
  | .meet a b => .meet (ty Δ kept a) (ty Δ kept b)

def typeFactors : CompareTy → List ModExpr
  | .var _ | .unit | .credit => []
  | .prod a b | .sum a b | .fn a b | .join a b | .meet a b => typeFactors a ++ typeFactors b
  | .modal a m => typeFactors a ++ factors m

def Allowed (Δ : Bounds) (kept : List ModExpr) (a : CompareTy) : Prop :=
  ∀ q ∈ typeFactors a, Entails Δ (.defined q) ∨ q ∈ kept

theorem ty_allowed (Δ : Bounds) (kept : List ModExpr) (a : CompareTy) :
    Allowed Δ kept (ty Δ kept a) := by
  induction a with
  | var | unit | credit => simp [Allowed,ty,typeFactors]
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb
  | join a b iha ihb | meet a b iha ihb =>
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact iha q hq
    · exact ihb q hq
  | modal a m ih =>
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact ih q hq
    · exact mode_allowed Δ kept m q hq

theorem ty_fixed {Δ kept a} (ha : ∀ q ∈ typeFactors a, q ∈ kept) : ty Δ kept a = a := by
  induction a with
  | var | unit | credit => rfl
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb
  | join a b iha ihb | meet a b iha ihb =>
    simp only [ty, iha (fun q hq => ha q (List.mem_append_left _ hq)),
      ihb (fun q hq => ha q (List.mem_append_right _ hq))]
  | modal a m ih =>
    simp only [ty, ih (fun q hq => ha q (List.mem_append_left _ hq)),
      mode_fixed (fun q hq => ha q (List.mem_append_right _ hq))]

theorem ty_defined {Δ kept a} (ha : CompareTy.DefinedUnder a Δ) : ty Δ kept a = a := by
  induction a with
  | var | unit | credit => rfl
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb
  | join a b iha ihb | meet a b iha ihb =>
    have hh : a.DefinedUnder Δ ∧ b.DefinedUnder Δ := by
      simpa only [CompareTy.definedUnder_prod_iff,CompareTy.definedUnder_sum_iff,
        CompareTy.definedUnder_fn_iff,CompareTy.definedUnder_join_iff,
        CompareTy.definedUnder_meet_iff] using ha
    simp only [ty, iha hh.1, ihb hh.2]
  | modal a m ih =>
    have hh := CompareTy.definedUnder_modal_iff.mp ha
    simp only [ty, ih hh.1, mode_defined hh.2]

@[simp] theorem ty_shape (Δ : Bounds) (kept : List ModExpr) (a : CompareTy) :
    (ty Δ kept a).shape = a.shape := by
  induction a <;> simp_all only [ty,CompareTy.shape]

theorem ty_wellShaped {Δ kept a} (ha : CompareTy.WellShaped Δ a) :
    (ty Δ kept a).WellShaped Δ := by
  induction a <;> simp_all only [ty,CompareTy.WellShaped,ty_shape,and_self]


/-- The protected alphabet contains the literal factors of every raw subtype
edge. No definedness premise is imposed on either endpoint. -/
def Covers (Δ : Bounds) (kept : List ModExpr) : Prop :=
  ∀ a b, Constraint.sub a b ∈ Δ →
    (∀ q ∈ typeFactors (.ofTy a), q ∈ kept) ∧
    (∀ q ∈ typeFactors (.ofTy b), q ∈ kept)

theorem shaped {Δ kept a b} (hc : Covers Δ kept) (h : ShapedSubtype Δ a b) :
    ShapedSubtype Δ (ty Δ kept a) (ty Δ kept b) := by
  induction h with
  | refl hs => exact .refl (ty_wellShaped hs)
  | trans _ _ iha ihb => exact .trans iha ihb
  | bound hb =>
    rw [ty_fixed (hc _ _ hb).1,ty_fixed (hc _ _ hb).2]
    exact .bound hb
  | identity hs => simpa only [ty,mode_epsilon] using ShapedSubtype.identity (ty_wellShaped hs)
  | identityRev hs => simpa only [ty,mode_epsilon] using ShapedSubtype.identityRev (ty_wellShaped hs)
  | compose hs => exact .compose (ty_wellShaped hs)
  | composeRev hs => exact .composeRev (ty_wellShaped hs)
  | congr _ hm ih =>
    simpa only [ty,mode_defined hm.defined.1,mode_defined hm.defined.2] using
      ShapedSubtype.congr ih hm
  | prod _ _ iha ihb => exact .prod iha ihb
  | sum _ _ iha ihb => exact .sum iha ihb
  | fn _ _ hm iha ihb =>
    have hn := (Entails.defined_compose_iff.mp hm.defined.2).1
    simpa only [ty,mode_defined hm.defined.1,mode_defined hn] using
      ShapedSubtype.fn iha ihb hm
  | joinLeft hs => exact .joinLeft (ty_wellShaped hs)
  | joinRight hs => exact .joinRight (ty_wellShaped hs)
  | meetLeft hs => exact .meetLeft (ty_wellShaped hs)
  | meetRight hs => exact .meetRight (ty_wellShaped hs)
  | joinLeast _ _ iha ihb => exact .joinLeast iha ihb
  | meetGreatest _ _ iha ihb => exact .meetGreatest iha ihb

/-- Every full algebraic derivation survives erasure of proof-local partial
factors, while the raw declared bounds are retained verbatim. -/
theorem algebra {Δ kept a b} (hc : Covers Δ kept) (h : AlgebraSubtype Δ a b) :
    AlgebraSubtype Δ (ty Δ kept a) (ty Δ kept b) := by
  induction h with
  | shaped h => exact .shaped (shaped hc h)
  | trans _ _ iha ihb => exact .trans iha ihb
  | equation h =>
    have hd := ComparisonDefinedCovers.equation_defined h
    rw [ty_defined hd.1,ty_defined hd.2]
    exact .equation h
  | equationRev h =>
    have hd := ComparisonDefinedCovers.equation_defined h
    rw [ty_defined hd.1,ty_defined hd.2]
    exact .equationRev h
  | congr _ hm ih =>
    simpa only [ty,mode_defined hm.defined.1,mode_defined hm.defined.2] using
      AlgebraSubtype.congr ih hm
  | prod _ _ iha ihb => exact .prod iha ihb
  | sum _ _ iha ihb => exact .sum iha ihb
  | fn _ _ hm iha ihb =>
    have hn := (Entails.defined_compose_iff.mp hm.defined.2).1
    simpa only [ty,mode_defined hm.defined.1,mode_defined hn] using
      AlgebraSubtype.fn iha ihb hm
  | joinLeast _ _ iha ihb => exact .joinLeast iha ihb
  | meetGreatest _ _ iha ihb => exact .meetGreatest iha ihb
  | clamp hab hat hm hb ht ihb iht =>
    simpa only [ty,ty_defined hab.2.1,ty_defined hab.2.2,ty_defined hat.2.2,
      mode_defined hm] using AlgebraSubtype.clamp hab hat hm hb ht
  | clampRev hab hat hm hb ht ihb iht =>
    simpa only [ty,ty_defined hab.2.1,ty_defined hab.2.2,ty_defined hat.2.2,
      mode_defined hm] using AlgebraSubtype.clampRev hab hat hm hb ht


/-- The nonrecursive rules of the full comparison algebra. -/
inductive Atomic (Δ : Bounds) : CompareTy → CompareTy → Prop where
  | refl {a} : a.WellShaped Δ → Atomic Δ a a
  | bound {a b} : Constraint.sub a b ∈ Δ → Atomic Δ (.ofTy a) (.ofTy b)
  | identity {a} : a.WellShaped Δ → Atomic Δ (.modal a .epsilon) a
  | identityRev {a} : a.WellShaped Δ → Atomic Δ a (.modal a .epsilon)
  | compose {a m n} : a.WellShaped Δ →
      Atomic Δ (.modal (.modal a m) n) (.modal a (.compose m n))
  | composeRev {a m n} : a.WellShaped Δ →
      Atomic Δ (.modal a (.compose m n)) (.modal (.modal a m) n)
  | joinLeft {a b} : (.join a b : CompareTy).WellShaped Δ → Atomic Δ a (.join a b)
  | joinRight {a b} : (.join a b : CompareTy).WellShaped Δ → Atomic Δ b (.join a b)
  | meetLeft {a b} : (.meet a b : CompareTy).WellShaped Δ → Atomic Δ (.meet a b) a
  | meetRight {a b} : (.meet a b : CompareTy).WellShaped Δ → Atomic Δ (.meet a b) b
  | equation {a b} : ComparisonAlgebra.Equation Δ a b → Atomic Δ a b
  | equationRev {a b} : ComparisonAlgebra.Equation Δ a b → Atomic Δ b a

/-- A finite derivation using only protected partial composition factors.
The algebraic rules and the original raw declared edges are unchanged. -/
inductive Derivation (Δ : Bounds) (kept : List ModExpr) : CompareTy → CompareTy → Prop where
  | atom {a b} : Allowed Δ kept a → Allowed Δ kept b → Atomic Δ a b → Derivation Δ kept a b
  | trans {a b c} : Derivation Δ kept a b → Derivation Δ kept b c → Derivation Δ kept a c
  | congr {a b m n} : Derivation Δ kept a b → Submode Δ m n →
      Derivation Δ kept (.modal a m) (.modal b n)
  | prod {a b c d m} : Derivation Δ kept (.modal a m) (.modal c m) →
      Derivation Δ kept (.modal b m) (.modal d m) →
      Derivation Δ kept (.modal (.prod a b) m) (.modal (.prod c d) m)
  | sum {a b c d m} : Derivation Δ kept (.modal a m) (.modal c m) →
      Derivation Δ kept (.modal b m) (.modal d m) →
      Derivation Δ kept (.modal (.sum a b) m) (.modal (.sum c d) m)
  | fn {a b c d m n} : Derivation Δ kept c a → Derivation Δ kept b d →
      Submode Δ m (.compose n .top) →
      Derivation Δ kept (.modal (.fn a b) m) (.modal (.fn c d) n)
  | joinLeast {a b c} : Derivation Δ kept a c → Derivation Δ kept b c →
      Derivation Δ kept (.join a b) c
  | meetGreatest {a b c} : Derivation Δ kept a b → Derivation Δ kept a c →
      Derivation Δ kept a (.meet b c)
  | clamp {b a t m} : ComparisonAlgebra.Compatible Δ b a →
      ComparisonAlgebra.Compatible Δ a t → ComparisonAlgebra.DefinedMode Δ m →
      Derivation Δ kept b a → Derivation Δ kept a t →
      Derivation Δ kept (.modal a m) (.meet (.join a (.modal b m)) (.modal t m))
  | clampRev {b a t m} : ComparisonAlgebra.Compatible Δ b a →
      ComparisonAlgebra.Compatible Δ a t → ComparisonAlgebra.DefinedMode Δ m →
      Derivation Δ kept b a → Derivation Δ kept a t →
      Derivation Δ kept (.meet (.join a (.modal b m)) (.modal t m)) (.modal a m)

theorem Atomic.subtype {Δ a b} (h : Atomic Δ a b) : AlgebraSubtype Δ a b := by
  cases h with
  | refl hs => exact .refl hs
  | bound hb => exact .shaped (.bound hb)
  | identity hs => exact .identity hs
  | identityRev hs => exact .identityRev hs
  | compose hs => exact .compose hs
  | composeRev hs => exact .composeRev hs
  | joinLeft hs => exact .shaped (.joinLeft hs)
  | joinRight hs => exact .shaped (.joinRight hs)
  | meetLeft hs => exact .shaped (.meetLeft hs)
  | meetRight hs => exact .shaped (.meetRight hs)
  | equation h => exact .equation h
  | equationRev h => exact .equationRev h

theorem Derivation.subtype {Δ kept a b} (h : Derivation Δ kept a b) : AlgebraSubtype Δ a b := by
  induction h with
  | atom _ _ h => exact h.subtype
  | trans _ _ iha ihb => exact .trans iha ihb
  | congr _ hm ih => exact .congr ih hm
  | prod _ _ iha ihb => exact .prod iha ihb
  | sum _ _ iha ihb => exact .sum iha ihb
  | fn _ _ hm iha ihb => exact .fn iha ihb hm
  | joinLeast _ _ iha ihb => exact .joinLeast iha ihb
  | meetGreatest _ _ iha ihb => exact .meetGreatest iha ihb
  | clamp hab hat hm _ _ ihb iht => exact .clamp hab hat hm ihb iht
  | clampRev hab hat hm _ _ ihb iht => exact .clampRev hab hat hm ihb iht

theorem Atomic.restrict {Δ kept a b} (hc : Covers Δ kept) (h : Atomic Δ a b) :
    Atomic Δ (ty Δ kept a) (ty Δ kept b) := by
  cases h with
  | refl hs => exact .refl (ty_wellShaped hs)
  | bound hb => rw [ty_fixed (hc _ _ hb).1,ty_fixed (hc _ _ hb).2]; exact .bound hb
  | identity hs => simpa only [ty,mode_epsilon] using Atomic.identity (ty_wellShaped hs)
  | identityRev hs => simpa only [ty,mode_epsilon] using Atomic.identityRev (ty_wellShaped hs)
  | compose hs => exact .compose (ty_wellShaped hs)
  | composeRev hs => exact .composeRev (ty_wellShaped hs)
  | joinLeft hs => exact .joinLeft (ty_wellShaped hs)
  | joinRight hs => exact .joinRight (ty_wellShaped hs)
  | meetLeft hs => exact .meetLeft (ty_wellShaped hs)
  | meetRight hs => exact .meetRight (ty_wellShaped hs)
  | equation h =>
    have hd := ComparisonDefinedCovers.equation_defined h
    rw [ty_defined hd.1,ty_defined hd.2]
    exact .equation h
  | equationRev h =>
    have hd := ComparisonDefinedCovers.equation_defined h
    rw [ty_defined hd.1,ty_defined hd.2]
    exact .equationRev h

theorem Atomic.derivation {Δ kept a b} (hc : Covers Δ kept) (h : Atomic Δ a b) :
    Derivation Δ kept (ty Δ kept a) (ty Δ kept b) :=
  .atom (ty_allowed _ _ _) (ty_allowed _ _ _) (h.restrict hc)

theorem shaped_derivation {Δ kept a b} (hc : Covers Δ kept) (h : ShapedSubtype Δ a b) :
    Derivation Δ kept (ty Δ kept a) (ty Δ kept b) := by
  induction h with
  | refl hs => exact (Atomic.refl hs).derivation hc
  | trans _ _ iha ihb => exact .trans iha ihb
  | bound hb => exact (Atomic.bound hb).derivation hc
  | identity hs => exact (Atomic.identity hs).derivation hc
  | identityRev hs => exact (Atomic.identityRev hs).derivation hc
  | compose hs => exact (Atomic.compose hs).derivation hc
  | composeRev hs => exact (Atomic.composeRev hs).derivation hc
  | congr _ hm ih =>
    simpa only [ty,mode_defined hm.defined.1,mode_defined hm.defined.2] using Derivation.congr ih hm
  | prod _ _ iha ihb => exact .prod iha ihb
  | sum _ _ iha ihb => exact .sum iha ihb
  | fn _ _ hm iha ihb =>
    have hn := (Entails.defined_compose_iff.mp hm.defined.2).1
    simpa only [ty,mode_defined hm.defined.1,mode_defined hn] using Derivation.fn iha ihb hm
  | joinLeft hs => exact (Atomic.joinLeft hs).derivation hc
  | joinRight hs => exact (Atomic.joinRight hs).derivation hc
  | meetLeft hs => exact (Atomic.meetLeft hs).derivation hc
  | meetRight hs => exact (Atomic.meetRight hs).derivation hc
  | joinLeast _ _ iha ihb => exact .joinLeast iha ihb
  | meetGreatest _ _ iha ihb => exact .meetGreatest iha ihb

theorem algebra_derivation {Δ kept a b} (hc : Covers Δ kept) (h : AlgebraSubtype Δ a b) :
    Derivation Δ kept (ty Δ kept a) (ty Δ kept b) := by
  induction h with
  | shaped h => exact shaped_derivation hc h
  | trans _ _ iha ihb => exact .trans iha ihb
  | equation h => exact (Atomic.equation h).derivation hc
  | equationRev h => exact (Atomic.equationRev h).derivation hc
  | congr _ hm ih =>
    simpa only [ty,mode_defined hm.defined.1,mode_defined hm.defined.2] using Derivation.congr ih hm
  | prod _ _ iha ihb => exact .prod iha ihb
  | sum _ _ iha ihb => exact .sum iha ihb
  | fn _ _ hm iha ihb =>
    have hn := (Entails.defined_compose_iff.mp hm.defined.2).1
    simpa only [ty,mode_defined hm.defined.1,mode_defined hn] using Derivation.fn iha ihb hm
  | joinLeast _ _ iha ihb => exact .joinLeast iha ihb
  | meetGreatest _ _ iha ihb => exact .meetGreatest iha ihb
  | clamp hab hat hm _ _ ihb iht =>
    rw [ty_defined hab.2.1,ty_defined hab.2.2] at ihb
    rw [ty_defined hab.2.2,ty_defined hat.2.2] at iht
    simpa only [ty,ty_defined hab.2.1,ty_defined hab.2.2,ty_defined hat.2.2,
      mode_defined hm] using Derivation.clamp hab hat hm ihb iht
  | clampRev hab hat hm _ _ ihb iht =>
    rw [ty_defined hab.2.1,ty_defined hab.2.2] at ihb
    rw [ty_defined hab.2.2,ty_defined hat.2.2] at iht
    simpa only [ty,ty_defined hab.2.1,ty_defined hab.2.2,ty_defined hat.2.2,
      mode_defined hm] using Derivation.clampRev hab hat hm ihb iht


@[simp] theorem allowed_modal {Δ kept a m} :
    Allowed Δ kept (.modal a m) ↔ Allowed Δ kept a ∧ AllowedMode Δ kept m := by
  simp only [Allowed,AllowedMode,typeFactors,List.mem_append,or_imp,forall_and]

@[simp] theorem allowed_prod {Δ kept a b} :
    Allowed Δ kept (.prod a b) ↔ Allowed Δ kept a ∧ Allowed Δ kept b := by
  simp only [Allowed,typeFactors,List.mem_append,or_imp,forall_and]

@[simp] theorem allowed_sum {Δ kept a b} :
    Allowed Δ kept (.sum a b) ↔ Allowed Δ kept a ∧ Allowed Δ kept b := by
  simp only [Allowed,typeFactors,List.mem_append,or_imp,forall_and]

@[simp] theorem allowed_fn {Δ kept a b} :
    Allowed Δ kept (.fn a b) ↔ Allowed Δ kept a ∧ Allowed Δ kept b := by
  simp only [Allowed,typeFactors,List.mem_append,or_imp,forall_and]

@[simp] theorem allowed_join {Δ kept a b} :
    Allowed Δ kept (.join a b) ↔ Allowed Δ kept a ∧ Allowed Δ kept b := by
  simp only [Allowed,typeFactors,List.mem_append,or_imp,forall_and]

@[simp] theorem allowed_meet {Δ kept a b} :
    Allowed Δ kept (.meet a b) ↔ Allowed Δ kept a ∧ Allowed Δ kept b := by
  simp only [Allowed,typeFactors,List.mem_append,or_imp,forall_and]

theorem AllowedMode.of_defined {Δ kept m} (hm : Entails Δ (.defined m)) :
    AllowedMode Δ kept m := by
  simpa only [mode_defined hm] using mode_allowed Δ kept m

theorem Allowed.of_defined {Δ kept a} (ha : CompareTy.DefinedUnder a Δ) :
    Allowed Δ kept a := by
  simpa only [ty_defined ha] using ty_allowed Δ kept a

theorem AllowedMode.fixed {Δ kept m} (hm : AllowedMode Δ kept m) : mode Δ kept m = m := by
  induction m with
  | compose a b iha ihb =>
    rw [mode_compose,iha (fun q hq => hm q (List.mem_append_left _ hq)),
      ihb (fun q hq => hm q (List.mem_append_right _ hq))]
  | _ => exact if_pos (hm _ (by simp [factors]))

theorem Allowed.fixed {Δ kept a} (ha : Allowed Δ kept a) : ty Δ kept a = a := by
  induction a with
  | var | unit | credit => rfl
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb
  | join a b iha ihb | meet a b iha ihb =>
    have hh : Allowed Δ kept a ∧ Allowed Δ kept b := by simpa only
      [allowed_prod,allowed_sum,allowed_fn,allowed_join,allowed_meet] using ha
    simp only [ty,iha hh.1,ihb hh.2]
  | modal a m ih =>
    have hh := allowed_modal.mp ha
    simp only [ty,ih hh.1,hh.2.fixed]

/-- Every node of the restricted proof has only protected partial factors. -/
theorem Derivation.allowed {Δ kept a b} (h : Derivation Δ kept a b) :
    Allowed Δ kept a ∧ Allowed Δ kept b := by
  induction h with
  | atom ha hb _ => exact ⟨ha,hb⟩
  | trans _ _ iha ihb => exact ⟨iha.1,ihb.2⟩
  | congr _ hm ih =>
    exact ⟨allowed_modal.mpr ⟨ih.1,.of_defined hm.defined.1⟩,
      allowed_modal.mpr ⟨ih.2,.of_defined hm.defined.2⟩⟩
  | prod _ _ iha ihb | sum _ _ iha ihb =>
    simp only [allowed_modal] at iha ihb
    simpa only [allowed_modal,allowed_prod,allowed_sum] using
      And.intro ⟨⟨iha.1.1,ihb.1.1⟩,iha.1.2⟩ ⟨⟨iha.2.1,ihb.2.1⟩,iha.2.2⟩
  | fn _ _ hm iha ihb =>
    have hn := (Entails.defined_compose_iff.mp hm.defined.2).1
    exact ⟨allowed_modal.mpr ⟨allowed_fn.mpr ⟨iha.2,ihb.1⟩,.of_defined hm.defined.1⟩,
      allowed_modal.mpr ⟨allowed_fn.mpr ⟨iha.1,ihb.2⟩,.of_defined hn⟩⟩
  | joinLeast _ _ iha ihb => exact ⟨allowed_join.mpr ⟨iha.1,ihb.1⟩,iha.2⟩
  | meetGreatest _ _ iha ihb => exact ⟨iha.1,allowed_meet.mpr ⟨iha.2,ihb.2⟩⟩
  | clamp hab hat hm _ _ ihb iht =>
    have hma := allowed_modal.mpr ⟨ihb.2,AllowedMode.of_defined hm⟩
    have hmb := allowed_modal.mpr ⟨ihb.1,AllowedMode.of_defined hm⟩
    have hmt := allowed_modal.mpr ⟨iht.2,AllowedMode.of_defined hm⟩
    exact ⟨hma,allowed_meet.mpr ⟨allowed_join.mpr ⟨ihb.2,hmb⟩,hmt⟩⟩
  | clampRev hab hat hm _ _ ihb iht =>
    have hma := allowed_modal.mpr ⟨ihb.2,AllowedMode.of_defined hm⟩
    have hmb := allowed_modal.mpr ⟨ihb.1,AllowedMode.of_defined hm⟩
    have hmt := allowed_modal.mpr ⟨iht.2,AllowedMode.of_defined hm⟩
    exact ⟨allowed_meet.mpr ⟨allowed_join.mpr ⟨ihb.2,hmb⟩,hmt⟩,hma⟩

theorem derivation_iff {Δ kept a b} (hc : Covers Δ kept)
    (ha : Allowed Δ kept a) (hb : Allowed Δ kept b) :
    Derivation Δ kept a b ↔ AlgebraSubtype Δ a b := by
  refine ⟨Derivation.subtype,fun h => ?_⟩
  simpa only [ha.fixed,hb.fixed] using algebra_derivation hc h

def boundFactors (Δ : Bounds) : List ModExpr :=
  Δ.flatMap fun c => match c with
    | .sub a b => typeFactors (.ofTy a) ++ typeFactors (.ofTy b)
    | _ => []

/-- The alphabet depends only on the original raw edges and selected endpoints. -/
def boundaryFactors (Δ : Bounds) (endpoints : List CompareTy) : List ModExpr :=
  boundFactors Δ ++ endpoints.flatMap typeFactors

theorem boundary_covers (Δ : Bounds) (endpoints : List CompareTy) :
    Covers Δ (boundaryFactors Δ endpoints) := by
  intro a b hab
  constructor
  · intro q hq
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨.sub a b,hab,List.mem_append_left _ hq⟩)
  · intro q hq
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨.sub a b,hab,List.mem_append_right _ hq⟩)

theorem boundary_allowed {Δ endpoints a} (ha : a ∈ endpoints) :
    Allowed Δ (boundaryFactors Δ endpoints) a := by
  intro q hq
  exact .inr (List.mem_append_right _ (List.mem_flatMap.mpr ⟨a,ha,hq⟩))

/-- Full raw algebraic comparison has a derivation whose partial composition
factors all come from the finite input boundary. This does not assert a bound on
the number or nesting depth of uses of those factors. -/
theorem boundary_derivation_iff (Δ : Bounds) (a b : CompareTy) :
    Derivation Δ (boundaryFactors Δ [a,b]) a b ↔ AlgebraSubtype Δ a b :=
  derivation_iff (boundary_covers _ _) (boundary_allowed (by simp)) (boundary_allowed (by simp))

theorem defined_derivation_iff {Δ : Bounds} {a b : CompareTy}
    (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) :
    Derivation Δ (boundaryFactors Δ []) a b ↔ AlgebraSubtype Δ a b :=
  derivation_iff (boundary_covers _ _) (.of_defined ha) (.of_defined hb)


/-- Source obligations use the same guarded entailment, with their subtype
premises certified in the restricted proof grammar. -/
def CertifiedEntails (Δ : Bounds) (kept : List ModExpr) : CompareConstraint → Prop
  | .sub a b => Derivation Δ kept a b ∧ a.DefinedUnder Δ ∧ b.DefinedUnder Δ
  | .mode m n => Submode Δ m n
  | .defined m => Entails Δ (.defined m)
  | .equal v a => Derivation Δ kept (.var v) a ∧ Derivation Δ kept a (.var v) ∧ a.DefinedUnder Δ
  | .equiv a b => Derivation Δ kept a b ∧ Derivation Δ kept b a ∧
      a.DefinedUnder Δ ∧ b.DefinedUnder Δ

theorem certifiedEntails_iff {Δ kept c} (hc : Covers Δ kept) :
    CertifiedEntails Δ kept c ↔ AlgebraEntails Δ c := by
  cases c with
  | sub a b =>
    constructor
    · rintro ⟨h,ha,hb⟩; exact ⟨h.subtype,ha,hb⟩
    · rintro ⟨h,ha,hb⟩
      exact ⟨(derivation_iff hc (.of_defined ha) (.of_defined hb)).mpr h,ha,hb⟩
  | mode | defined => rfl
  | equal v a =>
    have hv : Allowed Δ kept (.var v) := by simp [Allowed,typeFactors]
    constructor
    · rintro ⟨hl,hu,ha⟩; exact ⟨hl.subtype,hu.subtype,ha⟩
    · rintro ⟨hl,hu,ha⟩
      exact ⟨(derivation_iff hc hv (.of_defined ha)).mpr hl,
        (derivation_iff hc (.of_defined ha) hv).mpr hu,ha⟩
  | equiv a b =>
    constructor
    · rintro ⟨hl,hu,ha,hb⟩; exact ⟨hl.subtype,hu.subtype,ha,hb⟩
    · rintro ⟨hl,hu,ha,hb⟩
      exact ⟨(derivation_iff hc (.of_defined ha) (.of_defined hb)).mpr hl,
        (derivation_iff hc (.of_defined hb) (.of_defined ha)).mpr hu,ha,hb⟩

/-- A single input-relative partial alphabet suffices for every source guard and
the body comparison. The original witness, including all shared quantified
images, is retained literally. -/
def CertifiedSubsumesUnder (ambient : Bounds) (source target : Scheme) : Prop :=
  let (nt,nm) := source.subsumptionIndices ambient target
  let (assumptions,t) := target.instantiate nt nm true
  let declared := ambient ++ assumptions.assumptions
  let kept := boundaryFactors declared [.ofTy t]
  ∃ σ, CompareInstantiates source σ ∧ σ.WellShaped declared ∧
    σ.WellFormedUnder declared ∧ (σ.ty source.body).DefinedUnder declared ∧
    (∀ c ∈ σ.bounds source.bounds, CertifiedEntails declared kept c) ∧
    Derivation declared kept (σ.ty source.body) (.ofTy t)

theorem subsumption_iff (ambient : Bounds) (source target : Scheme) :
    CertifiedSubsumesUnder ambient source target ↔ AlgebraSubsumesUnder ambient source target := by
  simp only [CertifiedSubsumesUnder,AlgebraSubsumesUnder]
  generalize source.subsumptionIndices ambient target = indices
  rcases indices with ⟨nt,nm⟩
  dsimp only
  apply exists_congr
  intro σ
  constructor
  · rintro ⟨hi,hs,hw,hbody,hb,ht⟩
    exact ⟨hi,hs,hw,hbody,fun c hc => (certifiedEntails_iff (boundary_covers _ _)).mp (hb c hc),
      ht.subtype⟩
  · rintro ⟨hi,hs,hw,hbody,hb,ht⟩
    refine ⟨hi,hs,hw,hbody,fun c hc => (certifiedEntails_iff (boundary_covers _ _)).mpr (hb c hc),?_⟩
    exact (derivation_iff (boundary_covers _ _) (.of_defined hbody)
      (boundary_allowed (by simp))).mpr ht

end
end ModalityInference.ComparisonRawModalRestriction
