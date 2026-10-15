import ModalityInference.Proofs.ComparisonPartialBoundary
import ModalityInference.Proofs.ComparisonReductionAlgebra

namespace ModalityInference.ComparisonPartialCarrier

/-- Lattice nodes are confined to the defined parts of a carrier. -/
def Carrier (Δ : Bounds) : CompareTy → Prop
  | .var _ | .unit | .credit => True
  | .prod a b | .sum a b | .fn a b => Carrier Δ a ∧ Carrier Δ b
  | .modal a _ => Carrier Δ a
  | .join a b | .meet a b => a.DefinedUnder Δ ∧ b.DefinedUnder Δ

theorem Carrier.of_defined {Δ : Bounds} {a : CompareTy} (h : a.DefinedUnder Δ) : Carrier Δ a := by
  induction a with
  | var | unit | credit => trivial
  | prod a b iha ihb => exact ⟨iha (CompareTy.definedUnder_prod_iff.mp h).1,
      ihb (CompareTy.definedUnder_prod_iff.mp h).2⟩
  | sum a b iha ihb => exact ⟨iha (CompareTy.definedUnder_sum_iff.mp h).1,
      ihb (CompareTy.definedUnder_sum_iff.mp h).2⟩
  | fn a b iha ihb => exact ⟨iha (CompareTy.definedUnder_fn_iff.mp h).1,
      ihb (CompareTy.definedUnder_fn_iff.mp h).2⟩
  | modal a m ih => exact ih (CompareTy.definedUnder_modal_iff.mp h).1
  | join a b _ _ => exact CompareTy.definedUnder_join_iff.mp h
  | meet a b _ _ => exact CompareTy.definedUnder_meet_iff.mp h

theorem Carrier.of_public {Δ : Bounds} (a : Ty) : Carrier Δ (.ofTy a) := by
  induction a with
  | var | unit | credit => trivial
  | modal _ _ ih => exact ih
  | prod _ _ iha ihb | sum _ _ iha ihb | fn _ _ iha ihb => exact ⟨iha, ihb⟩

open ComparisonPartialBoundary in
 theorem Carrier.interpret_dual {Δ : Bounds} {η : ModVar → Mode} (hη : ModeModels Δ η)
    (e : Bool) {a : CompareTy} (h : Carrier Δ a) :
    interpret η (!e) a = dual (interpret η e a) := by
  induction a with
  | var | unit | credit => rfl
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    simp only [interpret, iha h.1, ihb h.2, branch_dual]
  | modal a m ih =>
    simp only [interpret, scalar]
    split
    · exact ih h
    · rfl
  | join a b _ _ =>
    have hd := CompareTy.definedUnder_join_iff.mpr h
    rw [interpret_defined (!e) hη hd, interpret_defined e hη hd, dual_middle]
  | meet a b _ _ =>
    have hd := CompareTy.definedUnder_meet_iff.mpr h
    rw [interpret_defined (!e) hη hd, interpret_defined e hη hd, dual_middle]

open ComparisonPartialBoundary in
 theorem Carrier.interpret_middle {Δ : Bounds} {η : ModVar → Mode} (hη : ModeModels Δ η)
    (e : Bool) {a : CompareTy} (hc : Carrier Δ a)
    (h : interpret η e a = middle) : ModeModels a.wellFormedBounds η := by
  induction a with
  | var | unit | credit => simp [CompareTy.wellFormedBounds, ModeModels]
  | prod a b iha ihb | sum a b iha ihb =>
    obtain ⟨ha, hb⟩ := branch_eq_middle h
    simpa only [CompareTy.wellFormedBounds, ModeModels, List.mem_append, or_imp, forall_and]
      using And.intro (iha hc.1 ha) (ihb hc.2 hb)
  | fn a b iha ihb =>
    obtain ⟨ha, hb⟩ := branch_eq_middle h
    have ha' : interpret η e a = middle := by
      have hh := congrArg dual ha
      simpa only [dual_dual, dual_middle] using hh
    simpa only [CompareTy.wellFormedBounds, ModeModels, List.mem_append, or_imp, forall_and]
      using And.intro (iha hc.1 ha') (ihb hc.2 hb)
  | modal a m ih =>
    change scalar η e m (interpret η e a) = middle at h
    unfold scalar at h
    split at h
    · next hm =>
      have hh := ih hc h
      simp only [CompareTy.wellFormedBounds, ModeModels, List.mem_append, or_imp, forall_and,
        List.mem_singleton, forall_eq]
      exact ⟨hh, hm⟩
    · exact False.elim (extreme_ne_middle e h)
  | join _ _ _ _ => exact (CompareTy.definedUnder_join_iff.mpr hc) η hη
  | meet _ _ _ _ => exact (CompareTy.definedUnder_meet_iff.mpr hc) η hη

open ComparisonPartialBoundary in
 theorem Carrier.defined_of_below {Δ : Bounds} {a b : CompareTy}
    (hΔ : Δ.TypeBoundsDefined) (ha : Carrier Δ a) (hb : b.DefinedUnder Δ)
    (h : AlgebraSubtype Δ a b) : a.DefinedUnder Δ := by
  intro η hη
  have hfalse := algebra_sound false hη hΔ h
  have htrue := algebra_sound true hη hΔ h
  rw [interpret_defined false hη hb] at hfalse
  have hd : interpret η true a = dual (interpret η false a) := ha.interpret_dual hη false
  rw [interpret_defined true hη hb, hd] at htrue
  have hback := dual_le htrue
  rw [dual_middle, dual_dual] at hback
  exact ha.interpret_middle hη false (ComparisonPartialBoundary.le_antisymm hfalse hback)

open ComparisonPartialBoundary in
 theorem Carrier.defined_of_above {Δ : Bounds} {a b : CompareTy}
    (hΔ : Δ.TypeBoundsDefined) (ha : Carrier Δ a) (hb : b.DefinedUnder Δ)
    (h : AlgebraSubtype Δ b a) : a.DefinedUnder Δ := by
  intro η hη
  have hfalse := algebra_sound false hη hΔ h
  have htrue := algebra_sound true hη hΔ h
  rw [interpret_defined false hη hb] at hfalse
  have hd : interpret η true a = dual (interpret η false a) := ha.interpret_dual hη false
  rw [interpret_defined true hη hb, hd] at htrue
  have hback := dual_le htrue
  rw [dual_middle, dual_dual] at hback
  exact ha.interpret_middle hη false (ComparisonPartialBoundary.le_antisymm hback hfalse)

theorem Carrier.defined_iff {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a b : CompareTy} (ha : Carrier Δ a) (hb : Carrier Δ b)
    (hab : AlgebraSubtype Δ a b) : a.DefinedUnder Δ ↔ b.DefinedUnder Δ :=
  ⟨fun hd => hb.defined_of_above hΔ hd hab, fun hd => ha.defined_of_below hΔ hd hab⟩

inductive LowerClosure (Δ : Bounds) (S : CompareTy → Prop) : CompareTy → Prop where
  | base {a} : Carrier Δ a → a.WellShaped Δ → S a → LowerClosure Δ S a
  | lower {a b} : Carrier Δ a → AlgebraSubtype Δ a b →
      LowerClosure Δ S b → LowerClosure Δ S a
  | join {a b} : ComparisonAlgebra.Compatible Δ a b →
      LowerClosure Δ S a → LowerClosure Δ S b → LowerClosure Δ S (.join a b)

theorem LowerClosure.carrier {Δ S a} (h : LowerClosure Δ S a) : Carrier Δ a := by
  induction h with
  | base hc _ _ | lower hc _ _ _ => exact hc
  | join hc _ _ _ _ => exact hc.2

theorem LowerClosure.shaped {Δ S a} (h : LowerClosure Δ S a) : a.WellShaped Δ := by
  induction h with
  | base _ hs _ => exact hs
  | lower _ hab _ _ => exact hab.wellShaped_left
  | join hc _ _ _ _ => exact hc.1

theorem LowerClosure.bound {Δ S a t} (h : LowerClosure Δ S a)
    (hS : ∀ s, S s → AlgebraSubtype Δ s t) : AlgebraSubtype Δ a t := by
  induction h with
  | base _ _ hs => exact hS _ hs
  | lower _ hab _ ih => exact hab.trans ih
  | join _ _ _ iha ihb => exact .joinLeast iha ihb

/-- A partial boundary cannot be introduced by a join of defined covers. -/
theorem LowerClosure.partial {Δ S a} (hΔ : Δ.TypeBoundsDefined)
    (h : LowerClosure Δ S a) (ha : ¬a.DefinedUnder Δ) :
    ∃ b, S b ∧ AlgebraSubtype Δ a b := by
  induction h with
  | base _ hs hS => exact ⟨_, hS, .refl hs⟩
  | @lower a b hc hab hb ih =>
    have hn : ¬ b.DefinedUnder Δ := fun h => ha ((hc.defined_iff hΔ hb.carrier hab).mpr h)
    obtain ⟨c, hc, hbc⟩ := ih hn
    exact ⟨c, hc, hab.trans hbc⟩
  | join hc _ _ _ _ => exact False.elim (ha (CompareTy.definedUnder_join_iff.mpr hc.2))

structure LowerIdeal (Δ : Bounds) where
  mem : CompareTy → Prop
  carrier : ∀ a, mem a → Carrier Δ a
  shaped : ∀ a, mem a → a.WellShaped Δ
  lower : ∀ a b, Carrier Δ a → AlgebraSubtype Δ a b → mem b → mem a
  join : ∀ a b, ComparisonAlgebra.Compatible Δ a b → mem a → mem b → mem (.join a b)

def LowerIdeal.closure (Δ : Bounds) (S : CompareTy → Prop) : LowerIdeal Δ where
  mem := LowerClosure Δ S
  carrier := fun _ => LowerClosure.carrier
  shaped := fun _ => LowerClosure.shaped
  lower := fun _ _ => LowerClosure.lower
  join := fun _ _ => LowerClosure.join

def LowerIdeal.modalImage {Δ : Bounds} (S : LowerIdeal Δ) (m : ModExpr) : CompareTy → Prop :=
  fun a => ∃ b, S.mem b ∧ a = .modal b m

/-- A total action can be factored out of a carrier ideal without distributing
through any partial lattice operand. -/
theorem LowerIdeal.modal_factor {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (S : LowerIdeal Δ) {m : ModExpr} (hm : Submode Δ m m) {a : CompareTy}
    (h : LowerClosure Δ (S.modalImage m) a) :
    ∃ b, S.mem b ∧ AlgebraSubtype Δ a (.modal b m) := by
  induction h with
  | base _ hs hS =>
    obtain ⟨b, hb, rfl⟩ := hS
    exact ⟨b, hb, .refl hs⟩
  | lower _ hab _ ih =>
    obtain ⟨c, hc, hbc⟩ := ih
    exact ⟨c, hc, hab.trans hbc⟩
  | @join a b hc ha hb iha ihb =>
    obtain ⟨x, hx, hax⟩ := iha
    obtain ⟨y, hy, hby⟩ := ihb
    have hxdef : x.DefinedUnder Δ :=
      (CompareTy.definedUnder_modal_iff.mp
        ((S.carrier x hx).defined_of_above (a := .modal x m) hΔ hc.2.1 hax)).1
    have hydef : y.DefinedUnder Δ :=
      (CompareTy.definedUnder_modal_iff.mp
        ((S.carrier y hy).defined_of_above (a := .modal y m) hΔ hc.2.2 hby)).1
    have hxy : ComparisonAlgebra.Compatible Δ x y :=
      ⟨⟨S.shaped x hx, S.shaped y hy,
        hax.shape_equivalent.symm.trans (hc.1.2.2.trans hby.shape_equivalent)⟩, hxdef, hydef⟩
    refine ⟨.join x y, S.join x y hxy hx hy, .joinLeast ?_ ?_⟩
    · exact hax.trans (.congr (.shaped (.joinLeft hxy.1)) hm)
    · exact hby.trans (.congr (.shaped (.joinRight hxy.1)) hm)

end ModalityInference.ComparisonPartialCarrier
