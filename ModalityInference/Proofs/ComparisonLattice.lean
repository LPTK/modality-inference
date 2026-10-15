import ModalityInference.Proofs.GroundEquivalence
import ModalityInference.ComparisonShapes

/-! Effective-mode profiles expose the lattice carried by each finite ground
shape. Product and sum children already include the enclosing mode; function
domains and codomains do not inherit the closure mode. -/
namespace ModalityInference.ComparisonLattice

theorem mode_join_le (m n p : Mode) :
    (m.join n).le p = true ↔ m.le p = true ∧ n.le p = true := by
  simp [Mode.le_iff, Mode.join, Bool.or_eq_true, Bool.and_eq_true,
    or_imp, forall_and, and_assoc, and_left_comm]

theorem mode_le_meet (m n p : Mode) :
    m.le (n.meet p) = true ↔ m.le n = true ∧ m.le p = true := by
  simp [Mode.le_iff, Mode.meet, Bool.or_eq_true, Bool.and_eq_true,
    or_imp, forall_and, and_assoc, and_left_comm]

theorem mode_antisymm {m n : Mode} (hmn : m.le n = true) (hnm : n.le m = true) : m = n := by
  cases m; cases n; simp only [Mode.le_iff, Mode.mk.injEq] at *
  exact ⟨Bool.eq_iff_iff.mpr ⟨hmn.1, hnm.1⟩,
    Bool.eq_iff_iff.mpr ⟨hmn.2.1, hnm.2.1⟩, Bool.eq_iff_iff.mpr ⟨hnm.2.2, hmn.2.2⟩⟩

inductive Profile where
  | unit (mode : Mode)
  | credit (mode : Mode)
  | prod (left right : Profile) (mode : Mode)
  | sum (left right : Profile) (mode : Mode)
  | fn (domain codomain : Profile) (mode : Mode)
  deriving Repr, DecidableEq

namespace Profile

def shape : Profile → ComparisonShape
  | .unit _ => .unit
  | .credit _ => .credit
  | .prod a b _ => .prod a.shape b.shape
  | .sum a b _ => .sum a.shape b.shape
  | .fn a b _ => .fn a.shape b.shape

def clip (m : Mode) : Profile → Profile
  | .unit n => .unit (n.compose m)
  | .credit n => .credit (n.compose m)
  | .prod a b n => .prod (a.clip m) (b.clip m) (n.compose m)
  | .sum a b n => .sum (a.clip m) (b.clip m) (n.compose m)
  | .fn a b n => .fn a b ((n.compose m).compose Mode.top)

@[simp] theorem shape_clip (a : Profile) (m : Mode) : (a.clip m).shape = a.shape := by
  induction a <;> simp_all [clip, shape]

theorem clip_compose (a : Profile) (m n : Mode) :
    (a.clip m).clip n = a.clip (m.compose n) := by
  induction a <;> simp_all [clip, Mode.compose, Mode.top, Bool.and_assoc]

@[simp] theorem clip_idem (a : Profile) (m : Mode) : (a.clip m).clip m = a.clip m := by
  rw [clip_compose, Mode.compose_self]

def realize : Profile → GroundTy
  | .unit m => .unit m
  | .credit m => .credit m
  | .prod a b m => .prod a.realize b.realize m
  | .sum a b m => .sum a.realize b.realize m
  | .fn a b m => .fn a.realize b.realize m

def Valid : Profile → Prop
  | .unit _ => True
  | .credit _ => True
  | .fn a b m => a.Valid ∧ b.Valid ∧ m.unique = false
  | .prod a b m | .sum a b m =>
    a.Valid ∧ b.Valid ∧ a.clip m = a ∧ b.clip m = b

theorem clip_fixed {a : Profile} {m : Mode} (h : a.clip m = a) (n : Mode) :
    (a.clip n).clip (m.compose n) = a.clip n := by
  rw [clip_compose, Mode.compose_absorb_right, ← clip_compose, h]

theorem Valid.clip {a : Profile} (h : a.Valid) (m : Mode) : (a.clip m).Valid := by
  induction a generalizing m
  all_goals simp_all only [Profile.clip, Valid, Mode.compose, Mode.top,
    Bool.and_false, and_true, true_and]
  all_goals exact ⟨clip_fixed h.2.2.1 m, clip_fixed h.2.2.2 m⟩

def Le : Profile → Profile → Prop
  | .unit m, .unit n | .credit m, .credit n => m.le n = true
  | .prod a b m, .prod c d n | .sum a b m, .sum c d n =>
    m.le n = true ∧ Le a c ∧ Le b d
  | .fn a b m, .fn c d n => m.le n = true ∧ Le c a ∧ Le b d
  | _, _ => False
termination_by a b => sizeOf a + sizeOf b
decreasing_by all_goals simp_wf; omega

theorem Le.refl (a : Profile) : a.Le a := by
  induction a <;> simp_all [Le]

theorem Le.antisymm {a b : Profile} (hab : a.Le b) (hba : b.Le a) : a = b := by
  induction a generalizing b <;> cases b <;> simp_all only [Le]
  all_goals first
    | exact congrArg _ (mode_antisymm hab hba)
    | (rcases hab with ⟨hm, ha, hb⟩; rcases hba with ⟨hm', ha', hb'⟩
       congr 1 <;> solve_by_elim [mode_antisymm])

private theorem comparable_shape (a b : Profile) (h : a.Le b ∨ b.Le a) : a.shape = b.shape := by
  induction a generalizing b <;> cases b <;> simp_all [Le, Profile.shape]
  all_goals rcases h with ⟨_, h₁, h₂⟩ | ⟨_, h₁, h₂⟩
  all_goals constructor <;> solve_by_elim [Or.inl, Or.inr]

theorem Le.shape {a b : Profile} (h : a.Le b) : a.shape = b.shape :=
  comparable_shape a b (.inl h)

def blendMode (join : Bool) (m n : Mode) : Mode :=
  if join then m.join n else m.meet n

theorem blendMode_compose (p : Bool) (m n k : Mode) :
    blendMode p (m.compose k) (n.compose k) = (blendMode p m n).compose k := by
  cases p <;> cases m <;> cases n <;> cases k <;>
    simp [blendMode, Mode.join, Mode.meet, Mode.compose,
      Bool.and_or_distrib_right, Bool.and_assoc, Bool.and_left_comm]

@[simp] theorem blendMode_self (p : Bool) (m : Mode) : blendMode p m m = m := by
  cases p <;> cases m <;> simp [blendMode, Mode.join, Mode.meet]

def blend : Bool → Profile → Profile → Option Profile
  | p, .unit m, .unit n => some (.unit (blendMode p m n))
  | p, .credit m, .credit n => some (.credit (blendMode p m n))
  | p, .prod a b m, .prod c d n =>
    return .prod (← blend p a c) (← blend p b d) (blendMode p m n)
  | p, .sum a b m, .sum c d n =>
    return .sum (← blend p a c) (← blend p b d) (blendMode p m n)
  | p, .fn a b m, .fn c d n =>
    return .fn (← blend (!p) a c) (← blend p b d) (blendMode p m n)
  | _, _, _ => none
termination_by _ a b => sizeOf a + sizeOf b
decreasing_by all_goals simp_wf; omega

private theorem option_pair_some {α β γ : Type} (x : Option α) (y : Option β) (f : α → β → γ) :
    (∃ z, x.bind (fun a => y.bind (fun b => some (f a b))) = some z) ↔
      (∃ a, x = some a) ∧ (∃ b, y = some b) := by
  cases x <;> cases y <;> simp

theorem blend_exists_iff (p : Bool) (a b : Profile) :
    (∃ c, blend p a b = some c) ↔ a.shape = b.shape := by
  induction a generalizing p b <;> cases b <;>
    simp_all [blend, shape, bind, pure, option_pair_some]
  all_goals cases p <;> simp_all

@[simp] theorem blend_self (p : Bool) (a : Profile) : blend p a a = some a := by
  induction a generalizing p <;>
    simp_all only [blend, blendMode_self, bind, pure, Option.bind_some]

theorem blend_clip {p : Bool} {a b c : Profile} (h : blend p a b = some c) (m : Mode) :
    blend p (a.clip m) (b.clip m) = some (c.clip m) := by
  induction a generalizing p b c m with
  | prod a₁ a₂ k ih₁ ih₂ | sum a₁ a₂ k ih₁ ih₂ =>
    cases b <;> simp only [blend, reduceCtorEq, bind, pure,
      Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := h
    simp only [clip, blend, ih₁ hc₁ m, ih₂ hc₂ m, blendMode_compose,
      bind, pure, Option.bind_some]
  | fn a₁ a₂ k ih₁ ih₂ =>
    cases b <;> simp only [blend, reduceCtorEq, bind, pure,
      Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := h
    simp only [clip, blend, hc₁, hc₂, blendMode_compose, bind, pure, Option.bind_some]
  | unit k | credit k =>
    cases b <;> simp only [blend, reduceCtorEq, Option.some.injEq] at h
    subst c
    simp only [clip, blend, blendMode_compose]

theorem blend_universal {p : Bool} {a b c : Profile}
    (h : blend p a b = some c) (d : Profile) :
    (if p then Le c d ↔ Le a d ∧ Le b d
      else Le d c ↔ Le d a ∧ Le d b) := by
  induction a generalizing p b c d with
  | fn a₁ a₂ m ih₁ ih₂ =>
    cases b <;> simp only [blend, reduceCtorEq, bind, pure, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := h
    have h₁ := ih₁ hc₁
    have h₂ := ih₂ hc₂
    cases p <;> cases d <;> simp only [Bool.false_eq_true, if_false, if_true, Le, false_and]
    all_goals simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true] at h₁ h₂
    all_goals simp only [h₁, h₂]
    all_goals simp only [blendMode, Bool.false_eq_true, if_false, if_true,
      mode_join_le, mode_le_meet, and_assoc, and_left_comm, and_comm]
  | prod a₁ a₂ m ih₁ ih₂ | sum a₁ a₂ m ih₁ ih₂ =>
    cases b <;> simp only [blend, reduceCtorEq, bind, pure, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := h
    have ⟨h₁, h₂⟩ := And.intro (ih₁ hc₁) (ih₂ hc₂)
    cases p <;> cases d <;>
      simp only [Bool.false_eq_true, if_false, if_true, Le, false_and] at h₁ h₂ ⊢
    all_goals simp [h₁, h₂, blendMode, mode_join_le, mode_le_meet,
      and_assoc, and_left_comm]
  | unit m | credit m =>
    cases b <;> simp only [blend, reduceCtorEq, Option.some.injEq] at h
    subst c
    cases p <;> cases d <;> simp [Le, blendMode, mode_join_le, mode_le_meet]

private theorem bool_blend_fixed (p a b m n : Bool) (ha : (a && m) = a) (hb : (b && n) = b) :
    ((if p then a || b else a && b) && (if p then m || n else m && n)) =
      (if p then a || b else a && b) := by
  cases p <;> cases a <;> cases b <;> cases m <;> cases n <;> simp_all

theorem blendMode_fixed {a b m n : Mode}
    (ha : a.compose m = a) (hb : b.compose n = b) (p : Bool) :
    (blendMode p a b).compose (blendMode p m n) = blendMode p a b := by
  cases p <;> cases a <;> cases b <;> cases m <;> cases n
  all_goals simp only [blendMode, Mode.join, Mode.meet, Mode.compose, Bool.false_eq_true,
    if_false, if_true, Mode.mk.injEq] at *
  case false.mk.mk.mk.mk =>
    exact ⟨bool_blend_fixed false _ _ _ _ ha.1 hb.1,
      bool_blend_fixed false _ _ _ _ ha.2.1 hb.2.1,
      bool_blend_fixed true _ _ _ _ ha.2.2 hb.2.2⟩
  case true.mk.mk.mk.mk =>
    exact ⟨bool_blend_fixed true _ _ _ _ ha.1 hb.1,
      bool_blend_fixed true _ _ _ _ ha.2.1 hb.2.1,
      bool_blend_fixed false _ _ _ _ ha.2.2 hb.2.2⟩

theorem blendMode_fixed_normalized {a b m n k : Mode}
    (ha : (a.compose m).compose k = a) (hb : (b.compose n).compose k = b) (p : Bool) :
    ((blendMode p a b).compose (blendMode p m n)).compose k = blendMode p a b := by
  simpa only [blendMode_compose, Mode.compose_assoc] using
    blendMode_fixed (show a.compose (m.compose k) = a by simpa only [Mode.compose_assoc] using ha)
      (show b.compose (n.compose k) = b by simpa only [Mode.compose_assoc] using hb) p

theorem blend_fixed {p : Bool} {a b c : Profile} {m n : Mode}
    (ha : a.clip m = a) (hb : b.clip n = b) (h : blend p a b = some c) :
    c.clip (blendMode p m n) = c := by
  induction a generalizing p b c m n with
  | prod a₁ a₂ k ih₁ ih₂ | sum a₁ a₂ k ih₁ ih₂ =>
    cases b <;> simp only [blend, reduceCtorEq, bind, pure,
      Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := h
    simp only [clip, Profile.prod.injEq, Profile.sum.injEq] at ha hb ⊢
    exact ⟨ih₁ ha.1 hb.1 hc₁, ih₂ ha.2.1 hb.2.1 hc₂, blendMode_fixed ha.2.2 hb.2.2 p⟩
  | fn a₁ a₂ k ih₁ ih₂ =>
    cases b <;> simp only [blend, reduceCtorEq, bind, pure,
      Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := h
    simp only [clip, Profile.fn.injEq, true_and] at ha hb ⊢
    exact blendMode_fixed_normalized ha hb p
  | unit k | credit k =>
    cases b <;> simp only [blend, reduceCtorEq, Option.some.injEq] at h
    subst c
    simp only [clip, Profile.unit.injEq, Profile.credit.injEq] at ha hb ⊢
    exact blendMode_fixed ha hb p

theorem blend_valid {p : Bool} {a b c : Profile}
    (ha : a.Valid) (hb : b.Valid) (h : blend p a b = some c) : c.Valid := by
  induction a generalizing p b c with
  | prod a₁ a₂ k ih₁ ih₂ | sum a₁ a₂ k ih₁ ih₂ =>
    cases b <;> simp only [blend, reduceCtorEq, bind, pure,
      Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := h
    simp only [Valid] at ha hb ⊢
    exact ⟨ih₁ ha.1 hb.1 hc₁, ih₂ ha.2.1 hb.2.1 hc₂,
      blend_fixed ha.2.2.1 hb.2.2.1 hc₁, blend_fixed ha.2.2.2 hb.2.2.2 hc₂⟩
  | fn a₁ a₂ k ih₁ ih₂ =>
    cases b <;> simp only [blend, reduceCtorEq, bind, pure,
      Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := h
    exact ⟨ih₁ ha.1 hb.1 hc₁, ih₂ ha.2.1 hb.2.1 hc₂,
      by cases p <;> simp_all [blendMode, Mode.join, Mode.meet, Valid]⟩
  | unit k | credit k =>
    cases b <;> simp only [blend, reduceCtorEq, Option.some.injEq] at h
    subst c
    trivial

end Profile

def observe : GroundTy → Profile
  | .unit m => .unit m
  | .credit m => .credit m
  | .prod a b m => .prod ((observe a).clip m) ((observe b).clip m) m
  | .sum a b m => .sum ((observe a).clip m) ((observe b).clip m) m
  | .fn a b m => .fn (observe a) (observe b) (m.compose Mode.top)

theorem observe_modal (a : GroundTy) (m : Mode) : observe (a.modal m) = (observe a).clip m := by
  cases a <;> simp [GroundTy.modal, observe, Profile.clip, Profile.clip_compose,
    Mode.compose, Mode.top]

theorem observe_valid (a : GroundTy) : (observe a).Valid := by
  induction a <;> simp_all only [observe, Profile.Valid]
  all_goals simp_all [Profile.Valid.clip, Mode.compose, Mode.top]

theorem observe_realize {a : Profile} (ha : a.Valid) : observe a.realize = a := by
  induction a <;> simp_all only [Profile.Valid, Profile.realize, observe]
  all_goals (congr 1; cases ‹Mode›; simp_all [Mode.compose, Mode.top])

theorem observe_le_of_groundOrder {a b : GroundTy} (h : GroundOrder a b) :
    (observe a).Le (observe b) := by
  induction h <;> simp_all [observe, Profile.Le, observe_modal,
    Mode.le_iff, Mode.compose, Mode.top]

theorem groundOrder_of_observe_le {a b : GroundTy} (h : (observe a).Le (observe b)) :
    GroundOrder a b := by
  cases ha : a <;> cases hb : b <;> simp only [ha, hb, observe, Profile.Le] at h
  case prod.prod =>
    exact .prod h.1
      (groundOrder_of_observe_le (by simpa only [observe_modal] using h.2.1))
      (groundOrder_of_observe_le (by simpa only [observe_modal] using h.2.2))
  case sum.sum =>
    exact .sum h.1
      (groundOrder_of_observe_le (by simpa only [observe_modal] using h.2.1))
      (groundOrder_of_observe_le (by simpa only [observe_modal] using h.2.2))
  case fn.fn =>
    exact .fn (groundOrder_of_observe_le h.2.1) (groundOrder_of_observe_le h.2.2)
      (by simpa [Mode.compose, Mode.top] using ((Mode.le_iff _ _).mp h.1).1)
      (by simpa [Mode.compose, Mode.top] using ((Mode.le_iff _ _).mp h.1).2.1)
  all_goals first
    | exact .unit h
    | exact .credit h
termination_by a.nodes + b.nodes
decreasing_by all_goals simp_all [GroundTy.nodes]; omega

theorem groundOrder_iff_observe_le (a b : GroundTy) :
    GroundOrder a b ↔ (observe a).Le (observe b) :=
  ⟨observe_le_of_groundOrder, groundOrder_of_observe_le⟩

theorem equivalent_iff_observe_eq (a b : GroundTy) : a.Equivalent b ↔ observe a = observe b :=
  ⟨fun h => (observe_le_of_groundOrder h.1).antisymm (observe_le_of_groundOrder h.2),
    fun h => ⟨groundOrder_of_observe_le (h ▸ Profile.Le.refl _),
      groundOrder_of_observe_le (h ▸ Profile.Le.refl _)⟩⟩

end ModalityInference.ComparisonLattice

namespace ModalityInference.ComparisonLattice.Profile

theorem blendMode_compose_right (p : Bool) (m n k : Mode) :
    blendMode p (k.compose m) (k.compose n) = k.compose (blendMode p m n) := by
  simpa only [Mode.compose_comm] using blendMode_compose p m n k

theorem clip_blendMode (p : Bool) (a : Profile) (m n : Mode) :
    blend p (a.clip m) (a.clip n) = some (a.clip (blendMode p m n)) := by
  induction a generalizing p <;>
    simp_all only [clip, blend, blend_self, blendMode_compose, blendMode_compose_right,
      bind, pure, Option.bind_some]

end ModalityInference.ComparisonLattice.Profile
namespace ModalityInference.ComparisonLattice.Profile
private def mix : Bool → Profile → Profile → Profile
  | p, .unit m, .unit n => .unit (blendMode p m n)
  | p, .credit m, .credit n => .credit (blendMode p m n)
  | p, .prod a b m, .prod c d n => .prod (mix p a c) (mix p b d) (blendMode p m n)
  | p, .sum a b m, .sum c d n => .sum (mix p a c) (mix p b d) (blendMode p m n)
  | p, .fn a b m, .fn c d n => .fn (mix (!p) a c) (mix p b d) (blendMode p m n)
  | _, a, _ => a

private theorem blend_eq_some_mix (p : Bool) (a b : Profile) (h : a.shape = b.shape) :
    blend p a b = some (mix p a b) := by
  induction a generalizing p b <;> cases b <;>
    simp_all only [shape, reduceCtorEq, ComparisonShape.prod.injEq, ComparisonShape.sum.injEq,
      ComparisonShape.fn.injEq, blend, mix, bind, pure, Option.bind_some]
end ModalityInference.ComparisonLattice.Profile

namespace ModalityInference.ComparisonLattice.Profile

theorem blendMode_distrib (p : Bool) (a b c : Mode) :
    blendMode p a (blendMode (!p) b c) =
      blendMode (!p) (blendMode p a b) (blendMode p a c) := by
  cases p <;> cases a <;> cases b <;> cases c <;>
    simp only [blendMode, Mode.join, Mode.meet, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, Mode.mk.injEq]
  all_goals repeat' constructor
  all_goals first | exact Bool.and_or_distrib_left _ _ _ | exact Bool.or_and_distrib_left _ _ _

end ModalityInference.ComparisonLattice.Profile
namespace ModalityInference.ComparisonLattice.Profile
private theorem mix_distrib (p : Bool) (a b c : Profile)
    (hab : a.shape = b.shape) (hac : a.shape = c.shape) :
    mix p a (mix (!p) b c) = mix (!p) (mix p a b) (mix p a c) := by
  induction a generalizing p b c <;> cases b <;> cases c <;>
    simp only [shape, reduceCtorEq, ComparisonShape.prod.injEq, ComparisonShape.sum.injEq,
      ComparisonShape.fn.injEq] at hab hac
  all_goals simp only [mix]
  all_goals congr 1 <;> solve_by_elim [And.left, And.right, blendMode_distrib]
end ModalityInference.ComparisonLattice.Profile
namespace ModalityInference.ComparisonLattice.Profile
private theorem mix_eq_of_blend {p : Bool} {a b c : Profile} (h : blend p a b = some c) :
    mix p a b = c :=
  Option.some.inj ((blend_eq_some_mix p a b ((blend_exists_iff p a b).mp ⟨c, h⟩)).symm.trans h)

theorem blend_distrib {p : Bool} {a b c bc ab ac l r : Profile}
    (hbc : blend (!p) b c = some bc) (hab : blend p a b = some ab)
    (hac : blend p a c = some ac) (hl : blend p a bc = some l)
    (hr : blend (!p) ab ac = some r) : l = r := by
  rw [← mix_eq_of_blend hl, ← mix_eq_of_blend hr, ← mix_eq_of_blend hbc,
    ← mix_eq_of_blend hab, ← mix_eq_of_blend hac]
  exact mix_distrib p a b c ((blend_exists_iff p a b).mp ⟨ab, hab⟩)
    ((blend_exists_iff p a c).mp ⟨ac, hac⟩)

theorem blend_shape {p : Bool} {a b c : Profile} (h : blend p a b = some c) :
    c.shape = a.shape := by
  cases p with
  | false => exact ((blend_universal h c).mp (Le.refl c)).1.shape
  | true => exact ((blend_universal h c).mp (Le.refl c)).1.shape.symm

end ModalityInference.ComparisonLattice.Profile
namespace ModalityInference.ComparisonLattice.Profile
private theorem mix_absorb_left (p : Bool) (a b : Profile)
    (h : if p then b.Le a else a.Le b) : mix p a b = a := by
  cases p with
  | false =>
    have hb := blend_eq_some_mix false a b h.shape
    exact Le.antisymm ((blend_universal hb _).mp (Le.refl _)).1
      ((blend_universal hb a).mpr ⟨Le.refl a, h⟩)
  | true =>
    have hb := blend_eq_some_mix true a b h.shape.symm
    exact Le.antisymm ((blend_universal hb a).mpr ⟨Le.refl a, h⟩)
      ((blend_universal hb _).mp (Le.refl _)).1

end ModalityInference.ComparisonLattice.Profile
namespace ModalityInference.ComparisonLattice
private theorem bool_clamp_join (b a t m : Bool)
    (hba : b = true → a = true) (hat : a = true → t = true) :
    ((a || (b && m)) && (t && m)) = (a && m) := by
  cases b <;> cases a <;> cases t <;> cases m <;> simp_all

private theorem bool_clamp_meet (b a t m : Bool)
    (hba : a = true → b = true) (hat : t = true → a = true) :
    ((a && (b && m)) || (t && m)) = (a && m) := by
  cases b <;> cases a <;> cases t <;> cases m <;> simp_all

theorem mode_clamp {b a t : Mode} (hba : b.le a = true) (hat : a.le t = true) (m : Mode) :
    (a.join (b.compose m)).meet (t.compose m) = a.compose m := by
  cases b; cases a; cases t; cases m
  simp only [Mode.le_iff, Mode.join, Mode.meet, Mode.compose, Mode.mk.injEq] at *
  exact ⟨bool_clamp_join _ _ _ _ hba.1 hat.1, bool_clamp_join _ _ _ _ hba.2.1 hat.2.1,
    bool_clamp_meet _ _ _ _ hba.2.2 hat.2.2⟩
end ModalityInference.ComparisonLattice
namespace ModalityInference.ComparisonLattice.Profile
private theorem mix_clamp {b a t : Profile} (hba : b.Le a) (hat : a.Le t) (m : Mode) :
    mix false (mix true a (b.clip m)) (t.clip m) = a.clip m := by
  induction a generalizing b t <;> cases b <;> cases t <;> simp only [Le] at hba hat
  all_goals simp only [clip, mix, blendMode, Bool.false_eq_true, if_false, if_true]
  case fn.fn.fn =>
    simp only [Bool.not_false, Bool.not_true,
      mix_absorb_left false _ _ hba.2.1, mix_absorb_left true _ _ hat.2.1,
      mix_absorb_left true _ _ hba.2.2, mix_absorb_left false _ _ hat.2.2,
      Mode.compose_assoc, mode_clamp hba.1 hat.1]
  all_goals congr 1
  all_goals first
    | exact mode_clamp hba hat m
    | exact mode_clamp hba.1 hat.1 m
    | solve_by_elim [hba.2.1, hat.2.1, hba.2.2, hat.2.2]
end ModalityInference.ComparisonLattice.Profile
namespace ModalityInference.ComparisonLattice.Profile
theorem blend_clamp {b a t j : Profile} (hba : b.Le a) (hat : a.Le t)
    (m : Mode) (hj : blend true a (b.clip m) = some j) :
    blend false j (t.clip m) = some (a.clip m) := by
  rw [blend_eq_some_mix false j (t.clip m)
    (by simpa only [shape_clip, blend_shape hj] using hat.shape)]
  rw [← mix_eq_of_blend hj, mix_clamp hba hat m]

theorem clamp {b a t : Profile} (hba : b.Le a) (hat : a.Le t) (m : Mode) :
    (blend true a (b.clip m)).bind (fun j => blend false j (t.clip m)) = some (a.clip m) := by
  obtain ⟨j, hj⟩ := (blend_exists_iff true a (b.clip m)).mpr
    (by simpa only [shape_clip] using hba.shape.symm)
  simpa only [hj, Option.bind_some] using blend_clamp hba hat m hj
end ModalityInference.ComparisonLattice.Profile

namespace ModalityInference.ComparisonLattice

def groundBlend (p : Bool) (a b : GroundTy) : Option GroundTy :=
  (Profile.blend p (observe a) (observe b)).map Profile.realize

theorem groundBlend_observe {p : Bool} {a b c : GroundTy} (h : groundBlend p a b = some c) :
    Profile.blend p (observe a) (observe b) = some (observe c) := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  simpa only [observe_realize (Profile.blend_valid (observe_valid a) (observe_valid b) hr)] using hr

theorem groundBlend_exists_iff (p : Bool) (a b : GroundTy) :
    (∃ c, groundBlend p a b = some c) ↔ (observe a).shape = (observe b).shape := by
  constructor
  · rintro ⟨c, hc⟩
    exact (Profile.blend_exists_iff p _ _).mp ⟨observe c, groundBlend_observe hc⟩
  · intro h
    obtain ⟨r, hr⟩ := (Profile.blend_exists_iff p (observe a) (observe b)).mpr h
    exact ⟨r.realize, by simp only [groundBlend, hr, Option.map_some]⟩
end ModalityInference.ComparisonLattice
namespace ModalityInference.ComparisonLattice

theorem groundBlend_universal {p : Bool} {a b c : GroundTy}
    (h : groundBlend p a b = some c) (d : GroundTy) :
    (if p then GroundOrder c d ↔ GroundOrder a d ∧ GroundOrder b d
      else GroundOrder d c ↔ GroundOrder d a ∧ GroundOrder d b) := by
  simpa only [groundOrder_iff_observe_le] using
    Profile.blend_universal (groundBlend_observe h) (observe d)

theorem groundBlend_modal {p : Bool} {a b c : GroundTy}
    (h : groundBlend p a b = some c) (m : Mode) :
    ∃ d, groundBlend p (a.modal m) (b.modal m) = some d ∧ d.Equivalent (c.modal m) := by
  refine ⟨((observe c).clip m).realize, ?_, ?_⟩
  · simp only [groundBlend, observe_modal, Profile.blend_clip (groundBlend_observe h), Option.map_some]
  · exact (equivalent_iff_observe_eq _ _).mpr
      ((observe_realize ((observe_valid c).clip m)).trans (observe_modal c m).symm)

theorem groundBlend_mode {p : Bool} (a : GroundTy) (m n : Mode) :
    ∃ d, groundBlend p (a.modal m) (a.modal n) = some d ∧
      d.Equivalent (a.modal (Profile.blendMode p m n)) := by
  refine ⟨((observe a).clip (Profile.blendMode p m n)).realize, ?_, ?_⟩
  · simp only [groundBlend, observe_modal, Profile.clip_blendMode, Option.map_some]
  · exact (equivalent_iff_observe_eq _ _).mpr
      ((observe_realize ((observe_valid a).clip _)).trans (observe_modal a _).symm)

theorem groundBlend_distrib {p : Bool} {a b c bc ab ac l r : GroundTy}
    (hbc : groundBlend (!p) b c = some bc) (hab : groundBlend p a b = some ab)
    (hac : groundBlend p a c = some ac) (hl : groundBlend p a bc = some l)
    (hr : groundBlend (!p) ab ac = some r) : l.Equivalent r :=
  (equivalent_iff_observe_eq _ _).mpr
    (Profile.blend_distrib (groundBlend_observe hbc) (groundBlend_observe hab)
      (groundBlend_observe hac) (groundBlend_observe hl) (groundBlend_observe hr))

end ModalityInference.ComparisonLattice
namespace ModalityInference.ComparisonLattice

theorem groundBlend_clamp {b a t j : GroundTy} (hba : GroundOrder b a) (hat : GroundOrder a t)
    (m : Mode) (hj : groundBlend true a (b.modal m) = some j) :
    ∃ d, groundBlend false j (t.modal m) = some d ∧ d.Equivalent (a.modal m) := by
  refine ⟨((observe a).clip m).realize, ?_, ?_⟩
  · have h := Profile.blend_clamp (observe_le_of_groundOrder hba)
      (observe_le_of_groundOrder hat) m
      (by simpa only [observe_modal] using groundBlend_observe hj)
    simp only [groundBlend, observe_modal, h, Option.map_some]
  · exact (equivalent_iff_observe_eq _ _).mpr
      ((observe_realize ((observe_valid a).clip m)).trans (observe_modal a m).symm)

end ModalityInference.ComparisonLattice

namespace ModalityInference.CompareTy
/-- Joins and meets are interpreted only when both operands realize at the same
finite shape. Modality evaluation retains its partiality. -/
def realize (ρ : GroundAssignment) : CompareTy → Option GroundTy
  | .var v => some (ρ.types v)
  | .unit => some (.unit Mode.identity)
  | .credit => some (.credit Mode.identity)
  | .prod a b => return .prod (← a.realize ρ) (← b.realize ρ) Mode.identity
  | .sum a b => return .sum (← a.realize ρ) (← b.realize ρ) Mode.identity
  | .fn a b => return .fn (← a.realize ρ) (← b.realize ρ) Mode.identity
  | .modal a m => return (← a.realize ρ).modal (← m.eval (some ∘ ρ.modes))
  | .join a b => do ComparisonLattice.groundBlend true (← a.realize ρ) (← b.realize ρ)
  | .meet a b => do ComparisonLattice.groundBlend false (← a.realize ρ) (← b.realize ρ)

@[simp] theorem realize_ofTy (ρ : GroundAssignment) (a : Ty) :
    (CompareTy.ofTy a).realize ρ = a.realize ρ := by
  induction a <;> simp_all [CompareTy.ofTy, realize, TypeExpr.realize]

end ModalityInference.CompareTy

namespace ModalityInference.CompareTy
open ComparisonLattice

theorem realize_shape {ρ : GroundAssignment} {a : CompareTy} {x : GroundTy}
    (h : a.realize ρ = some x) :
    (observe x).shape = a.shape.subst (fun v => (observe (ρ.types v)).shape) := by
  induction a generalizing x
  case prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    simp only [realize, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨u, hu, v, hv, rfl⟩ := h
    simp only [observe, Profile.shape, Profile.shape_clip, shape, ComparisonShape.subst,
      iha hu, ihb hv]
  case join a b iha ihb | meet a b iha ihb =>
    simp only [realize, bind, Option.bind_eq_some_iff] at h
    obtain ⟨u, hu, v, hv, hb⟩ := h
    exact (Profile.blend_shape (groundBlend_observe hb)).trans (iha hu)
  case modal a m ih =>
    simp only [realize, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨u, hu, n, hn, rfl⟩ := h
    simpa only [observe_modal, Profile.shape_clip, shape] using ih hu
  case var v | unit | credit =>
    simp only [realize, Option.some.injEq] at h
    subst x
    rfl
end ModalityInference.CompareTy
