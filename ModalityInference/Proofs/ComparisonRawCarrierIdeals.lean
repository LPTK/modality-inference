import ModalityInference.Proofs.ComparisonAlgebra

/-! Ideal extensions for a restricted comparison calculus.  Carrier joins and
meets need only be well-shaped; they may contain partial annotations.  The
underlying relation is supplied independently, and its soundness is used only
to recover shape compatibility. -/
namespace ModalityInference.ComparisonRawCarrierIdeals

structure Core (Δ : Bounds) where
  carrier : CompareTy → Prop
  le : CompareTy → CompareTy → Prop
  sound : ∀ {a b}, le a b → AlgebraSubtype Δ a b
  left : ∀ {a b}, le a b → carrier a
  right : ∀ {a b}, le a b → carrier b
  refl : ∀ {a}, carrier a → a.WellShaped Δ → le a a
  trans : ∀ {a b c}, le a b → le b c → le a c
  join_closed : ∀ {a b}, carrier a → carrier b → carrier (.join a b)
  meet_closed : ∀ {a b}, carrier a → carrier b → carrier (.meet a b)
  joinLeft : ∀ {a b}, carrier a → carrier b → (.join a b : CompareTy).WellShaped Δ →
    le a (.join a b)
  joinRight : ∀ {a b}, carrier a → carrier b → (.join a b : CompareTy).WellShaped Δ →
    le b (.join a b)
  joinLeast : ∀ {a b c}, le a c → le b c → le (.join a b) c
  meetLeft : ∀ {a b}, carrier a → carrier b → (.meet a b : CompareTy).WellShaped Δ →
    le (.meet a b) a
  meetRight : ∀ {a b}, carrier a → carrier b → (.meet a b : CompareTy).WellShaped Δ →
    le (.meet a b) b
  meetGreatest : ∀ {a b c}, le a b → le a c → le a (.meet b c)

variable {Δ : Bounds} (C : Core Δ)

inductive LowerClosure (S : CompareTy → Prop) : CompareTy → Prop where
  | base {a} : C.carrier a → a.WellShaped Δ → S a → LowerClosure S a
  | lower {a b} : C.le a b → LowerClosure S b → LowerClosure S a
  | join {a b} : (.join a b : CompareTy).WellShaped Δ →
      LowerClosure S a → LowerClosure S b → LowerClosure S (.join a b)

inductive UpperClosure (S : CompareTy → Prop) : CompareTy → Prop where
  | base {a} : C.carrier a → a.WellShaped Δ → S a → UpperClosure S a
  | upper {a b} : C.le a b → UpperClosure S a → UpperClosure S b
  | meet {a b} : (.meet a b : CompareTy).WellShaped Δ →
      UpperClosure S a → UpperClosure S b → UpperClosure S (.meet a b)

theorem LowerClosure.carrier {S a} (h : LowerClosure C S a) : C.carrier a := by
  induction h with
  | base hc _ _ => exact hc
  | lower h _ _ => exact C.left h
  | join _ _ _ ha hb => exact C.join_closed ha hb

theorem UpperClosure.carrier {S a} (h : UpperClosure C S a) : C.carrier a := by
  induction h with
  | base hc _ _ => exact hc
  | upper h _ _ => exact C.right h
  | meet _ _ _ ha hb => exact C.meet_closed ha hb

theorem LowerClosure.shaped {S a} (h : LowerClosure C S a) : a.WellShaped Δ := by
  cases h with
  | base _ hs _ => exact hs
  | lower h _ => exact (C.sound h).wellShaped_left
  | join hs _ _ => exact hs

theorem UpperClosure.shaped {S a} (h : UpperClosure C S a) : a.WellShaped Δ := by
  cases h with
  | base _ hs _ => exact hs
  | upper h _ => exact (C.sound h).wellShaped_right
  | meet hs _ _ => exact hs

structure LowerIdeal where
  mem : CompareTy → Prop
  carrier : ∀ {a}, mem a → C.carrier a
  shaped : ∀ {a}, mem a → a.WellShaped Δ
  lower : ∀ {a b}, C.le a b → mem b → mem a
  join : ∀ {a b}, (.join a b : CompareTy).WellShaped Δ → mem a → mem b → mem (.join a b)

structure UpperIdeal where
  mem : CompareTy → Prop
  carrier : ∀ {a}, mem a → C.carrier a
  shaped : ∀ {a}, mem a → a.WellShaped Δ
  upper : ∀ {a b}, C.le a b → mem a → mem b
  meet : ∀ {a b}, (.meet a b : CompareTy).WellShaped Δ → mem a → mem b → mem (.meet a b)

def LowerIdeal.closure (S : CompareTy → Prop) : LowerIdeal C where
  mem := LowerClosure C S
  carrier := LowerClosure.carrier C
  shaped := LowerClosure.shaped C
  lower := LowerClosure.lower
  join := LowerClosure.join

def UpperIdeal.closure (S : CompareTy → Prop) : UpperIdeal C where
  mem := UpperClosure C S
  carrier := UpperClosure.carrier C
  shaped := UpperClosure.shaped C
  upper := UpperClosure.upper
  meet := UpperClosure.meet

theorem LowerClosure.lift {S a} (h : LowerClosure C S a) (T : LowerIdeal C)
    (hS : ∀ {s}, S s → C.carrier s → s.WellShaped Δ → T.mem s) : T.mem a := by
  induction h with
  | base hc hs hb => exact hS hb hc hs
  | lower h _ ih => exact T.lower h ih
  | join hs _ _ ha hb => exact T.join hs ha hb

theorem UpperClosure.lift {S a} (h : UpperClosure C S a) (T : UpperIdeal C)
    (hS : ∀ {s}, S s → C.carrier s → s.WellShaped Δ → T.mem s) : T.mem a := by
  induction h with
  | base hc hs hb => exact hS hb hc hs
  | upper h _ ih => exact T.upper h ih
  | meet hs _ _ ha hb => exact T.meet hs ha hb

def LowerIdeal.principal (a : CompareTy) : LowerIdeal C where
  mem b := C.le b a
  carrier := C.left
  shaped h := (C.sound h).wellShaped_left
  lower := C.trans
  join _ := C.joinLeast

def UpperIdeal.principal (a : CompareTy) : UpperIdeal C where
  mem b := C.le a b
  carrier := C.right
  shaped h := (C.sound h).wellShaped_right
  upper h₁ h₂ := C.trans h₂ h₁
  meet _ := C.meetGreatest

def image (f : CompareTy → CompareTy) (S : CompareTy → Prop) : CompareTy → Prop :=
  fun a => ∃ b, S b ∧ a = f b

/-- A monotone shape-preserving map need not preserve joins or meets. -/
structure Map where
  toFun : CompareTy → CompareTy
  carrier : ∀ {a}, C.carrier a → C.carrier (toFun a)
  shaped : ∀ {a}, a.WellShaped Δ → (toFun a).WellShaped Δ
  shape : ∀ a, ComparisonShape.Equivalent Δ (toFun a).shape a.shape
  mono : ∀ {a b}, C.le a b → C.le (toFun a) (toFun b)

theorem LowerIdeal.factor (S : LowerIdeal C) (f : Map C) {a}
    (h : LowerClosure C (image f.toFun S.mem) a) :
    ∃ b, S.mem b ∧ C.le a (f.toFun b) := by
  induction h with
  | base hc hs hb =>
    obtain ⟨b,hb,rfl⟩ := hb
    exact ⟨b,hb,C.refl hc hs⟩
  | lower h _ ih =>
    obtain ⟨b,hb,hb'⟩ := ih
    exact ⟨b,hb,C.trans h hb'⟩
  | @join a b hs _ _ iha ihb =>
    obtain ⟨x,hx,hax⟩ := iha
    obtain ⟨y,hy,hby⟩ := ihb
    have hxy : (.join x y : CompareTy).WellShaped Δ := by
      refine ⟨S.shaped hx,S.shaped hy,?_⟩
      exact (f.shape x).symm.trans ((C.sound hax).shape_equivalent.symm.trans
        (hs.2.2.trans ((C.sound hby).shape_equivalent.trans (f.shape y))))
    exact ⟨.join x y,S.join hxy hx hy,C.joinLeast
      (C.trans hax (f.mono (C.joinLeft (S.carrier hx) (S.carrier hy) hxy)))
      (C.trans hby (f.mono (C.joinRight (S.carrier hx) (S.carrier hy) hxy)))⟩

theorem UpperIdeal.factor (S : UpperIdeal C) (f : Map C) {a}
    (h : UpperClosure C (image f.toFun S.mem) a) :
    ∃ b, S.mem b ∧ C.le (f.toFun b) a := by
  induction h with
  | base hc hs hb =>
    obtain ⟨b,hb,rfl⟩ := hb
    exact ⟨b,hb,C.refl hc hs⟩
  | upper h _ ih =>
    obtain ⟨b,hb,hb'⟩ := ih
    exact ⟨b,hb,C.trans hb' h⟩
  | @meet a b hs _ _ iha ihb =>
    obtain ⟨x,hx,hxa⟩ := iha
    obtain ⟨y,hy,hyb⟩ := ihb
    have hxy : (.meet x y : CompareTy).WellShaped Δ := by
      refine ⟨S.shaped hx,S.shaped hy,?_⟩
      exact (f.shape x).symm.trans ((C.sound hxa).shape_equivalent.trans
        (hs.2.2.trans ((C.sound hyb).shape_equivalent.symm.trans (f.shape y))))
    exact ⟨.meet x y,S.meet hxy hx hy,C.meetGreatest
      (C.trans (f.mono (C.meetLeft (S.carrier hx) (S.carrier hy) hxy)) hxa)
      (C.trans (f.mono (C.meetRight (S.carrier hx) (S.carrier hy) hxy)) hyb)⟩

def Map.id : Map C where
  toFun a := a
  carrier h := h
  shaped h := h
  shape _ _ _ := rfl
  mono h := h

def Map.comp (g f : Map C) : Map C where
  toFun a := g.toFun (f.toFun a)
  carrier h := g.carrier (f.carrier h)
  shaped h := g.shaped (f.shaped h)
  shape a := (g.shape (f.toFun a)).trans (f.shape a)
  mono h := g.mono (f.mono h)

def LowerIdeal.extend (S : LowerIdeal C) (f : Map C) : LowerIdeal C :=
  .closure C (image f.toFun S.mem)

def UpperIdeal.extend (S : UpperIdeal C) (f : Map C) : UpperIdeal C :=
  .closure C (image f.toFun S.mem)

theorem LowerIdeal.extend_mem (S : LowerIdeal C) (f : Map C) {a} (ha : S.mem a) :
    (S.extend C f).mem (f.toFun a) :=
  .base (f.carrier (S.carrier ha)) (f.shaped (S.shaped ha)) ⟨a,ha,rfl⟩

theorem UpperIdeal.extend_mem (S : UpperIdeal C) (f : Map C) {a} (ha : S.mem a) :
    (S.extend C f).mem (f.toFun a) :=
  .base (f.carrier (S.carrier ha)) (f.shaped (S.shaped ha)) ⟨a,ha,rfl⟩

theorem LowerIdeal.extend_iff (S : LowerIdeal C) (f : Map C) (a : CompareTy) :
    (S.extend C f).mem a ↔ ∃ b, S.mem b ∧ C.le a (f.toFun b) := by
  constructor
  · exact S.factor C f
  · rintro ⟨b,hb,hab⟩
    exact (S.extend C f).lower hab (S.extend_mem C f hb)

theorem UpperIdeal.extend_iff (S : UpperIdeal C) (f : Map C) (a : CompareTy) :
    (S.extend C f).mem a ↔ ∃ b, S.mem b ∧ C.le (f.toFun b) a := by
  constructor
  · exact S.factor C f
  · rintro ⟨b,hb,hba⟩
    exact (S.extend C f).upper hba (S.extend_mem C f hb)

theorem LowerIdeal.extend_id (S : LowerIdeal C) (a : CompareTy) :
    (S.extend C (Map.id C)).mem a ↔ S.mem a := by
  rw [S.extend_iff]
  constructor
  · rintro ⟨b,hb,hab⟩
    exact S.lower hab hb
  · intro ha
    exact ⟨a,ha,C.refl (S.carrier ha) (S.shaped ha)⟩

theorem UpperIdeal.extend_id (S : UpperIdeal C) (a : CompareTy) :
    (S.extend C (Map.id C)).mem a ↔ S.mem a := by
  rw [S.extend_iff]
  constructor
  · rintro ⟨b,hb,hba⟩
    exact S.upper hba hb
  · intro ha
    exact ⟨a,ha,C.refl (S.carrier ha) (S.shaped ha)⟩

/-- Composition uses directed carrier joins to factor intermediate covers.
No action is distributed over a join containing a partial operand. -/
theorem LowerIdeal.extend_comp (S : LowerIdeal C) (f g : Map C) (a : CompareTy) :
    ((S.extend C f).extend C g).mem a ↔ (S.extend C (g.comp C f)).mem a := by
  rw [(S.extend C f).extend_iff,S.extend_iff]
  constructor
  · rintro ⟨b,hb,hab⟩
    obtain ⟨c,hc,hbc⟩ := (S.extend_iff C f b).mp hb
    exact ⟨c,hc,C.trans hab (g.mono hbc)⟩
  · rintro ⟨b,hb,hab⟩
    exact ⟨f.toFun b,S.extend_mem C f hb,hab⟩

theorem UpperIdeal.extend_comp (S : UpperIdeal C) (f g : Map C) (a : CompareTy) :
    ((S.extend C f).extend C g).mem a ↔ (S.extend C (g.comp C f)).mem a := by
  rw [(S.extend C f).extend_iff,S.extend_iff]
  constructor
  · rintro ⟨b,hb,hba⟩
    obtain ⟨c,hc,hcb⟩ := (S.extend_iff C f b).mp hb
    exact ⟨c,hc,C.trans (g.mono hcb) hba⟩
  · rintro ⟨b,hb,hba⟩
    exact ⟨f.toFun b,S.extend_mem C f hb,hba⟩

theorem LowerIdeal.extend_principal (f : Map C) {a} (hc : C.carrier a)
    (hs : a.WellShaped Δ) (b : CompareTy) :
    ((LowerIdeal.principal C a).extend C f).mem b ↔ C.le b (f.toFun a) := by
  rw [LowerIdeal.extend_iff]
  constructor
  · rintro ⟨c,hc,hbc⟩
    exact C.trans hbc (f.mono hc)
  · intro hb
    exact ⟨a,C.refl hc hs,hb⟩

theorem UpperIdeal.extend_principal (f : Map C) {a} (hc : C.carrier a)
    (hs : a.WellShaped Δ) (b : CompareTy) :
    ((UpperIdeal.principal C a).extend C f).mem b ↔ C.le (f.toFun a) b := by
  rw [UpperIdeal.extend_iff]
  constructor
  · rintro ⟨c,hc,hcb⟩
    exact C.trans (f.mono hc) hcb
  · intro hb
    exact ⟨a,C.refl hc hs,hb⟩

theorem LowerIdeal.extend_mono {S T : LowerIdeal C} {f g : Map C}
    (hST : ∀ a, S.mem a → T.mem a)
    (hfg : ∀ a, S.mem a → C.le (f.toFun a) (g.toFun a)) {a}
    (ha : (S.extend C f).mem a) : (T.extend C g).mem a := by
  obtain ⟨b,hb,hab⟩ := (S.extend_iff C f a).mp ha
  exact (T.extend_iff C g a).mpr ⟨b,hST b hb,C.trans hab (hfg b hb)⟩

theorem UpperIdeal.extend_mono {S T : UpperIdeal C} {f g : Map C}
    (hST : ∀ a, S.mem a → T.mem a)
    (hgf : ∀ a, S.mem a → C.le (g.toFun a) (f.toFun a)) {a}
    (ha : (S.extend C f).mem a) : (T.extend C g).mem a := by
  obtain ⟨b,hb,hba⟩ := (S.extend_iff C f a).mp ha
  exact (T.extend_iff C g a).mpr ⟨b,hST b hb,C.trans (hgf b hb) hba⟩

def Direction (reverse : Bool) (a b : CompareTy) : Prop :=
  if reverse then C.le b a else C.le a b

theorem direction_flip (p : Bool) (a b : CompareTy) :
    Direction C (!p) a b ↔ Direction C p b a := by
  cases p <;> rfl

/-- Finite compatible subsets have a common bound in the indicated direction. -/
structure Family (reverse : Bool) where
  mem : CompareTy → Prop
  carrier : ∀ {a}, mem a → C.carrier a
  shaped : ∀ {a}, mem a → a.WellShaped Δ
  merge : ∀ {a b}, mem a → mem b → ComparisonShape.Equivalent Δ a.shape b.shape →
    ∃ c, mem c ∧ Direction C reverse a c ∧ Direction C reverse b c

def LowerIdeal.family (S : LowerIdeal C) : Family C false where
  mem := S.mem
  carrier := S.carrier
  shaped := S.shaped
  merge ha hb hab :=
    ⟨.join _ _,S.join ⟨S.shaped ha,S.shaped hb,hab⟩ ha hb,
      C.joinLeft (S.carrier ha) (S.carrier hb) ⟨S.shaped ha,S.shaped hb,hab⟩,
      C.joinRight (S.carrier ha) (S.carrier hb) ⟨S.shaped ha,S.shaped hb,hab⟩⟩

def UpperIdeal.family (S : UpperIdeal C) : Family C true where
  mem := S.mem
  carrier := S.carrier
  shaped := S.shaped
  merge ha hb hab :=
    ⟨.meet _ _,S.meet ⟨S.shaped ha,S.shaped hb,hab⟩ ha hb,
      C.meetLeft (S.carrier ha) (S.carrier hb) ⟨S.shaped ha,S.shaped hb,hab⟩,
      C.meetRight (S.carrier ha) (S.carrier hb) ⟨S.shaped ha,S.shaped hb,hab⟩⟩

structure BinaryMap (leftReverse rightReverse : Bool) where
  toFun : CompareTy → CompareTy → CompareTy
  carrier : ∀ {a b}, C.carrier a → C.carrier b → C.carrier (toFun a b)
  shaped : ∀ {a b}, a.WellShaped Δ → b.WellShaped Δ → (toFun a b).WellShaped Δ
  separate : ∀ {a b c d}, ComparisonShape.Equivalent Δ (toFun a b).shape (toFun c d).shape →
    ComparisonShape.Equivalent Δ a.shape c.shape ∧ ComparisonShape.Equivalent Δ b.shape d.shape
  mono : ∀ {a b c d}, Direction C leftReverse a c → Direction C rightReverse b d →
    C.le (toFun a b) (toFun c d)

def binaryImage (f : CompareTy → CompareTy → CompareTy)
    (S T : CompareTy → Prop) : CompareTy → Prop :=
  fun a => ∃ b c, S b ∧ T c ∧ a = f b c

theorem LowerClosure.factor₂ {p q} (S : Family C p) (T : Family C q)
    (f : BinaryMap C p q) {a} (h : LowerClosure C (binaryImage f.toFun S.mem T.mem) a) :
    ∃ x y, S.mem x ∧ T.mem y ∧ C.le a (f.toFun x y) := by
  induction h with
  | base hc hs hb =>
    obtain ⟨x,y,hx,hy,rfl⟩ := hb
    exact ⟨x,y,hx,hy,C.refl hc hs⟩
  | lower h _ ih =>
    obtain ⟨x,y,hx,hy,hxy⟩ := ih
    exact ⟨x,y,hx,hy,C.trans h hxy⟩
  | @join a b hs _ _ iha ihb =>
    obtain ⟨x,y,hx,hy,haxy⟩ := iha
    obtain ⟨u,v,hu,hv,hbuv⟩ := ihb
    have hh := f.separate ((C.sound haxy).shape_equivalent.symm.trans
      (hs.2.2.trans (C.sound hbuv).shape_equivalent))
    obtain ⟨z,hz,hxz,huz⟩ := S.merge hx hu hh.1
    obtain ⟨w,hw,hyw,hvw⟩ := T.merge hy hv hh.2
    exact ⟨z,w,hz,hw,C.joinLeast (C.trans haxy (f.mono hxz hyw))
      (C.trans hbuv (f.mono huz hvw))⟩

theorem UpperClosure.factor₂ {p q} (S : Family C (!p)) (T : Family C (!q))
    (f : BinaryMap C p q) {a} (h : UpperClosure C (binaryImage f.toFun S.mem T.mem) a) :
    ∃ x y, S.mem x ∧ T.mem y ∧ C.le (f.toFun x y) a := by
  induction h with
  | base hc hs hb =>
    obtain ⟨x,y,hx,hy,rfl⟩ := hb
    exact ⟨x,y,hx,hy,C.refl hc hs⟩
  | upper h _ ih =>
    obtain ⟨x,y,hx,hy,hxy⟩ := ih
    exact ⟨x,y,hx,hy,C.trans hxy h⟩
  | @meet a b hs _ _ iha ihb =>
    obtain ⟨x,y,hx,hy,hxya⟩ := iha
    obtain ⟨u,v,hu,hv,huvb⟩ := ihb
    have hh := f.separate ((C.sound hxya).shape_equivalent.trans
      (hs.2.2.trans (C.sound huvb).shape_equivalent.symm))
    obtain ⟨z,hz,hxz,huz⟩ := S.merge hx hu hh.1
    obtain ⟨w,hw,hyw,hvw⟩ := T.merge hy hv hh.2
    exact ⟨z,w,hz,hw,C.meetGreatest
      (C.trans (f.mono ((direction_flip C p x z).mp hxz)
        ((direction_flip C q y w).mp hyw)) hxya)
      (C.trans (f.mono ((direction_flip C p u z).mp huz)
        ((direction_flip C q v w).mp hvw)) huvb)⟩

end ModalityInference.ComparisonRawCarrierIdeals
