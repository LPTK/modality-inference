import ModalityInference.Proofs.ComparisonDefinedCovers

/-! Optional defined approximations use an absent lower approximation as a
formal bottom and an absent upper approximation as a formal top. These markers
are proof devices, never new type forms or returned witnesses. -/
namespace ModalityInference.ComparisonDefinedCovers

def CoverLe (Δ : Bounds) (lower : Bool) : Option CompareTy → Option CompareTy → Prop
  | none, none => True
  | none, some _ => lower = true
  | some _, none => lower = false
  | some a, some b => AlgebraSubtype Δ a b

def OfShape (Δ : Bounds) (shape : ComparisonShape) (x : Option CompareTy) : Prop :=
  ∀ a, x = some a → a.WellShaped Δ ∧ ComparisonShape.Equivalent Δ a.shape shape

def joinO (lower : Bool) : Option CompareTy → Option CompareTy → Option CompareTy :=
  (if lower then loose else strict) .join

def meetO (lower : Bool) : Option CompareTy → Option CompareTy → Option CompareTy :=
  (if lower then strict else loose) .meet

theorem OfShape.compatible {Δ s a b} (ha : OfShape Δ s (some a))
    (hb : OfShape Δ s (some b)) : (.join a b : CompareTy).WellShaped Δ :=
  ⟨(ha _ rfl).1, (hb _ rfl).1, (ha _ rfl).2.trans (hb _ rfl).2.symm⟩

theorem OfShape.normal {Δ : Bounds} {a : CompareTy} (ha : a.WellShaped Δ) (lower : Bool) :
    OfShape Δ a.shape (normal Δ lower a) := by
  intro c hc
  exact ⟨(normal_sound ha lower hc).2.shape.1, (normal_sound ha lower hc).2.shape.2.2⟩

theorem OfShape.rebase {Δ s t x} (h : OfShape Δ s x)
    (he : ComparisonShape.Equivalent Δ s t) : OfShape Δ t x :=
  fun a ha => ⟨(h a ha).1, (h a ha).2.trans he⟩

theorem CoverLe.refl {Δ s x} (lower : Bool) (hx : OfShape Δ s x) : CoverLe Δ lower x x := by
  cases x with
  | none => trivial
  | some a => exact AlgebraSubtype.refl (hx a rfl).1

theorem CoverLe.trans {Δ lower x y z} (hxy : CoverLe Δ lower x y)
    (hyz : CoverLe Δ lower y z) : CoverLe Δ lower x z := by
  cases lower <;> cases x <;> cases y <;> cases z <;> simp_all [CoverLe]
  all_goals exact hxy.trans hyz

theorem CoverLe.modal {Δ lower x y m n} (h : CoverLe Δ lower x y)
    (hm : Submode Δ m n) :
    CoverLe Δ lower (x.map (CompareTy.modal · m)) (y.map (CompareTy.modal · n)) := by
  cases x <;> cases y <;> simp_all [CoverLe]
  exact AlgebraSubtype.congr h hm

theorem CoverLe.strict_mono {Δ lower a b c d} {op : CompareTy → CompareTy → CompareTy}
    (h : ∀ {w x y z}, AlgebraSubtype Δ w y → AlgebraSubtype Δ x z →
      AlgebraSubtype Δ (op w x) (op y z))
    (ha : CoverLe Δ lower a c) (hb : CoverLe Δ lower b d) :
    CoverLe Δ lower (strict op a b) (strict op c d) := by
  cases lower <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [CoverLe, strict]

theorem CoverLe.fn {Δ lower a b c d} (ha : CoverLe Δ (!lower) c a)
    (hb : CoverLe Δ lower b d) :
    CoverLe Δ lower (strict .fn a b) (strict .fn c d) := by
  cases lower <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [CoverLe, strict]
  all_goals exact fn_congr ha hb

theorem CoverLe.join_left {Δ s lower x y} (hx : OfShape Δ s x) (hy : OfShape Δ s y) :
    CoverLe Δ lower x (joinO lower x y) := by
  cases lower <;> cases x <;> cases y <;> simp_all [CoverLe, joinO, strict, loose]
  all_goals first
    | exact AlgebraSubtype.refl (hx _ rfl).1
    | exact AlgebraSubtype.shaped (.joinLeft (hx.compatible hy))

theorem CoverLe.join_right {Δ s lower x y} (hx : OfShape Δ s x) (hy : OfShape Δ s y) :
    CoverLe Δ lower y (joinO lower x y) := by
  cases lower <;> cases x <;> cases y <;> simp_all [CoverLe, joinO, strict, loose]
  all_goals first
    | exact AlgebraSubtype.refl (hy _ rfl).1
    | exact AlgebraSubtype.shaped (.joinRight (hx.compatible hy))

theorem CoverLe.meet_left {Δ s lower x y} (hx : OfShape Δ s x) (hy : OfShape Δ s y) :
    CoverLe Δ lower (meetO lower x y) x := by
  cases lower <;> cases x <;> cases y <;> simp_all [CoverLe, meetO, strict, loose]
  all_goals first
    | exact AlgebraSubtype.refl (hx _ rfl).1
    | exact AlgebraSubtype.shaped (.meetLeft (hx.compatible hy))

theorem CoverLe.meet_right {Δ s lower x y} (hx : OfShape Δ s x) (hy : OfShape Δ s y) :
    CoverLe Δ lower (meetO lower x y) y := by
  cases lower <;> cases x <;> cases y <;> simp_all [CoverLe, meetO, strict, loose]
  all_goals first
    | exact AlgebraSubtype.refl (hy _ rfl).1
    | exact AlgebraSubtype.shaped (.meetRight (hx.compatible hy))

theorem CoverLe.join_least {Δ lower x y z} (hx : CoverLe Δ lower x z)
    (hy : CoverLe Δ lower y z) : CoverLe Δ lower (joinO lower x y) z := by
  cases lower <;> cases x <;> cases y <;> cases z <;> simp_all [CoverLe, joinO, strict, loose]
  all_goals exact AlgebraSubtype.joinLeast hx hy

theorem CoverLe.meet_greatest {Δ lower x y z} (hx : CoverLe Δ lower x y)
    (hy : CoverLe Δ lower x z) : CoverLe Δ lower x (meetO lower y z) := by
  cases lower <;> cases x <;> cases y <;> cases z <;> simp_all [CoverLe, meetO, strict, loose]
  all_goals exact AlgebraSubtype.meetGreatest hx hy

theorem CoverLe.join {Δ s lower a b c d} (ha : CoverLe Δ lower a c)
    (hb : CoverLe Δ lower b d) (hc : OfShape Δ s c) (hd : OfShape Δ s d) :
    CoverLe Δ lower (joinO lower a b) (joinO lower c d) :=
  (ha.trans (join_left hc hd)).join_least (hb.trans (join_right hc hd))

theorem CoverLe.meet {Δ s lower a b c d} (ha : CoverLe Δ lower a c)
    (hb : CoverLe Δ lower b d) (hc : OfShape Δ s a) (hd : OfShape Δ s b) :
    CoverLe Δ lower (meetO lower a b) (meetO lower c d) :=
  ((meet_left hc hd).trans ha).meet_greatest ((meet_right hc hd).trans hb)

end ModalityInference.ComparisonDefinedCovers
