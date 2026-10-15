import ModalityInference.Proofs.ComparisonReductionAlgebra

/-! One-sided envelopes and cover assembly for partial comparison images.
Total actions remain explicit; no equation distributes an action through a
partial lattice node. -/
namespace ModalityInference.ComparisonPartialCovers

structure Demand where
  endpoint : CompareTy
  action : ModExpr

def Lower (Δ : Bounds) (d : Demand) (image : CompareTy) : Prop :=
  AlgebraSubtype Δ d.endpoint (.modal image d.action)

def Upper (Δ : Bounds) (d : Demand) (image : CompareTy) : Prop :=
  AlgebraSubtype Δ (.modal image d.action) d.endpoint

def Total (Δ : Bounds) (d : Demand) : Prop :=
  Submode Δ d.action d.action

theorem join_cover {Δ : Bounds} {head : CompareTy} {rest : List CompareTy}
    {image : CompareTy}
    (hc : ∀ c ∈ head :: rest, AlgebraSubtype Δ c image) :
    AlgebraSubtype Δ (ComparisonInterpolation.join head rest) image := by
  exact (ComparisonInterpolation.algebra_join_subtype_iff head rest image).mpr hc

theorem lower_join {Δ : Bounds} {head : CompareTy} {rest : List CompareTy}
    {image : CompareTy} {d : Demand}
    (hc : ∀ c ∈ head :: rest, AlgebraSubtype Δ c image)
    (ht : Total Δ d)
    (hd : ∃ c ∈ head :: rest, Lower Δ d c) :
    Lower Δ d (ComparisonInterpolation.join head rest) := by
  have hj := join_cover hc
  obtain ⟨c, hmem, hd⟩ := hd
  have hi := (ComparisonInterpolation.algebra_join_subtype_iff head rest
    (ComparisonInterpolation.join head rest)).mp (.refl hj.wellShaped_left) c hmem
  exact hd.trans (.congr hi ht)

theorem upper_meet {Δ : Bounds} {head : CompareTy} {rest : List CompareTy}
    {d : Demand}
    (hs : (ComparisonInterpolation.meet head rest).WellShaped Δ)
    (ht : Total Δ d)
    (hd : ∃ c ∈ head :: rest, Upper Δ d c) :
    Upper Δ d (ComparisonInterpolation.meet head rest) := by
  obtain ⟨c, hmem, hd⟩ := hd
  have hp := (ComparisonInterpolation.algebra_subtype_meet_iff head rest
    (ComparisonInterpolation.meet head rest)).mp (.refl hs) c hmem
  exact (AlgebraSubtype.congr hp ht).trans hd

theorem lower_join_preserves_upper {Δ : Bounds} {head : CompareTy}
    {rest : List CompareTy} {image : CompareTy} {d : Demand}
    (hc : ∀ c ∈ head :: rest, AlgebraSubtype Δ c image)
    (ht : Total Δ d) (hd : Upper Δ d image) :
    Upper Δ d (ComparisonInterpolation.join head rest) := by
  exact (AlgebraSubtype.congr (join_cover hc) ht).trans hd

theorem meet_cover {Δ : Bounds} {head : CompareTy} {rest : List CompareTy}
    {image : CompareTy}
    (hc : ∀ c ∈ head :: rest, AlgebraSubtype Δ image c) :
    AlgebraSubtype Δ image (ComparisonInterpolation.meet head rest) := by
  exact (ComparisonInterpolation.algebra_subtype_meet_iff head rest image).mpr hc

theorem upper_meet_preserves_lower {Δ : Bounds} {head : CompareTy}
    {rest : List CompareTy} {image : CompareTy} {d : Demand}
    (hc : ∀ c ∈ head :: rest, AlgebraSubtype Δ image c)
    (ht : Total Δ d) (hd : Lower Δ d image) :
    Lower Δ d (ComparisonInterpolation.meet head rest) := by
  exact hd.trans (.congr (meet_cover hc) ht)

theorem floor_le_self {Δ : Bounds} {a : CompareTy} (ha : a.WellShaped Δ) :
    AlgebraSubtype Δ (.modal a (.const Mode.bottom)) a :=
  (AlgebraSubtype.congr (.refl ha)
    (.valid fun _ _ => ⟨Mode.bottom, Mode.identity, rfl, rfl, by decide⟩)).trans
      (.identity ha)

theorem self_le_ceiling {Δ : Bounds} {a : CompareTy} (ha : a.WellShaped Δ) :
    AlgebraSubtype Δ a (.modal a (.const Mode.top)) :=
  (AlgebraSubtype.identityRev ha).trans
    (.congr (.refl ha)
      (.valid fun _ _ => ⟨Mode.identity, Mode.top, rfl, rfl, by decide⟩))

theorem floor_le_act {Δ : Bounds} {a x : CompareTy} {m : ModExpr}
    (hx : AlgebraSubtype Δ (.modal a (.const Mode.bottom)) x)
    (hm : Submode Δ m m) :
    AlgebraSubtype Δ (.modal a (.const Mode.bottom)) (.modal x m) := by
  have hb : Submode Δ (.const Mode.bottom) (.compose (.const Mode.bottom) m) := by
    apply Submode.valid
    intro η hη
    obtain ⟨v, w, hv, _, _⟩ := hm.denote hη
    exact ⟨Mode.bottom, Mode.bottom.compose v, rfl,
      by simp [ModExpr.eval, hv], by simp [Mode.le, Mode.bottom, Mode.compose]⟩
  exact (AlgebraSubtype.congr (.refl (a := a) hx.wellShaped_left) hb).trans
    ((AlgebraSubtype.composeRev (a := a) hx.wellShaped_left).trans (.congr hx hm))

theorem act_le_ceiling {Δ : Bounds} {a x : CompareTy} {m : ModExpr}
    (hx : AlgebraSubtype Δ x (.modal a (.const Mode.top)))
    (hm : Submode Δ m m) :
    AlgebraSubtype Δ (.modal x m) (.modal a (.const Mode.top)) := by
  have ht : Submode Δ (.compose (.const Mode.top) m) (.const Mode.top) := by
    apply Submode.valid
    intro η hη
    obtain ⟨v, w, hv, _, _⟩ := hm.denote hη
    exact ⟨Mode.top.compose v, Mode.top,
      by simp [ModExpr.eval, hv], rfl, by simp [Mode.le, Mode.top, Mode.compose]⟩
  exact (AlgebraSubtype.congr hx hm).trans
    ((AlgebraSubtype.compose (a := a) hx.wellShaped_right).trans
      (.congr (.refl (a := a) hx.wellShaped_right) ht))

inductive Generated (Δ : Bounds) (atoms : List CompareTy) : CompareTy → Prop where
  | atom {a} : a ∈ atoms → Generated Δ atoms a
  | join {a b} : Generated Δ atoms a → Generated Δ atoms b →
      Generated Δ atoms (.join a b)
  | meet {a b} : Generated Δ atoms a → Generated Δ atoms b →
      Generated Δ atoms (.meet a b)
  | modal {a m} : Generated Δ atoms a → Submode Δ m m → Generated Δ atoms (.modal a m)

/-- Partial atoms need neither definedness nor distributivity. The same floor
remains below a term after every total action, including actions around meets. -/
theorem floor_le_generated {Δ : Bounds} {atoms : List CompareTy} {base a : CompareTy}
    (hb : ∀ t ∈ atoms, AlgebraSubtype Δ (.modal base (.const Mode.bottom)) t)
    (ha : Generated Δ atoms a) :
    AlgebraSubtype Δ (.modal base (.const Mode.bottom)) a := by
  induction ha with
  | atom h => exact hb _ h
  | join _ _ iha ihb =>
    exact iha.trans (.shaped (.joinLeft
      ⟨iha.wellShaped_right, ihb.wellShaped_right,
        iha.shape_equivalent.symm.trans ihb.shape_equivalent⟩))
  | meet _ _ iha ihb => exact .meetGreatest iha ihb
  | modal _ hm ih => exact floor_le_act ih hm

theorem meet_floor_le_generated {Δ : Bounds} {head : CompareTy}
    {rest : List CompareTy} {a : CompareTy}
    (hs : (ComparisonInterpolation.meet head rest).WellShaped Δ)
    (ha : Generated Δ (head :: rest) a) :
    AlgebraSubtype Δ (.modal (ComparisonInterpolation.meet head rest) (.const Mode.bottom)) a := by
  apply floor_le_generated (ha := ha)
  intro t ht
  exact (floor_le_self hs).trans
    ((ComparisonInterpolation.algebra_subtype_meet_iff head rest
      (ComparisonInterpolation.meet head rest)).mp (.refl hs) t ht)

theorem generated_le_ceiling {Δ : Bounds} {atoms : List CompareTy} {base a : CompareTy}
    (hb : ∀ t ∈ atoms, AlgebraSubtype Δ t (.modal base (.const Mode.top)))
    (ha : Generated Δ atoms a) :
    AlgebraSubtype Δ a (.modal base (.const Mode.top)) := by
  induction ha with
  | atom h => exact hb _ h
  | join _ _ iha ihb => exact .joinLeast iha ihb
  | meet _ _ iha ihb =>
    exact (AlgebraSubtype.shaped (.meetLeft
      ⟨iha.wellShaped_left, ihb.wellShaped_left,
        iha.shape_equivalent.trans ihb.shape_equivalent.symm⟩)).trans iha
  | modal _ hm ih => exact act_le_ceiling ih hm

theorem generated_le_join_ceiling {Δ : Bounds} {head : CompareTy}
    {rest : List CompareTy} {a : CompareTy}
    (hs : (ComparisonInterpolation.join head rest).WellShaped Δ)
    (ha : Generated Δ (head :: rest) a) :
    AlgebraSubtype Δ a (.modal (ComparisonInterpolation.join head rest) (.const Mode.top)) := by
  apply generated_le_ceiling (ha := ha)
  intro t ht
  exact ((ComparisonInterpolation.algebra_join_subtype_iff head rest
    (ComparisonInterpolation.join head rest)).mp (.refl hs) t ht).trans (self_le_ceiling hs)

end ModalityInference.ComparisonPartialCovers
