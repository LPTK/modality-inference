import ModalityInference.Proofs.ComparisonBoundDefinedness
import ModalityInference.Proofs.ComparisonReductionAlgebra

/-!
# Defined approximations of comparison types

The lower and upper approximations retain defined parts of an internal type,
pruning partial annotations in opposite lattice polarities. A successful
approximation is defined and bounds the original type in its chosen direction.
-/

namespace ModalityInference.ComparisonDefinedCovers

noncomputable section

attribute [local instance] Classical.propDecidable

def strict (op : CompareTy → CompareTy → CompareTy) : Option CompareTy → Option CompareTy → Option CompareTy
  | some a, some b => some (op a b)
  | _, _ => none

def loose (op : CompareTy → CompareTy → CompareTy) : Option CompareTy → Option CompareTy → Option CompareTy
  | none, b => b
  | a, none => a
  | some a, some b => some (op a b)

noncomputable def normal (Δ : Bounds) (lower : Bool) : CompareTy → Option CompareTy
  | .var v => some (.var v)
  | .unit => some .unit
  | .credit => some .credit
  | .prod a b => strict .prod (normal Δ lower a) (normal Δ lower b)
  | .sum a b => strict .sum (normal Δ lower a) (normal Δ lower b)
  | .fn a b => strict .fn (normal Δ (!lower) a) (normal Δ lower b)
  | .modal a m => if Entails Δ (.defined m) then (normal Δ lower a).map (CompareTy.modal · m) else none
  | .join a b => (if lower then loose else strict) .join (normal Δ lower a) (normal Δ lower b)
  | .meet a b => (if lower then strict else loose) .meet (normal Δ lower a) (normal Δ lower b)

theorem normal_defined {Δ : Bounds} {a : CompareTy} (h : a.DefinedUnder Δ) (lower : Bool) :
    normal Δ lower a = some a := by
  induction a generalizing lower with
  | var | unit | credit => rfl
  | prod a b iha ihb =>
    have hh := CompareTy.definedUnder_prod_iff.mp h
    simp [normal, iha hh.1, ihb hh.2, strict]
  | sum a b iha ihb =>
    have hh := CompareTy.definedUnder_sum_iff.mp h
    simp [normal, iha hh.1, ihb hh.2, strict]
  | fn a b iha ihb =>
    have hh := CompareTy.definedUnder_fn_iff.mp h
    simp [normal, iha hh.1, ihb hh.2, strict]
  | modal a m ih =>
    have hh := CompareTy.definedUnder_modal_iff.mp h
    simp [normal, hh.2, ih hh.1]
  | join a b iha ihb =>
    have hh := CompareTy.definedUnder_join_iff.mp h
    cases lower <;> simp [normal, iha hh.1, ihb hh.2, strict, loose]
  | meet a b iha ihb =>
    have hh := CompareTy.definedUnder_meet_iff.mp h
    cases lower <;> simp [normal, iha hh.1, ihb hh.2, strict, loose]


def Refines (Δ : Bounds) (lower : Bool) (c a : CompareTy) : Prop :=
  if lower then AlgebraSubtype Δ c a else AlgebraSubtype Δ a c

theorem Refines.refl {Δ : Bounds} (lower : Bool) {a : CompareTy} (h : a.WellShaped Δ) :
    Refines Δ lower a a := by
  cases lower <;> exact AlgebraSubtype.refl h

theorem Refines.shape {Δ : Bounds} {lower : Bool} {c a : CompareTy} (h : Refines Δ lower c a) :
    c.WellShaped Δ ∧ a.WellShaped Δ ∧ ComparisonShape.Equivalent Δ c.shape a.shape := by
  cases lower
  · exact ⟨h.wellShaped_right, h.wellShaped_left, h.shape_equivalent.symm⟩
  · exact h.shape_invariant

theorem prod_congr {Δ : Bounds} {a b c d : CompareTy}
    (ha : AlgebraSubtype Δ a c) (hb : AlgebraSubtype Δ b d) :
    AlgebraSubtype Δ (.prod a b) (.prod c d) :=
  (AlgebraSubtype.identityRev (a := .prod a b) ⟨ha.wellShaped_left, hb.wellShaped_left⟩).trans
    ((AlgebraSubtype.prod
      ((AlgebraSubtype.identity ha.wellShaped_left).trans (ha.trans (.identityRev ha.wellShaped_right)))
      ((AlgebraSubtype.identity hb.wellShaped_left).trans (hb.trans (.identityRev hb.wellShaped_right)))).trans
      (.identity ⟨ha.wellShaped_right, hb.wellShaped_right⟩))

theorem sum_congr {Δ : Bounds} {a b c d : CompareTy}
    (ha : AlgebraSubtype Δ a c) (hb : AlgebraSubtype Δ b d) :
    AlgebraSubtype Δ (.sum a b) (.sum c d) :=
  (AlgebraSubtype.identityRev (a := .sum a b) ⟨ha.wellShaped_left, hb.wellShaped_left⟩).trans
    ((AlgebraSubtype.sum
      ((AlgebraSubtype.identity ha.wellShaped_left).trans (ha.trans (.identityRev ha.wellShaped_right)))
      ((AlgebraSubtype.identity hb.wellShaped_left).trans (hb.trans (.identityRev hb.wellShaped_right)))).trans
      (.identity ⟨ha.wellShaped_right, hb.wellShaped_right⟩))

theorem fn_congr {Δ : Bounds} {a b c d : CompareTy}
    (ha : AlgebraSubtype Δ c a) (hb : AlgebraSubtype Δ b d) :
    AlgebraSubtype Δ (.fn a b) (.fn c d) :=
  (AlgebraSubtype.identityRev (a := .fn a b) ⟨ha.wellShaped_right, hb.wellShaped_left⟩).trans
    ((AlgebraSubtype.fn ha hb (.valid fun _ _ =>
      ⟨Mode.identity, Mode.identity.compose Mode.top, rfl, rfl, by decide⟩)).trans
      (.identity ⟨ha.wellShaped_left, hb.wellShaped_right⟩))

theorem Refines.prod {Δ : Bounds} {lower : Bool} {a b c d : CompareTy}
    (ha : Refines Δ lower c a) (hb : Refines Δ lower d b) :
    Refines Δ lower (.prod c d) (.prod a b) := by
  cases lower <;> exact prod_congr ha hb

theorem Refines.sum {Δ : Bounds} {lower : Bool} {a b c d : CompareTy}
    (ha : Refines Δ lower c a) (hb : Refines Δ lower d b) :
    Refines Δ lower (.sum c d) (.sum a b) := by
  cases lower <;> exact sum_congr ha hb

theorem Refines.fn {Δ : Bounds} {lower : Bool} {a b c d : CompareTy}
    (ha : Refines Δ (!lower) c a) (hb : Refines Δ lower d b) :
    Refines Δ lower (.fn c d) (.fn a b) := by
  cases lower <;> exact fn_congr ha hb

theorem Refines.join {Δ : Bounds} {lower : Bool} {a b c d : CompareTy}
    (ha : Refines Δ lower c a) (hb : Refines Δ lower d b)
    (hab : (.join a b : CompareTy).WellShaped Δ) :
    Refines Δ lower (.join c d) (.join a b) := by
  have hcd : (.join c d : CompareTy).WellShaped Δ :=
    ⟨ha.shape.1, hb.shape.1, ha.shape.2.2.trans (hab.2.2.trans hb.shape.2.2.symm)⟩
  cases lower
  · exact .joinLeast (ha.trans (.shaped (.joinLeft hcd))) (hb.trans (.shaped (.joinRight hcd)))
  · exact .joinLeast (ha.trans (.shaped (.joinLeft hab))) (hb.trans (.shaped (.joinRight hab)))

theorem Refines.meet {Δ : Bounds} {lower : Bool} {a b c d : CompareTy}
    (ha : Refines Δ lower c a) (hb : Refines Δ lower d b)
    (hab : (.meet a b : CompareTy).WellShaped Δ) :
    Refines Δ lower (.meet c d) (.meet a b) := by
  have hcd : (.meet c d : CompareTy).WellShaped Δ :=
    ⟨ha.shape.1, hb.shape.1, ha.shape.2.2.trans (hab.2.2.trans hb.shape.2.2.symm)⟩
  cases lower
  · exact .meetGreatest ((AlgebraSubtype.shaped (.meetLeft hab)).trans ha)
      ((AlgebraSubtype.shaped (.meetRight hab)).trans hb)
  · exact .meetGreatest ((AlgebraSubtype.shaped (.meetLeft hcd)).trans ha)
      ((AlgebraSubtype.shaped (.meetRight hcd)).trans hb)

theorem strict_some {op : CompareTy → CompareTy → CompareTy} {a b : Option CompareTy}
    {c : CompareTy} (h : strict op a b = some c) :
    ∃ x y, a = some x ∧ b = some y ∧ c = op x y := by
  cases a <;> cases b <;> simp_all [strict]


theorem normal_sound {Δ : Bounds} {a : CompareTy} (ha : a.WellShaped Δ)
    (lower : Bool) {c : CompareTy} (h : normal Δ lower a = some c) :
    c.DefinedUnder Δ ∧ Refines Δ lower c a := by
  induction a generalizing lower c with
  | var | unit | credit =>
    cases h
    exact ⟨by simp [CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels], Refines.refl lower ha⟩
  | prod a b iha ihb =>
    obtain ⟨x, y, hx, hy, rfl⟩ := strict_some h
    have hax := iha ha.1 lower hx
    have hby := ihb ha.2 lower hy
    exact ⟨CompareTy.definedUnder_prod_iff.mpr ⟨hax.1, hby.1⟩, hax.2.prod hby.2⟩
  | sum a b iha ihb =>
    obtain ⟨x, y, hx, hy, rfl⟩ := strict_some h
    have hax := iha ha.1 lower hx
    have hby := ihb ha.2 lower hy
    exact ⟨CompareTy.definedUnder_sum_iff.mpr ⟨hax.1, hby.1⟩, hax.2.sum hby.2⟩
  | fn a b iha ihb =>
    obtain ⟨x, y, hx, hy, rfl⟩ := strict_some h
    have hax := iha ha.1 (!lower) hx
    have hby := ihb ha.2 lower hy
    exact ⟨CompareTy.definedUnder_fn_iff.mpr ⟨hax.1, hby.1⟩, hax.2.fn hby.2⟩
  | modal a m ih =>
    simp only [normal] at h
    split at h
    · next hm =>
      cases hc : normal Δ lower a with
      | none => simp [hc] at h
      | some x =>
        simp only [hc, Option.map_some, Option.some.injEq] at h
        subst c
        have hx := ih ha lower hc
        refine ⟨CompareTy.definedUnder_modal_iff.mpr ⟨hx.1, hm⟩, ?_⟩
        cases lower <;> exact .congr hx.2 (.refl hm)
    · contradiction
  | join a b iha ihb =>
    cases lower
    · obtain ⟨x, y, hx, hy, rfl⟩ := strict_some h
      have hax := iha ha.1 false hx
      have hby := ihb ha.2.1 false hy
      exact ⟨CompareTy.definedUnder_join_iff.mpr ⟨hax.1, hby.1⟩, hax.2.join hby.2 ha⟩
    · cases hx : normal Δ true a with
      | none =>
        have hy : normal Δ true b = some c := by simpa [normal, hx, loose] using h
        have hb := ihb ha.2.1 true hy
        exact ⟨hb.1, hb.2.trans (.shaped (.joinRight ha))⟩
      | some x =>
        cases hy : normal Δ true b with
        | none =>
          have hc : x = c := by simpa [normal, hx, hy, loose] using h
          subst c
          have hb := iha ha.1 true hx
          exact ⟨hb.1, hb.2.trans (.shaped (.joinLeft ha))⟩
        | some y =>
          have hc : CompareTy.join x y = c := by simpa [normal, hx, hy, loose] using h
          subst c
          have hax := iha ha.1 true hx
          have hby := ihb ha.2.1 true hy
          exact ⟨CompareTy.definedUnder_join_iff.mpr ⟨hax.1, hby.1⟩, hax.2.join hby.2 ha⟩
  | meet a b iha ihb =>
    cases lower
    · cases hx : normal Δ false a with
      | none =>
        have hy : normal Δ false b = some c := by simpa [normal, hx, loose] using h
        have hb := ihb ha.2.1 false hy
        exact ⟨hb.1, (AlgebraSubtype.shaped (.meetRight ha)).trans hb.2⟩
      | some x =>
        cases hy : normal Δ false b with
        | none =>
          have hc : x = c := by simpa [normal, hx, hy, loose] using h
          subst c
          have hb := iha ha.1 false hx
          exact ⟨hb.1, (AlgebraSubtype.shaped (.meetLeft ha)).trans hb.2⟩
        | some y =>
          have hc : CompareTy.meet x y = c := by simpa [normal, hx, hy, loose] using h
          subst c
          have hax := iha ha.1 false hx
          have hby := ihb ha.2.1 false hy
          exact ⟨CompareTy.definedUnder_meet_iff.mpr ⟨hax.1, hby.1⟩, hax.2.meet hby.2 ha⟩
    · obtain ⟨x, y, hx, hy, rfl⟩ := strict_some h
      have hax := iha ha.1 true hx
      have hby := ihb ha.2.1 true hy
      exact ⟨CompareTy.definedUnder_meet_iff.mpr ⟨hax.1, hby.1⟩, hax.2.meet hby.2 ha⟩


theorem typeOp_defined (Δ : Bounds) (p : Bool) (a b : CompareTy) :
    (ComparisonAlgebra.typeOp p a b).DefinedUnder Δ ↔ a.DefinedUnder Δ ∧ b.DefinedUnder Δ := by
  cases p
  · exact CompareTy.definedUnder_meet_iff
  · exact CompareTy.definedUnder_join_iff

theorem modeOp_defined {Δ : Bounds} (p : Bool) {m n : ModExpr}
    (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n)) :
    Entails Δ (.defined (ComparisonAlgebra.modeOp p m n)) := by
  intro η hη
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hm η hη)
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hn η hη)
  cases p <;> simp [ComparisonAlgebra.modeOp, ModExpr.WellFormed, ModExpr.eval, hx, hy]

theorem equation_defined {Δ : Bounds} {a b : CompareTy} (h : ComparisonAlgebra.Equation Δ a b) :
    a.DefinedUnder Δ ∧ b.DefinedUnder Δ := by
  cases h
  case scalar a m n p hs ha hm hn =>
    exact ⟨CompareTy.definedUnder_modal_iff.mpr ⟨ha, modeOp_defined p hm hn⟩,
      (typeOp_defined Δ p _ _).mpr ⟨CompareTy.definedUnder_modal_iff.mpr ⟨ha, hm⟩,
        CompareTy.definedUnder_modal_iff.mpr ⟨ha, hn⟩⟩⟩
  all_goals simp_all only [typeOp_defined, ComparisonAlgebra.Compatible,
    CompareTy.definedUnder_modal_iff, CompareTy.definedUnder_prod_iff,
    CompareTy.definedUnder_sum_iff, CompareTy.definedUnder_fn_iff]
  all_goals tauto

end
end ModalityInference.ComparisonDefinedCovers
