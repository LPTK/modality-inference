import ModalityInference.Proofs.ComparisonRawModalRestriction

/-! Compose-preserving relabelings transport raw declared type edges without
altering scalar assumptions, shape models, or any guarded modality label. -/

namespace ModalityInference.ComparisonRawModeTransport

/-- A relabeling respects root composition and fixes every guarded label. -/
structure Relabeling (Δ : Bounds) (f : ModExpr → ModExpr) : Prop where
  compose : ∀ m n, f (.compose m n) = .compose (f m) (f n)
  total : ∀ m, Entails Δ (.defined m) → f m = m

def publicType (f : ModExpr → ModExpr) : Ty → Ty
  | .var v => .var v
  | .unit => .unit
  | .credit => .credit
  | .prod a b => .prod (publicType f a) (publicType f b)
  | .sum a b => .sum (publicType f a) (publicType f b)
  | .fn a b => .fn (publicType f a) (publicType f b)
  | .modal a m => .modal (publicType f a) (f m)

def type (f : ModExpr → ModExpr) : CompareTy → CompareTy
  | .var v => .var v
  | .unit => .unit
  | .credit => .credit
  | .prod a b => .prod (type f a) (type f b)
  | .sum a b => .sum (type f a) (type f b)
  | .fn a b => .fn (type f a) (type f b)
  | .modal a m => .modal (type f a) (f m)
  | .join a b => .join (type f a) (type f b)
  | .meet a b => .meet (type f a) (type f b)

/-- Scalar assumptions are retained verbatim. Only type endpoints are relabeled. -/
def constraint (f : ModExpr → ModExpr) : Constraint → Constraint
  | .sub a b => .sub (publicType f a) (publicType f b)
  | .equiv a b => .equiv (publicType f a) (publicType f b)
  | .equal v a => .equal v (publicType f a)
  | c => c

def context (f : ModExpr → ModExpr) (Δ : Bounds) : Bounds := Δ.map (constraint f)

@[simp] theorem type_ofTy (f : ModExpr → ModExpr) (a : Ty) :
    type f (.ofTy a) = .ofTy (publicType f a) := by
  induction a <;> simp_all [type,publicType,CompareTy.ofTy]

@[simp] theorem publicType_shape (f : ModExpr → ModExpr) (a : Ty) :
    ComparisonShape.ofTy (publicType f a) = ComparisonShape.ofTy a := by
  induction a <;> simp_all [publicType,ComparisonShape.ofTy]

@[simp] theorem type_shape (f : ModExpr → ModExpr) (a : CompareTy) :
    (type f a).shape = a.shape := by
  induction a <;> simp_all [type,CompareTy.shape]

@[simp] theorem context_models (f : ModExpr → ModExpr) (Δ : Bounds) (η : ModVar → Mode) :
    ModeModels (context f Δ) η ↔ ModeModels Δ η := by
  simp only [context,ModeModels,List.forall_mem_map]
  apply forall_congr'
  intro c
  apply imp_congr_right
  intro _
  cases c <;> rfl

@[simp] theorem context_pairs (f : ModExpr → ModExpr) (Δ : Bounds) :
    ComparisonShape.pairs (context f Δ) = ComparisonShape.pairs Δ := by
  simp only [ComparisonShape.pairs,context,List.flatMap_map]
  apply List.flatMap_congr
  intro c _
  cases c <;> simp [constraint,publicType_shape]

@[simp] theorem context_shapes (f : ModExpr → ModExpr) (Δ : Bounds)
    (ρ : TypeVar → ComparisonShape) :
    ComparisonShape.Models (context f Δ) ρ ↔ ComparisonShape.Models Δ ρ := by
  simp only [ComparisonShape.Models,context_pairs]

@[simp] theorem context_equivalent (f : ModExpr → ModExpr) (Δ : Bounds) (s t : ComparisonShape) :
    ComparisonShape.Equivalent (context f Δ) s t ↔ ComparisonShape.Equivalent Δ s t := by
  simp only [ComparisonShape.Equivalent,context_shapes]

@[simp] theorem context_shaped (f : ModExpr → ModExpr) (Δ : Bounds) (a : CompareTy) :
    a.WellShaped (context f Δ) ↔ a.WellShaped Δ := by
  induction a <;> simp_all only [CompareTy.WellShaped,context_equivalent]

@[simp] theorem type_shaped (f : ModExpr → ModExpr) (Δ : Bounds) (a : CompareTy) :
    (type f a).WellShaped (context f Δ) ↔ a.WellShaped Δ := by
  induction a <;> simp_all only [type,CompareTy.WellShaped,type_shape,context_equivalent]

@[simp] theorem context_defined (f : ModExpr → ModExpr) (Δ : Bounds) (a : CompareTy) :
    a.DefinedUnder (context f Δ) ↔ a.DefinedUnder Δ := by
  simp only [CompareTy.DefinedUnder,context_models]

@[simp] theorem context_mode_defined (f : ModExpr → ModExpr) (Δ : Bounds) (m : ModExpr) :
    Entails (context f Δ) (.defined m) ↔ Entails Δ (.defined m) := by
  simp only [Entails,context_models]

theorem Relabeling.type_fixed {Δ f} (h : Relabeling Δ f) {a : CompareTy}
    (ha : a.DefinedUnder Δ) : type f a = a := by
  induction a with
  | var | unit | credit => rfl
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb
  | join a b iha ihb | meet a b iha ihb =>
    have hh : a.DefinedUnder Δ ∧ b.DefinedUnder Δ := by
      simpa only [CompareTy.definedUnder_prod_iff,CompareTy.definedUnder_sum_iff,
        CompareTy.definedUnder_fn_iff,CompareTy.definedUnder_join_iff,CompareTy.definedUnder_meet_iff] using ha
    simp only [type,iha hh.1,ihb hh.2]
  | modal a m ih =>
    have hh := CompareTy.definedUnder_modal_iff.mp ha
    simp only [type,ih hh.1,h.total m hh.2]

theorem submode_context {Δ f m n} (h : Submode Δ m n) : Submode (context f Δ) m n :=
  .valid fun _ hη => h.denote ((context_models _ _ _).mp hη)

theorem compatible_context {Δ f a b} (h : ComparisonAlgebra.Compatible Δ a b) :
    ComparisonAlgebra.Compatible (context f Δ) a b :=
  ⟨(context_shaped _ _ _).mpr h.1,(context_defined _ _ _).mpr h.2.1,
    (context_defined _ _ _).mpr h.2.2⟩

theorem equation_context {Δ f a b} (h : ComparisonAlgebra.Equation Δ a b) :
    ComparisonAlgebra.Equation (context f Δ) a b := by
  cases h with
  | distrib p hab hac => exact .distrib p (compatible_context hab) (compatible_context hac)
  | modal p hab hm => exact .modal p (compatible_context hab) ((context_mode_defined _ _ _).mpr hm)
  | scalar p hs ha hm hn =>
    exact .scalar p ((context_shaped _ _ _).mpr hs)
      ((context_defined _ _ _).mpr ha) ((context_mode_defined _ _ _).mpr hm)
      ((context_mode_defined _ _ _).mpr hn)
  | prod p hac hbd => exact .prod p (compatible_context hac) (compatible_context hbd)
  | sum p hac hbd => exact .sum p (compatible_context hac) (compatible_context hbd)
  | fn p hac hbd => exact .fn p (compatible_context hac) (compatible_context hbd)

theorem Relabeling.shaped {Δ f a b} (hf : Relabeling Δ f) (h : ShapedSubtype Δ a b) :
    ShapedSubtype (context f Δ) (type f a) (type f b) := by
  induction h with
  | refl hs => exact .refl ((type_shaped _ _ _).mpr hs)
  | trans _ _ iha ihb => exact .trans iha ihb
  | bound hb =>
    simp only [type_ofTy]
    exact .bound (List.mem_map_of_mem (f := constraint f) hb)
  | identity hs => simpa only [type,hf.total .epsilon (fun _ _ => rfl)] using
      ShapedSubtype.identity ((type_shaped _ _ _).mpr hs)
  | identityRev hs => simpa only [type,hf.total .epsilon (fun _ _ => rfl)] using
      ShapedSubtype.identityRev ((type_shaped _ _ _).mpr hs)
  | compose hs => simpa only [type,hf.compose] using
      ShapedSubtype.compose ((type_shaped _ _ _).mpr hs)
  | composeRev hs => simpa only [type,hf.compose] using
      ShapedSubtype.composeRev ((type_shaped _ _ _).mpr hs)
  | congr _ hm ih => simpa only [type,hf.total _ hm.defined.1,hf.total _ hm.defined.2] using
      ShapedSubtype.congr ih (submode_context hm)
  | prod _ _ iha ihb => exact .prod iha ihb
  | sum _ _ iha ihb => exact .sum iha ihb
  | fn _ _ hm iha ihb =>
    have hn := (Entails.defined_compose_iff.mp hm.defined.2).1
    simpa only [type,hf.total _ hm.defined.1,hf.total _ hn] using
      ShapedSubtype.fn iha ihb (submode_context hm)
  | joinLeft hs => exact .joinLeft ((type_shaped _ _ _).mpr hs)
  | joinRight hs => exact .joinRight ((type_shaped _ _ _).mpr hs)
  | meetLeft hs => exact .meetLeft ((type_shaped _ _ _).mpr hs)
  | meetRight hs => exact .meetRight ((type_shaped _ _ _).mpr hs)
  | joinLeast _ _ iha ihb => exact .joinLeast iha ihb
  | meetGreatest _ _ iha ihb => exact .meetGreatest iha ihb

theorem Relabeling.algebra {Δ f a b} (hf : Relabeling Δ f) (h : AlgebraSubtype Δ a b) :
    AlgebraSubtype (context f Δ) (type f a) (type f b) := by
  induction h with
  | shaped h => exact .shaped (hf.shaped h)
  | trans _ _ iha ihb => exact .trans iha ihb
  | equation h =>
    have hd := ComparisonDefinedCovers.equation_defined h
    rw [hf.type_fixed hd.1,hf.type_fixed hd.2]
    exact .equation (equation_context h)
  | equationRev h =>
    have hd := ComparisonDefinedCovers.equation_defined h
    rw [hf.type_fixed hd.1,hf.type_fixed hd.2]
    exact .equationRev (equation_context h)
  | congr _ hm ih => simpa only [type,hf.total _ hm.defined.1,hf.total _ hm.defined.2] using
      AlgebraSubtype.congr ih (submode_context hm)
  | prod _ _ iha ihb => exact .prod iha ihb
  | sum _ _ iha ihb => exact .sum iha ihb
  | fn _ _ hm iha ihb =>
    have hn := (Entails.defined_compose_iff.mp hm.defined.2).1
    simpa only [type,hf.total _ hm.defined.1,hf.total _ hn] using
      AlgebraSubtype.fn iha ihb (submode_context hm)
  | joinLeast _ _ iha ihb => exact .joinLeast iha ihb
  | meetGreatest _ _ iha ihb => exact .meetGreatest iha ihb
  | clamp hab hat hm _ _ ihb iht =>
    rw [hf.type_fixed hab.2.1,hf.type_fixed hab.2.2] at ihb
    rw [hf.type_fixed hab.2.2,hf.type_fixed hat.2.2] at iht
    simpa only [type,hf.type_fixed hab.2.1,hf.type_fixed hab.2.2,hf.type_fixed hat.2.2,hf.total _ hm]
      using AlgebraSubtype.clamp (compatible_context hab) (compatible_context hat)
        ((context_mode_defined _ _ _).mpr hm) ihb iht
  | clampRev hab hat hm _ _ ihb iht =>
    rw [hf.type_fixed hab.2.1,hf.type_fixed hab.2.2] at ihb
    rw [hf.type_fixed hab.2.2,hf.type_fixed hat.2.2] at iht
    simpa only [type,hf.type_fixed hab.2.1,hf.type_fixed hab.2.2,hf.type_fixed hat.2.2,hf.total _ hm]
      using AlgebraSubtype.clampRev (compatible_context hab) (compatible_context hat)
        ((context_mode_defined _ _ _).mpr hm) ihb iht

end ModalityInference.ComparisonRawModeTransport
