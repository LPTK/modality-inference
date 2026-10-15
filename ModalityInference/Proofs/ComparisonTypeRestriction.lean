import ModalityInference.Proofs.ComparisonDefinedCovers
import ModalityInference.Proofs.ComparisonShapeSolver
import ModalityInference.Proofs.ComparisonPropagationModes

/-! Defined type replacements outside the declared support preserve comparison
derivations. Replacing unused names by unit restricts a witness to input names
without changing its partial modality expressions. -/

namespace ModalityInference.ComparisonTypeRestriction

structure Fixed (Δ : Bounds) (ts : TypeVar → CompareTy) : Prop where
  shaped : ∀ v, (ts v).WellShaped Δ
  defined : ∀ v, (ts v).DefinedUnder Δ
  fixed : ∀ v ∈ Δ.typeVars, ts v = .var v

theorem shape_subst (a : CompareTy) (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr) :
    (a.subst ts ms).shape = a.shape.subst (fun v => (ts v).shape) := by
  induction a <;> simp_all [CompareTy.subst, CompareTy.shape, ComparisonShape.subst]

theorem Fixed.shape_models {Δ ts} (h : Fixed Δ ts) {ρ : TypeVar → ComparisonShape}
    (hρ : ComparisonShape.Models Δ ρ) :
    ComparisonShape.Models Δ (fun v => (ts v).shape.subst ρ) := by
  intro p hp
  have hf (v : TypeVar) (hv : v ∈ p.1.vars ∨ v ∈ p.2.vars) :
      (ts v).shape.subst ρ = ρ v := by
    have hv' : v ∈ Δ.typeVars := by
      rw [← ComparisonShapeSolver.vars_pairs]
      exact (ComparisonShapeSolver.Measure.mem_vars _ _).mpr ⟨p.1, p.2, hp, hv⟩
    rw [h.fixed v hv']
    rfl
  rw [ComparisonShapeSolver.subst_congr p.1 (fun v hv => hf v (.inl hv)),
    ComparisonShapeSolver.subst_congr p.2 (fun v hv => hf v (.inr hv))]
  exact hρ p hp

theorem Fixed.shape_equivalent {Δ ts a b} (h : Fixed Δ ts)
    (hab : ComparisonShape.Equivalent Δ a b) :
    ComparisonShape.Equivalent Δ (a.subst (fun v => (ts v).shape))
      (b.subst (fun v => (ts v).shape)) := by
  intro ρ hρ
  rw [ComparisonShapeSolver.subst_comp, ComparisonShapeSolver.subst_comp]
  exact hab _ (h.shape_models hρ)

theorem Fixed.wellShaped {Δ ts a} (h : Fixed Δ ts) (ha : CompareTy.WellShaped Δ a) :
    (a.subst ts ModExpr.var).WellShaped Δ := by
  induction a with
  | var v => exact h.shaped v
  | unit | credit => trivial
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb => exact ⟨iha ha.1, ihb ha.2⟩
  | modal a m ih => exact ih ha
  | join a b iha ihb | meet a b iha ihb =>
    exact ⟨iha ha.1, ihb ha.2.1, by simpa only [shape_subst] using h.shape_equivalent ha.2.2⟩

theorem Fixed.type_defined {Δ ts a} (h : Fixed Δ ts) (ha : CompareTy.DefinedUnder a Δ) :
    (a.subst ts ModExpr.var).DefinedUnder Δ := by
  induction a with
  | var v => exact h.defined v
  | unit | credit => simpa only [CompareTy.subst] using ha
  | prod a b iha ihb =>
    have hh := CompareTy.definedUnder_prod_iff.mp ha
    exact CompareTy.definedUnder_prod_iff.mpr ⟨iha hh.1, ihb hh.2⟩
  | sum a b iha ihb =>
    have hh := CompareTy.definedUnder_sum_iff.mp ha
    exact CompareTy.definedUnder_sum_iff.mpr ⟨iha hh.1, ihb hh.2⟩
  | fn a b iha ihb =>
    have hh := CompareTy.definedUnder_fn_iff.mp ha
    exact CompareTy.definedUnder_fn_iff.mpr ⟨iha hh.1, ihb hh.2⟩
  | join a b iha ihb =>
    have hh := CompareTy.definedUnder_join_iff.mp ha
    exact CompareTy.definedUnder_join_iff.mpr ⟨iha hh.1, ihb hh.2⟩
  | meet a b iha ihb =>
    have hh := CompareTy.definedUnder_meet_iff.mp ha
    exact CompareTy.definedUnder_meet_iff.mpr ⟨iha hh.1, ihb hh.2⟩
  | modal a m ih =>
    have hh := CompareTy.definedUnder_modal_iff.mp ha
    simpa only [CompareTy.subst, ModExpr.subst_id] using
      CompareTy.definedUnder_modal_iff.mpr ⟨ih hh.1, hh.2⟩

theorem ofTy_fixed {ts : TypeVar → CompareTy} (a : Ty)
    (h : ∀ v ∈ a.typeVars, ts v = .var v) :
    (CompareTy.ofTy a).subst ts ModExpr.var = .ofTy a := by
  induction a <;> simp_all [CompareTy.ofTy, CompareTy.subst, TypeExpr.typeVars, or_imp, forall_and]

theorem Fixed.compatible {Δ ts a b} (h : Fixed Δ ts)
    (hab : ComparisonAlgebra.Compatible Δ a b) :
    ComparisonAlgebra.Compatible Δ (a.subst ts ModExpr.var) (b.subst ts ModExpr.var) :=
  ⟨h.wellShaped hab.1, h.type_defined hab.2.1, h.type_defined hab.2.2⟩

theorem Fixed.shapedSubtype {Δ ts a b} (h : Fixed Δ ts) (hab : ShapedSubtype Δ a b) :
    ShapedSubtype Δ (a.subst ts ModExpr.var) (b.subst ts ModExpr.var) := by
  induction hab <;> try simp only [CompareTy.subst, ModExpr.subst_id] at *
  case refl a ha => exact .refl (h.wellShaped ha)
  case trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  case bound a b hc =>
    rw [ofTy_fixed a (fun v hv => h.fixed v ((Δ.mem_typeVars_iff v).mpr
      ⟨.sub a b, hc, by simp [Constraint.typeVars, hv]⟩)),
      ofTy_fixed b (fun v hv => h.fixed v ((Δ.mem_typeVars_iff v).mpr
      ⟨.sub a b, hc, by simp [Constraint.typeVars, hv]⟩))]
    exact .bound hc
  case identity a ha => exact .identity (h.wellShaped ha)
  case identityRev a ha => exact .identityRev (h.wellShaped ha)
  case compose a m n ha => exact .compose (h.wellShaped ha)
  case composeRev a m n ha => exact .composeRev (h.wellShaped ha)
  case congr _ hm ih => exact .congr ih hm
  case prod _ _ ih₁ ih₂ => exact .prod ih₁ ih₂
  case sum _ _ ih₁ ih₂ => exact .sum ih₁ ih₂
  case fn _ _ hm ih₁ ih₂ => exact .fn ih₁ ih₂ hm
  case joinLeft a b ha => exact .joinLeft (h.wellShaped ha)
  case joinRight a b ha => exact .joinRight (h.wellShaped ha)
  case joinLeast _ _ ih₁ ih₂ => exact .joinLeast ih₁ ih₂
  case meetLeft a b ha => exact .meetLeft (h.wellShaped ha)
  case meetRight a b ha => exact .meetRight (h.wellShaped ha)
  case meetGreatest _ _ ih₁ ih₂ => exact .meetGreatest ih₁ ih₂

theorem subst_typeOp (p : Bool) (a b : CompareTy) (ts : TypeVar → CompareTy) :
    (ComparisonAlgebra.typeOp p a b).subst ts ModExpr.var =
      ComparisonAlgebra.typeOp p (a.subst ts ModExpr.var) (b.subst ts ModExpr.var) := by
  cases p <;> rfl

theorem Fixed.equation {Δ ts a b} (h : Fixed Δ ts) (hab : ComparisonAlgebra.Equation Δ a b) :
    ComparisonAlgebra.Equation Δ (a.subst ts ModExpr.var) (b.subst ts ModExpr.var) := by
  cases hab <;> simp only [CompareTy.subst, subst_typeOp, ModExpr.subst_id]
  case distrib p hab hac => exact .distrib p (h.compatible hab) (h.compatible hac)
  case modal p hab hm => exact .modal p (h.compatible hab) hm
  case scalar a m n p ha hd hm hn => exact .scalar p (h.wellShaped ha) (h.type_defined hd) hm hn
  case prod p hac hbd => exact .prod p (h.compatible hac) (h.compatible hbd)
  case sum p hac hbd => exact .sum p (h.compatible hac) (h.compatible hbd)
  case fn p hac hbd => exact .fn p (h.compatible hac) (h.compatible hbd)

theorem Fixed.algebra {Δ ts a b} (h : Fixed Δ ts) (hab : AlgebraSubtype Δ a b) :
    AlgebraSubtype Δ (a.subst ts ModExpr.var) (b.subst ts ModExpr.var) := by
  induction hab <;> try simp only [CompareTy.subst, ModExpr.subst_id] at *
  case shaped hs => exact .shaped (h.shapedSubtype hs)
  case trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  case equation he => exact .equation (h.equation he)
  case equationRev he => exact .equationRev (h.equation he)
  case congr _ hm ih => exact .congr ih hm
  case prod _ _ ih₁ ih₂ => exact .prod ih₁ ih₂
  case sum _ _ ih₁ ih₂ => exact .sum ih₁ ih₂
  case fn _ _ hm ih₁ ih₂ => exact .fn ih₁ ih₂ hm
  case joinLeast _ _ ih₁ ih₂ => exact .joinLeast ih₁ ih₂
  case meetGreatest _ _ ih₁ ih₂ => exact .meetGreatest ih₁ ih₂
  case clamp hba hat hm _ _ ih₁ ih₂ => exact .clamp (h.compatible hba) (h.compatible hat) hm ih₁ ih₂
  case clampRev hba hat hm _ _ ih₁ ih₂ => exact .clampRev (h.compatible hba) (h.compatible hat) hm ih₁ ih₂

def restrict (names : Finset TypeVar) (v : TypeVar) : CompareTy :=
  if v ∈ names then .var v else .unit

theorem restrict_fixed (Δ : Bounds) (names : Finset TypeVar) (h : Δ.typeVars ⊆ names) :
    Fixed Δ (restrict names) := by
  constructor
  · intro v
    by_cases hv : v ∈ names <;> simp [restrict, hv, CompareTy.WellShaped]
  · intro v
    by_cases hv : v ∈ names <;>
      simp [restrict, hv, CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels]
  · intro v hv
    simp [restrict, h hv]

theorem restrict_support (names : Finset TypeVar) {P : TypeVar → Prop} {Q : ModVar → Prop}
    {a : CompareTy} (h : ComparisonInterpolation.Supports P Q a) :
    ComparisonInterpolation.Supports (fun v => v ∈ names) Q (a.subst (restrict names) ModExpr.var) := by
  apply h.subst
  · intro v _
    by_cases hv : v ∈ names <;> simp [restrict, hv, ComparisonInterpolation.Supports]
  · intro v hv w hw
    have he : w = v := by simpa only [ModExpr.vars, Finset.mem_singleton] using hw
    exact he ▸ hv

theorem restrict_type_support (names : Finset TypeVar) (a : CompareTy) :
    ComparisonInterpolation.Supports (fun v => v ∈ names) (fun _ => True)
      (a.subst (restrict names) ModExpr.var) := by
  apply restrict_support (P := fun _ => True)
  induction a <;> simp_all [ComparisonInterpolation.Supports]

theorem restrict_of_supported (names : Finset TypeVar) {a : CompareTy}
    (h : ComparisonInterpolation.Supports (fun v => v ∈ names) (fun _ => True) a) :
    a.subst (restrict names) ModExpr.var = a := by
  induction a <;> simp_all [CompareTy.subst, ComparisonInterpolation.Supports, restrict]

theorem restrict_interval {Δ : Bounds} {a b : Ty} {w : CompareTy}
    (hal : AlgebraSubtype Δ (.ofTy a) w) (hru : AlgebraSubtype Δ w (.ofTy b)) :
    let names := Δ.typeVars ∪ a.typeVars ∪ b.typeVars
    let c := w.subst (restrict names) ModExpr.var
    AlgebraSubtype Δ (.ofTy a) c ∧ AlgebraSubtype Δ c (.ofTy b) ∧
      ComparisonInterpolation.Supports (fun v => v ∈ names) (fun _ => True) c := by
  dsimp only
  let names := Δ.typeVars ∪ a.typeVars ∪ b.typeVars
  have hf := restrict_fixed Δ names (by intro v hv; simp [names, hv])
  have ha : (CompareTy.ofTy a).subst (restrict names) ModExpr.var = .ofTy a :=
    ofTy_fixed a (by intro v hv; simp [restrict, names, hv])
  have hb : (CompareTy.ofTy b).subst (restrict names) ModExpr.var = .ofTy b :=
    ofTy_fixed b (by intro v hv; simp [restrict, names, hv])
  exact ⟨by simpa only [ha] using hf.algebra hal,
    by simpa only [hb] using hf.algebra hru, restrict_type_support names w⟩

end ModalityInference.ComparisonTypeRestriction
