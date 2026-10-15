import ModalityInference.Proofs.ComparisonWitnessShapes
import ModalityInference.Proofs.ComparisonDefinedCovers
import ModalityInference.Proofs.ModeWitness

/-! Total changes to modality variables outside the declared support preserve
the comparison algebra, including its partial syntax and guarded equations. -/
namespace ModalityInference.ComparisonModeRestriction

structure Fixed (Δ : Bounds) (ms : ModVar → ModExpr) : Prop where
  total : ∀ η, ModeModels Δ η → ∀ v, (ms v).WellFormed η
  fixed : ∀ v ∈ Δ.modVars, ms v = .var v

theorem Fixed.pullback {Δ ms} (h : Fixed Δ ms) {η : ModVar → Mode}
    (hη : ModeModels Δ η) :
    ∃ θ, (∀ v, (ms v).eval (some ∘ η) = some (θ v)) ∧ ModeModels Δ θ := by
  let θ : ModVar → Mode := fun v => ((ms v).eval (some ∘ η)).getD Mode.identity
  have he : ∀ v, (ms v).eval (some ∘ η) = some (θ v) := by
    intro v
    have hv := h.total η hη v
    cases hx : (ms v).eval (some ∘ η) <;> simp_all [ModExpr.WellFormed, θ]
  refine ⟨θ, he, (ModeModels.congr Δ ?_).mpr hη⟩
  intro v hv
  have hh := he v
  rw [h.fixed v hv] at hh
  exact (Option.some.inj hh).symm

theorem Fixed.defined {Δ ms m} (h : Fixed Δ ms) (hm : Entails Δ (.defined m)) :
    Entails Δ (.defined (m.subst ms)) := by
  intro η hη
  obtain ⟨θ, he, hθ⟩ := h.pullback hη
  have hf : (fun v => (ms v).eval (some ∘ η)) = some ∘ θ := funext he
  simpa only [ModExpr.WellFormed, ModExpr.eval_subst, hf] using hm θ hθ

theorem Fixed.submode {Δ ms m n} (h : Fixed Δ ms) (hmn : Submode Δ m n) :
    Submode Δ (m.subst ms) (n.subst ms) := by
  apply Submode.valid
  intro η hη
  obtain ⟨θ, he, hθ⟩ := h.pullback hη
  obtain ⟨x, y, hx, hy, hxy⟩ := hmn.denote hθ
  have hf : (fun v => (ms v).eval (some ∘ η)) = some ∘ θ := funext he
  exact ⟨x, y, by simpa only [ModExpr.eval_subst, hf] using hx,
    by simpa only [ModExpr.eval_subst, hf] using hy, hxy⟩

theorem Fixed.type_defined {Δ ms a} (h : Fixed Δ ms) (ha : CompareTy.DefinedUnder a Δ) :
    (a.subst CompareTy.var ms).DefinedUnder Δ := by
  induction a with
  | var | unit | credit => simpa [CompareTy.subst] using ha
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
    exact CompareTy.definedUnder_modal_iff.mpr ⟨ih hh.1, h.defined hh.2⟩

theorem ofTy_fixed {ms : ModVar → ModExpr} (a : Ty)
    (h : ∀ v ∈ a.modVars, ms v = .var v) :
    (CompareTy.ofTy a).subst CompareTy.var ms = .ofTy a := by
  induction a with
  | var | unit | credit => rfl
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    simp only [TypeExpr.modVars, Finset.mem_union, or_imp, forall_and] at h
    simp [CompareTy.ofTy, CompareTy.subst, iha h.1, ihb h.2]
  | modal a m ih =>
    have hm : m.subst ms = m := by
      rw [ModExpr.subst_congr m (τ := ModExpr.var) (fun v hv => h v (by simp [TypeExpr.modVars, hv]))]
      exact ModExpr.subst_id m
    simp [CompareTy.ofTy, CompareTy.subst, hm,
      ih (fun v hv => h v (by simp [TypeExpr.modVars, hv]))]

theorem Fixed.compatible {Δ ms a b} (h : Fixed Δ ms)
    (hab : ComparisonAlgebra.Compatible Δ a b) :
    ComparisonAlgebra.Compatible Δ (a.subst CompareTy.var ms) (b.subst CompareTy.var ms) :=
  ⟨(CompareTy.wellShaped_subst_modes_iff (.join a b) ms).mpr hab.1,
    h.type_defined hab.2.1, h.type_defined hab.2.2⟩

theorem Fixed.shaped {Δ ms a b} (h : Fixed Δ ms) (hab : ShapedSubtype Δ a b) :
    ShapedSubtype Δ (a.subst CompareTy.var ms) (b.subst CompareTy.var ms) := by
  induction hab <;> try simp only [CompareTy.subst]
  case refl a ha => exact .refl ((a.wellShaped_subst_modes_iff ms).mpr ha)
  case trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  case bound a b hc =>
    rw [ofTy_fixed a (fun v hv => h.fixed v ((Δ.mem_modVars_iff v).mpr
      ⟨.sub a b, hc, by simp [Constraint.modVars, hv]⟩)),
      ofTy_fixed b (fun v hv => h.fixed v ((Δ.mem_modVars_iff v).mpr
      ⟨.sub a b, hc, by simp [Constraint.modVars, hv]⟩))]
    exact .bound hc
  case identity a ha => exact .identity ((a.wellShaped_subst_modes_iff ms).mpr ha)
  case identityRev a ha => exact .identityRev ((a.wellShaped_subst_modes_iff ms).mpr ha)
  case compose a m n ha => exact .compose ((a.wellShaped_subst_modes_iff ms).mpr ha)
  case composeRev a m n ha => exact .composeRev ((a.wellShaped_subst_modes_iff ms).mpr ha)
  case congr _ hm ih => exact .congr ih (h.submode hm)
  case prod _ _ ih₁ ih₂ => exact .prod ih₁ ih₂
  case sum _ _ ih₁ ih₂ => exact .sum ih₁ ih₂
  case fn _ _ hm ih₁ ih₂ => exact .fn ih₁ ih₂ (h.submode hm)
  case joinLeft a b ha => exact .joinLeft (((.join a b : CompareTy).wellShaped_subst_modes_iff ms).mpr ha)
  case joinRight a b ha => exact .joinRight (((.join a b : CompareTy).wellShaped_subst_modes_iff ms).mpr ha)
  case joinLeast _ _ ih₁ ih₂ => exact .joinLeast ih₁ ih₂
  case meetLeft a b ha => exact .meetLeft (((.meet a b : CompareTy).wellShaped_subst_modes_iff ms).mpr ha)
  case meetRight a b ha => exact .meetRight (((.meet a b : CompareTy).wellShaped_subst_modes_iff ms).mpr ha)
  case meetGreatest _ _ ih₁ ih₂ => exact .meetGreatest ih₁ ih₂

theorem subst_typeOp (p : Bool) (a b : CompareTy) (ms : ModVar → ModExpr) :
    (ComparisonAlgebra.typeOp p a b).subst CompareTy.var ms =
      ComparisonAlgebra.typeOp p (a.subst CompareTy.var ms) (b.subst CompareTy.var ms) := by
  cases p <;> rfl

theorem subst_modeOp (p : Bool) (m n : ModExpr) (ms : ModVar → ModExpr) :
    (ComparisonAlgebra.modeOp p m n).subst ms =
      ComparisonAlgebra.modeOp p (m.subst ms) (n.subst ms) := by
  cases p <;> rfl

theorem Fixed.equation {Δ ms a b} (h : Fixed Δ ms) (hab : ComparisonAlgebra.Equation Δ a b) :
    ComparisonAlgebra.Equation Δ (a.subst CompareTy.var ms) (b.subst CompareTy.var ms) := by
  cases hab <;> simp only [CompareTy.subst, subst_typeOp, subst_modeOp]
  case distrib p hab hac => exact .distrib p (h.compatible hab) (h.compatible hac)
  case modal p hab hm => exact .modal p (h.compatible hab) (h.defined hm)
  case scalar a m n p ha hd hm hn =>
    exact .scalar p ((a.wellShaped_subst_modes_iff ms).mpr ha)
      (h.type_defined hd) (h.defined hm) (h.defined hn)
  case prod p hac hbd => exact .prod p (h.compatible hac) (h.compatible hbd)
  case sum p hac hbd => exact .sum p (h.compatible hac) (h.compatible hbd)
  case fn p hac hbd => exact .fn p (h.compatible hac) (h.compatible hbd)

theorem Fixed.algebra {Δ ms a b} (h : Fixed Δ ms) (hab : AlgebraSubtype Δ a b) :
    AlgebraSubtype Δ (a.subst CompareTy.var ms) (b.subst CompareTy.var ms) := by
  induction hab <;> try simp only [CompareTy.subst]
  case shaped hs => exact .shaped (h.shaped hs)
  case trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  case equation he => exact .equation (h.equation he)
  case equationRev he => exact .equationRev (h.equation he)
  case congr _ hm ih => exact .congr ih (h.submode hm)
  case prod _ _ ih₁ ih₂ => exact .prod ih₁ ih₂
  case sum _ _ ih₁ ih₂ => exact .sum ih₁ ih₂
  case fn _ _ hm ih₁ ih₂ => exact .fn ih₁ ih₂ (h.submode hm)
  case joinLeast _ _ ih₁ ih₂ => exact .joinLeast ih₁ ih₂
  case meetGreatest _ _ ih₁ ih₂ => exact .meetGreatest ih₁ ih₂
  case clamp hba hat hm _ _ ih₁ ih₂ =>
    exact .clamp (h.compatible hba) (h.compatible hat) (h.defined hm) ih₁ ih₂
  case clampRev hba hat hm _ _ ih₁ ih₂ =>
    exact .clampRev (h.compatible hba) (h.compatible hat) (h.defined hm) ih₁ ih₂

def restrict (names : Finset ModVar) (v : ModVar) : ModExpr :=
  if v ∈ names then .var v else .epsilon

theorem restrict_fixed (Δ : Bounds) (names : Finset ModVar) (h : Δ.modVars ⊆ names) :
    Fixed Δ (restrict names) := by
  constructor
  · intro η _ v
    by_cases hv : v ∈ names <;> simp [restrict, hv, ModExpr.WellFormed, ModExpr.eval, ModExpr.epsilon]
  · intro v hv
    simp [restrict, h hv]

theorem restrict_support (names : Finset ModVar) (m : ModExpr) :
    ∀ v ∈ (m.subst (restrict names)).vars, v ∈ names := by
  apply ModExpr.support_subst
  intro v _ w hw
  by_cases hv : v ∈ names
  · simp only [restrict, if_pos hv, ModExpr.vars, Finset.mem_singleton] at hw
    subst w
    exact hv
  · simp [restrict, hv, ModExpr.epsilon, ModExpr.vars] at hw

theorem restrict_type_support (names : Finset ModVar) (a : CompareTy) :
    ComparisonInterpolation.Supports (fun _ => True) (fun v => v ∈ names)
      (a.subst CompareTy.var (restrict names)) := by
  induction a <;> simp_all [CompareTy.subst, ComparisonInterpolation.Supports]
  exact restrict_support names _

/-- Modality names absent from the assumptions and public endpoints may be
removed even when the witness and endpoints contain partial annotations. -/
theorem restrict_interval {Δ : Bounds} {a b : Ty} {w : CompareTy}
    (hal : AlgebraSubtype Δ (.ofTy a) w) (hru : AlgebraSubtype Δ w (.ofTy b)) :
    let names := Δ.modVars ∪ a.modVars ∪ b.modVars
    let c := w.subst CompareTy.var (restrict names)
    AlgebraSubtype Δ (.ofTy a) c ∧ AlgebraSubtype Δ c (.ofTy b) ∧
      ComparisonInterpolation.Supports (fun _ => True) (fun v => v ∈ names) c := by
  dsimp only
  let names := Δ.modVars ∪ a.modVars ∪ b.modVars
  have hf := restrict_fixed Δ names (by intro v hv; simp [names, hv])
  have ha : (CompareTy.ofTy a).subst CompareTy.var (restrict names) = .ofTy a :=
    ofTy_fixed a (by intro v hv; simp [restrict, names, hv])
  have hb : (CompareTy.ofTy b).subst CompareTy.var (restrict names) = .ofTy b :=
    ofTy_fixed b (by intro v hv; simp [restrict, names, hv])
  exact ⟨by simpa only [ha] using hf.algebra hal,
    by simpa only [hb] using hf.algebra hru, restrict_type_support names w⟩

end ModalityInference.ComparisonModeRestriction
