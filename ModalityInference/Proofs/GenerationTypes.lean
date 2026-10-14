import ModalityInference.Proofs.SubstitutionWellFormed
import ModalityInference.Generation
import ModalityInference.Constraints

/-! Generated result types are defined under well-formed solution substitutions.
Fresh inference variables need no emitted reflexive or definedness constraints. -/
namespace ModalityInference

@[simp] theorem Solution.append {xs ys Δ σ} :
    Solution (xs ++ ys) Δ σ ↔ Solution xs Δ σ ∧ Solution ys Δ σ := by
  simp [Solution, EntailsAll, Substitution.bounds, or_imp, forall_and]

theorem Solution.sub_left {cs Δ σ a b} (h : Solution cs Δ σ)
    (hc : Constraint.sub a b ∈ cs) : (σ.ty a).DefinedUnder Δ :=
  (h _ (List.mem_map_of_mem hc)).2.1

theorem Solution.sub_right {cs Δ σ a b} (h : Solution cs Δ σ)
    (hc : Constraint.sub a b ∈ cs) : (σ.ty b).DefinedUnder Δ :=
  (h _ (List.mem_map_of_mem hc)).2.2

theorem Solution.mode_defined {cs Δ σ m} (h : Solution cs Δ σ)
    (hc : Constraint.defined m ∈ cs) :
    ∀ η, ModeModels Δ η → (m.subst σ.mode).WellFormed η :=
  h _ (List.mem_map_of_mem hc)

/-- Every generated result is defined when the solution's type and modality
images are well formed under the resulting bounds. -/
theorem Generates.definedUnder {Γ t a cs} (h : Generates Γ t a cs)
    {Δ σ} (hs : Solution cs Δ σ) (hσ : σ.WellFormedUnder Δ) : (σ.ty a).DefinedUnder Δ := by
  induction h generalizing Δ σ
  case lam Γ t a b m cs ht ih =>
    exact TypeExpr.definedUnder_modal.mpr
      ⟨TypeExpr.definedUnder_fn.mpr ⟨hσ.types (.flex a), ih hs hσ⟩,
        hσ.modes (.flex m)⟩
  case pair Γ Γ₁ Γ₂ x y a b c d m cs ds hj hx hy ihx ihy =>
    have hg := (Solution.append.mp hs).2
    have hc := TypeExpr.definedUnder_modal.mp (hg.sub_right (a := a) (b := .modal c m) (by simp))
    have hd := TypeExpr.definedUnder_modal.mp (hg.sub_right (a := b) (b := .modal d m) (by simp))
    exact TypeExpr.definedUnder_modal.mpr ⟨TypeExpr.definedUnder_prod.mpr ⟨hc.1, hd.1⟩, hc.2⟩
  case stackPair Γ Γ₁ Γ₂ x y a b c d m cs ds hj hx hy ihx ihy =>
    have hg := (Solution.append.mp hs).2
    have hc := TypeExpr.definedUnder_modal.mp (hg.sub_right (a := a) (b := .modal c m) (by simp))
    have hd := TypeExpr.definedUnder_modal.mp (hg.sub_right (a := b) (b := .modal d m) (by simp))
    exact TypeExpr.definedUnder_modal.mpr ⟨TypeExpr.definedUnder_prod.mpr ⟨hc.1, hd.1⟩, hc.2⟩
  case var Γ i s θ hl hθ =>
    exact hσ.type_of_guards (θ.ty s.body) (Solution.append.mp hs).2
  case unit Γ =>
    intro η hη
    simp [Substitution.ty, TypeExpr.subst, ModExpr.subst, TypeExpr.wellFormedBounds,
      ModeModels, ModeSatisfies, ModExpr.WellFormed, ModExpr.eval, ModExpr.bottom]
  case inl Γ x a b c m cs hx ih =>
    have hg := (Solution.append.mp hs).2
    have hb := TypeExpr.definedUnder_modal.mp (hg.sub_right (a := a) (b := .modal b m) (by simp))
    exact TypeExpr.definedUnder_modal.mpr ⟨TypeExpr.definedUnder_sum.mpr
      ⟨hb.1, hσ.types (.flex c)⟩, hb.2⟩
  case inr Γ x a b c m cs hx ih =>
    have hg := (Solution.append.mp hs).2
    have hc := TypeExpr.definedUnder_modal.mp (hg.sub_right (a := a) (b := .modal c m) (by simp))
    exact TypeExpr.definedUnder_modal.mpr ⟨TypeExpr.definedUnder_sum.mpr
      ⟨hσ.types (.flex b), hc.1⟩, hc.2⟩
  case app Γ Γ₁ Γ₂ f x a b c m cs ds hj hf hx ihf ihx =>
    have hh := (Solution.append.mp hs).2.sub_right (a := a) (b := .modal (.fn b c) m) (by simp)
    exact (TypeExpr.definedUnder_fn.mp (TypeExpr.definedUnder_modal.mp hh).1).2
  case split Γ Γ₁ Γ₂ x body a b c d m cs ds hj hx hb ihx ihb =>
    exact ihb (Solution.append.mp (Solution.append.mp hs).1).2 hσ
  case case Γ Γ₁ Γ₂ x l r a b c d e f m cs ds es hj hx hl hr ihx ihl ihr =>
    exact (Solution.append.mp hs).2.sub_right (a := d) (b := f) (by simp)
  case reuse Γ Γ₁ Γ₂ Γ₃ Γ₂₃ k x y a b c d e m n cs ds es hj hk₁ hk hx hy ihk ihx ihy =>
    have hg := (Solution.append.mp hs).2
    have hd := TypeExpr.definedUnder_modal.mp (hg.sub_right (a := b) (b := .modal d m) (by simp))
    have he := TypeExpr.definedUnder_modal.mp (hg.sub_right (a := c) (b := .modal e m) (by simp))
    exact TypeExpr.definedUnder_modal.mpr ⟨TypeExpr.definedUnder_prod.mpr ⟨hd.1, he.1⟩, hd.2⟩
  case region Γ t a b cs ht ih =>
    have hh := (Solution.append.mp hs).2.sub_right (a := a) (b := .modal b (.const Mode.global)) (by simp)
    exact (TypeExpr.definedUnder_modal.mp hh).1
  case defn Γ rhs body a b cs ds residual σ' hclosed hrhs hsolve hbody ihr ihb =>
    exact ihb hs hσ


end ModalityInference
