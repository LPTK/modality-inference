import ModalityInference.Proofs.TypingDefinedness
import ModalityInference.Generation
import ModalityInference.Constraints

/-! Generated type guards remain meaningful under arbitrary solution
substitutions, including images containing partial internal modalities. -/
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

@[simp] theorem TypeExpr.definedUnder_fn {Δ} {a b : Ty} :
    (TypeExpr.fn a b).DefinedUnder Δ ↔ a.DefinedUnder Δ ∧ b.DefinedUnder Δ := by
  simp [DefinedUnder, wellFormedBounds, ModeModels, or_imp, forall_and]

@[simp] theorem TypeExpr.definedUnder_prod {Δ} {a b : Ty} :
    (TypeExpr.prod a b).DefinedUnder Δ ↔ a.DefinedUnder Δ ∧ b.DefinedUnder Δ := by
  simp [DefinedUnder, wellFormedBounds, ModeModels, or_imp, forall_and]

@[simp] theorem TypeExpr.definedUnder_sum {Δ} {a b : Ty} :
    (TypeExpr.sum a b).DefinedUnder Δ ↔ a.DefinedUnder Δ ∧ b.DefinedUnder Δ := by
  simp [DefinedUnder, wellFormedBounds, ModeModels, or_imp, forall_and]

@[simp] theorem TypeExpr.definedUnder_modal {Δ} {a : Ty} {m : ModExpr} :
    (TypeExpr.modal a m).DefinedUnder Δ ↔
      a.DefinedUnder Δ ∧ ∀ η, ModeModels Δ η → m.WellFormed η := by
  simp [DefinedUnder, wellFormedBounds, ModeModels, or_imp, forall_and, ModeSatisfies]

/-- Every generated result type is defined under any declarative solution,
including solutions with partial internal substitution images. -/
theorem Generates.definedUnder {Γ t a cs} (h : Generates Γ t a cs)
    {Δ σ} (hs : Solution cs Δ σ) : (σ.ty a).DefinedUnder Δ := by
  induction h generalizing Δ σ
  case lam Γ t a b m cs ht ih =>
    obtain ⟨hbody, hguard⟩ := Solution.append.mp hs
    exact TypeExpr.definedUnder_modal.mpr
      ⟨TypeExpr.definedUnder_fn.mpr ⟨hguard.sub_left (a := a) (b := a) (by simp), ih hbody⟩,
        hguard.mode_defined (by simp)⟩
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
    exact (Solution.append.mp hs).2.sub_left (a := θ.ty s.body) (b := θ.ty s.body) (by simp)
  case unit Γ =>
    intro η hη
    simp [Substitution.ty, TypeExpr.subst, ModExpr.subst, TypeExpr.wellFormedBounds,
      ModeModels, ModeSatisfies, ModExpr.WellFormed, ModExpr.eval, ModExpr.bottom]
  case inl Γ x a b c m cs hx ih =>
    have hg := (Solution.append.mp hs).2
    have hb := TypeExpr.definedUnder_modal.mp (hg.sub_right (a := a) (b := .modal b m) (by simp))
    exact TypeExpr.definedUnder_modal.mpr ⟨TypeExpr.definedUnder_sum.mpr
      ⟨hb.1, hg.sub_left (a := c) (b := c) (by simp)⟩, hb.2⟩
  case inr Γ x a b c m cs hx ih =>
    have hg := (Solution.append.mp hs).2
    have hc := TypeExpr.definedUnder_modal.mp (hg.sub_right (a := a) (b := .modal c m) (by simp))
    exact TypeExpr.definedUnder_modal.mpr ⟨TypeExpr.definedUnder_sum.mpr
      ⟨hg.sub_left (a := b) (b := b) (by simp), hc.1⟩, hc.2⟩
  case app Γ Γ₁ Γ₂ f x a b c m cs ds hj hf hx ihf ihx =>
    have hh := (Solution.append.mp hs).2.sub_right (a := a) (b := .modal (.fn b c) m) (by simp)
    exact (TypeExpr.definedUnder_fn.mp (TypeExpr.definedUnder_modal.mp hh).1).2
  case split Γ Γ₁ Γ₂ x body a b c d m cs ds hj hx hb ihx ihb =>
    exact ihb (Solution.append.mp (Solution.append.mp hs).1).2
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
    exact ihb hs


end ModalityInference
