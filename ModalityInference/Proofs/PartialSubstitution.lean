import ModalityInference.Proofs.Subtyping

/-! Substitution must preserve the definedness obligations of partial modalities. -/
namespace ModalityInference

theorem ModExpr.eval_subst (m : ModExpr) (σ : ModVar → ModExpr) (ρ : ModVar → Option Mode) :
    (m.subst σ).eval ρ = m.eval (fun v => (σ v).eval ρ) := by
  induction m <;> simp_all [ModExpr.subst, ModExpr.eval]

theorem Modality.eval_total (m : Modality) (ρ : ModVar → Mode) :
    ∃ n, m.toExpr.eval (some ∘ ρ) = some n := by
  induction m with
  | const m => exact ⟨m, rfl⟩
  | var v => exact ⟨ρ v, rfl⟩
  | compose a b iha ihb =>
    obtain ⟨m, hm⟩ := iha
    obtain ⟨n, hn⟩ := ihb
    exact ⟨m.compose n, by simp [Modality.toExpr, ModExpr.eval, hm, hn]⟩

theorem Modality.wellFormed (m : Modality) (ρ : ModVar → Mode) : m.toExpr.WellFormed ρ := by
  obtain ⟨n, hn⟩ := m.eval_total ρ
  simp [ModExpr.WellFormed, hn]

private theorem Substitution.modeSatisfies {σ : Substitution} {η θ : ModVar → Mode}
    (h : ∀ v, (σ.mode v).eval (some ∘ η) = some (θ v)) (c : Constraint) :
    ModeSatisfies η (σ.constraint c) ↔ ModeSatisfies θ c := by
  have hf : (fun v => (σ.mode v).eval (some ∘ η)) = some ∘ θ := funext h
  cases c <;>
    simp [Substitution.constraint, Constraint.subst, ModeSatisfies, ModExpr.Below,
      ModExpr.WellFormed, ModExpr.eval_subst, hf]
  rename_i v t
  cases v with
  | flex n => cases he : σ.types.lookup n <;> simp [he]
  | rigid n => trivial

private theorem Substitution.modeModels_pullback {σ : Substitution} {Δ : Bounds}
    {η : ModVar → Mode} (hη : ModeModels (σ.bounds Δ) η)
    (hσ : ∀ v, (σ.mode v).WellFormed η) :
    ∃ θ, (∀ v, (σ.mode v).eval (some ∘ η) = some (θ v)) ∧ ModeModels Δ θ := by
  let θ : ModVar → Mode := fun v => ((σ.mode v).eval (some ∘ η)).getD Mode.identity
  have hvars : ∀ v, (σ.mode v).eval (some ∘ η) = some (θ v) := by
    intro v
    have hv := hσ v
    cases he : (σ.mode v).eval (some ∘ η) <;> simp_all [ModExpr.WellFormed, θ]
  refine ⟨θ, hvars, ?_⟩
  intro c hc
  apply (σ.modeSatisfies hvars c).mp
  exact hη (σ.constraint c) (List.mem_map.mpr ⟨c, hc, rfl⟩)

theorem Submode.substitute {Δ m n} (h : Submode Δ m n) (σ : Substitution)
    (hσ : ∀ η, ModeModels (σ.bounds Δ) η → ∀ v, (σ.mode v).WellFormed η) :
    Submode (σ.bounds Δ) (m.subst σ.mode) (n.subst σ.mode) := by
  apply Submode.valid
  intro η hη
  obtain ⟨θ, hvars, hθ⟩ := Substitution.modeModels_pullback hη (hσ η hη)
  obtain ⟨x, y, hx, hy, hxy⟩ := h.denote hθ
  have hf : (fun v => (σ.mode v).eval (some ∘ η)) = some ∘ θ := funext hvars
  exact ⟨x, y, by simpa only [ModExpr.eval_subst, hf] using hx,
    by simpa only [ModExpr.eval_subst, hf] using hy, hxy⟩

/-- Partial substitution images must be defined in every target model. Ordinary
modality substitutions satisfy this automatically; residuals retain obligations. -/
theorem Subtype.substitute {Δ a b} (h : Subtype Δ a b) (σ : Substitution)
    (hσ : ∀ η, ModeModels (σ.bounds Δ) η → ∀ v, (σ.mode v).WellFormed η) :
    Subtype (σ.bounds Δ) (σ.ty a) (σ.ty b) := by
  induction h <;> simp only [Substitution.ty, TypeExpr.subst]
  case refl => exact .refl
  case trans _ _ iha ihb => exact .trans iha ihb
  case bound a b hc => exact .bound (List.mem_map.mpr ⟨.sub a b, hc, rfl⟩)
  case identity => exact .identity
  case identityRev => exact .identityRev
  case compose => exact .compose
  case composeRev => exact .composeRev
  case congr _ hm ih => exact .congr ih (hm.substitute σ hσ)
  case prod _ _ iha ihb => exact .prod iha ihb
  case sum _ _ iha ihb => exact .sum iha ihb
  case fn _ _ hm iha ihb => exact .fn iha ihb (hm.substitute σ hσ)

theorem Subtype.substitute_ordinary {Δ a b} (h : Subtype Δ a b) (σ : Substitution)
    (hσ : ∀ v, ∃ m : Modality, σ.mode v = m.toExpr) :
    Subtype (σ.bounds Δ) (σ.ty a) (σ.ty b) := by
  apply h.substitute σ
  intro η _ v
  obtain ⟨m, hm⟩ := hσ v
  exact hm ▸ m.wellFormed η

namespace PartialSubstitution

def source : Ty := .modal .unit (.var (.flex 0))
def target : Ty := .modal .unit .top
def invalid : Substitution :=
  {modes := [(0, .leftResidual (.const Mode.top) (.const Mode.bottom))]}
def assignment : GroundAssignment :=
  ⟨fun _ => .unit Mode.identity, fun _ => Mode.identity⟩

theorem original_subtype : Subtype [] source target := by
  apply Subtype.congr .refl
  apply Submode.valid
  intro ρ _
  exact ⟨ρ (.flex 0), Mode.top, rfl, rfl, by simp [Mode.le, Mode.top]⟩

theorem invalid_substitution : ¬ Subtype [] (invalid.ty source) (invalid.ty target) := by
  intro h
  have hd := h.realize_defined (ρ := assignment) (by simp [GroundModels])
  simp [invalid, source, target, Substitution.ty, Substitution.mode,
    TypeExpr.subst, TypeExpr.realize, ModExpr.subst, ModExpr.eval, ModExpr.top,
    Mode.leftResidual, Mode.top, Mode.bottom] at hd

theorem no_unrestricted_subtyping_substitution : ¬ (∀ {Δ a b} (σ : Substitution),
    Subtype Δ a b → Subtype (σ.bounds Δ) (σ.ty a) (σ.ty b)) := by
  intro h
  exact invalid_substitution (h invalid original_subtype)

end PartialSubstitution
end ModalityInference
