import ModalityInference.Proofs.Instantiation
import ModalityInference.Proofs.Subtyping
import ModalityInference.Proofs.PartialSubstitution

/-! Every type occurring in a typing derivation has a ground realization.
The introduction rules guard internal partial modalities; source modalities
are total and satisfy these guards without additional restrictions.
-/
namespace ModalityInference

theorem EntailsAll.modeModels {Δ cs ρ} (h : EntailsAll Δ cs) (hΔ : ModeModels Δ ρ) :
    ModeModels cs ρ := by
  intro c hc
  cases c <;> first | exact (h _ hc).denote hΔ | exact h _ hc ρ hΔ | trivial

theorem TypeExpr.DefinedUnder.realize_defined {Δ ρ} {a : Ty}
    (h : a.DefinedUnder Δ) (hΔ : GroundModels ρ Δ) : (a.realize ρ).isSome = true :=
  (a.wellFormedBounds_spec ρ).mp (h ρ.modes hΔ.modeModels)

theorem EntailsAll.realize_defined {Δ ρ} {a : Ty} (h : EntailsAll Δ a.wellFormedBounds)
    (hΔ : GroundModels ρ Δ) : (a.realize ρ).isSome = true :=
  (a.wellFormedBounds_spec ρ).mp (h.modeModels hΔ.modeModels)

theorem Typing.realize_defined {Δ Γ t a} (h : Typing Δ Γ t a)
    {ρ} (hΔ : GroundModels ρ Δ) : (a.realize ρ).isSome = true := by
  induction h
  case subs _ _ hab ih => exact (hab.realize_defined hΔ) ▸ ih hΔ
  all_goals simp only [← TypeExpr.wellFormedBounds_spec, TypeExpr.wellFormedBounds,
    ModeModels, List.mem_append, List.mem_singleton, List.not_mem_nil, or_imp, forall_and,
    forall_eq, ModeSatisfies] at *
  case stackPair _ _ _ hmn _ iha ihb =>
    refine ⟨⟨iha.1 hΔ, ihb.1 hΔ⟩, ?_⟩
    obtain ⟨x, y, hx, hy, _⟩ := hmn.denote hΔ.modeModels
    simp [ModExpr.WellFormed, hy]
  case var _ _ _ hw => exact hw.modeModels hΔ.modeModels
  case lam ha hm _ _ ih => exact ⟨⟨ha.modeModels hΔ.modeModels, ih hΔ⟩, hm _ hΔ.modeModels⟩
  case inl hb _ ih => exact ⟨⟨ih.1 hΔ, hb.modeModels hΔ.modeModels⟩, ih.2 hΔ⟩
  case inr ha _ ih => exact ⟨⟨ha.modeModels hΔ.modeModels, ih.1 hΔ⟩, ih.2 hΔ⟩
  all_goals aesop (add safe forward GroundModels.modeModels) (add norm unfold Entails)

theorem TypeExpr.source_wellFormedBounds (a : SourceTy) (Δ : Bounds) :
    EntailsAll Δ (a.map Modality.toExpr).wellFormedBounds := by
  induction a <;> simp_all [TypeExpr.map, TypeExpr.wellFormedBounds,
    EntailsAll, List.mem_append, or_imp, Entails]
  exact fun σ _ => Modality.wellFormed _ σ

theorem TypeExpr.source_definedUnder (a : SourceTy) (Δ : Bounds) :
    (a.map Modality.toExpr).DefinedUnder Δ :=
  fun _ hΔ => (a.source_wellFormedBounds Δ).modeModels hΔ

theorem Entails.source_sub_iff (a b : SourceTy) (Δ : Bounds) :
    Entails Δ (.sub (a.map Modality.toExpr) (b.map Modality.toExpr)) ↔
      Subtype Δ (a.map Modality.toExpr) (b.map Modality.toExpr) :=
  ⟨And.left, fun h => ⟨h, a.source_definedUnder Δ, b.source_definedUnder Δ⟩⟩

theorem Entails.source_equal_iff (v : TypeVar) (a : SourceTy) (Δ : Bounds) :
    Entails Δ (.equal v (a.map Modality.toExpr)) ↔
      Subtype Δ (.var v) (a.map Modality.toExpr) ∧
      Subtype Δ (a.map Modality.toExpr) (.var v) :=
  ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, a.source_definedUnder Δ⟩⟩

theorem Entails.source_equiv_iff (a b : SourceTy) (Δ : Bounds) :
    Entails Δ (.equiv (a.map Modality.toExpr) (b.map Modality.toExpr)) ↔
      Subtype Δ (a.map Modality.toExpr) (b.map Modality.toExpr) ∧
      Subtype Δ (b.map Modality.toExpr) (a.map Modality.toExpr) :=
  ⟨fun h => ⟨h.1, h.2.1⟩,
    fun h => ⟨h.1, h.2, a.source_definedUnder Δ, b.source_definedUnder Δ⟩⟩

end ModalityInference
