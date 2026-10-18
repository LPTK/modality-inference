import ModalityInference.Proofs.ComparisonRootProjection
import ModalityInference.Proofs.SolverLocalSoundness

/-! Ordinary structural inversion under variable-bound assumptions. -/
namespace ModalityInference.SymbolicInversion

open ComparisonStructuralProjection

def tag (a : Ty) : Nat := rootTag (ComparisonShape.ofTy a)

theorem subtype_tag {Δ : Bounds} (hΔ : Residual Δ) {a b : Ty}
    (h : Subtype Δ a b) : tag a = tag b := by
  simpa only [tag, CompareTy.shape_ofTy] using
    rootTag_equivalent hΔ h.to_shaped.shape_equivalent

theorem bound_tag {Δ : Bounds} (hΔ : Residual Δ) {a b : Ty}
    (h : Constraint.sub a b ∈ Δ) : tag a = 0 := by
  obtain ⟨x, y, m, n, hx, _⟩ := List.forall_iff_forall_mem.mp hΔ _ h
  unfold tag
  rw [← TypeExpr.outer_comparisonShape a, hx]
  rfl

def pairChild (right : Bool) : Ty → Ty
  | .prod a b | .sum a b => if right then b else a
  | .modal a m => .modal (pairChild right a) m
  | _ => .unit

theorem subtype_pairChild {Δ : Bounds} (hΔ : Residual Δ) {a b : Ty}
    (h : Subtype Δ a b) (ha : tag a = 3 ∨ tag a = 4) (right : Bool) :
    Subtype Δ (pairChild right a) (pairChild right b) := by
  induction h with
  | refl => exact .refl
  | trans h₁ h₂ ih₁ ih₂ =>
    exact (ih₁ ha).trans (ih₂ (by rwa [← subtype_tag hΔ h₁]))
  | bound h => simp [bound_tag hΔ h] at ha
  | identity => exact .identity
  | identityRev => exact .identityRev
  | compose => exact .compose
  | composeRev => exact .composeRev
  | congr h hm ih => exact .congr (ih ha) hm
  | prod h₁ h₂ ih₁ ih₂ | sum h₁ h₂ ih₁ ih₂ =>
    cases right <;> first | exact h₁ | exact h₂
  | fn h₁ h₂ hm ih₁ ih₂ => simp [tag, ComparisonShape.ofTy, rootTag] at ha

def fnChild (domain : Bool) : Ty → Ty
  | .fn a b => if domain then a else b
  | .modal a _ => fnChild domain a
  | _ => .unit

theorem subtype_fnChild {Δ : Bounds} (hΔ : Residual Δ) {a b : Ty}
    (h : Subtype Δ a b) (ha : tag a = 5) (domain : Bool) :
    if domain then Subtype Δ (fnChild domain b) (fnChild domain a)
    else Subtype Δ (fnChild domain a) (fnChild domain b) := by
  induction h with
  | refl => cases domain <;> exact .refl
  | trans h₁ h₂ ih₁ ih₂ =>
    have hh := ih₂ ((subtype_tag hΔ h₁).symm.trans ha)
    cases domain
    · exact (ih₁ ha).trans hh
    · exact hh.trans (ih₁ ha)
  | bound h => simp [bound_tag hΔ h] at ha
  | identity | identityRev | compose | composeRev => cases domain <;> exact .refl
  | congr h hm ih => exact ih ha
  | prod h₁ h₂ ih₁ ih₂ | sum h₁ h₂ ih₁ ih₂ =>
    simp [tag, ComparisonShape.ofTy, rootTag] at ha
  | fn h₁ h₂ hm ih₁ ih₂ => cases domain <;> first | exact h₁ | exact h₂

theorem rootExpr_ofTy (a : Ty) : rootExpr (CompareTy.ofTy a) = a.outer.2 := by
  induction a <;> simp_all [rootExpr, CompareTy.ofTy, TypeExpr.outer]

theorem subtype_rootMode {Δ : Bounds} (hΔ : Residual Δ) {a b : Ty}
    (h : Subtype Δ a b) (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ)
    (hn : tag a ≠ 0) (hf : tag a ≠ 5) : Submode Δ a.outer.2 b.outer.2 := by
  apply Submode.valid
  intro η hη
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp
    ((TypeExpr.definedUnder_modal.mp ((a.outer_definedUnder Δ).mpr ha)).2 η hη)
  obtain ⟨n, hn'⟩ := Option.isSome_iff_exists.mp
    ((TypeExpr.definedUnder_modal.mp ((b.outer_definedUnder Δ).mpr hb)).2 η hη)
  refine ⟨m, n, hm, hn', ?_⟩
  have hh := shaped_rootValue hΔ h.to_shaped hn (by simp [tag]) hη
  simpa only [rootOrder, hf, if_false, rootValue,
    rootExpr_ofTy, ModExpr.complete_of_eval hm, ModExpr.complete_of_eval hn'] using hh

theorem subtype_fnMode {Δ : Bounds} (hΔ : Residual Δ) {a b : Ty}
    (h : Subtype Δ a b) (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ)
    (hf : tag a = 5) : Submode Δ a.outer.2 (.compose b.outer.2 .top) := by
  apply Submode.valid
  intro η hη
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp
    ((TypeExpr.definedUnder_modal.mp ((a.outer_definedUnder Δ).mpr ha)).2 η hη)
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp
    ((TypeExpr.definedUnder_modal.mp ((b.outer_definedUnder Δ).mpr hb)).2 η hη)
  refine ⟨m, n.compose Mode.top, hm, ?_, ?_⟩
  · simp only [ModExpr.eval, hn, ModExpr.top, bind, pure, Option.bind_some]
  have hh := shaped_rootValue hΔ h.to_shaped (by decide : 5 ≠ 0)
    (by simpa [tag] using hf) hη
  simp only [rootOrder, if_true, rootValue, rootExpr_ofTy,
    ModExpr.complete_of_eval hm, ModExpr.complete_of_eval hn] at hh
  simpa only [Mode.le_iff, Mode.compose, Mode.top, Bool.and_false, Bool.and_true,
    Bool.false_eq_true, IsEmpty.forall_iff, and_true] using hh

theorem rootMode_modal {a : Ty} {m : ModExpr}
    (ha : ∀ t n, a ≠ .modal t n) (η : ModVar → Option Mode) :
    (.modal a m : Ty).outer.2.eval η = m.eval η := by
  cases a <;> simp_all [TypeExpr.outer, ModExpr.eval, ModExpr.epsilon]

theorem subtype_structural_mode {Δ : Bounds} (hΔ : Residual Δ) {a b : Ty} {m n : ModExpr}
    (h : Subtype Δ (.modal a m) (.modal b n))
    (ha : (.modal a m : Ty).DefinedUnder Δ) (hb : (.modal b n : Ty).DefinedUnder Δ)
    (hn : tag a ≠ 0) (hf : tag a ≠ 5)
    (ham : ∀ t k, a ≠ .modal t k) (hbm : ∀ t k, b ≠ .modal t k) : Submode Δ m n := by
  have hh := subtype_rootMode hΔ h ha hb hn hf
  exact .valid fun η hη => by
    simpa only [ModExpr.Below, rootMode_modal ham, rootMode_modal hbm] using hh.denote hη

theorem subtype_function_mode {Δ : Bounds} (hΔ : Residual Δ) {a b c d : Ty} {m n : ModExpr}
    (h : Subtype Δ (.modal (.fn a b) m) (.modal (.fn c d) n))
    (ha : (.modal (.fn a b) m : Ty).DefinedUnder Δ)
    (hb : (.modal (.fn c d) n : Ty).DefinedUnder Δ) : Submode Δ m (.compose n .top) := by
  have hh := subtype_fnMode hΔ h ha hb rfl
  exact .valid fun η hη => by
    simpa [ModExpr.Below, TypeExpr.outer, ModExpr.eval, ModExpr.epsilon] using hh.denote hη

end ModalityInference.SymbolicInversion
