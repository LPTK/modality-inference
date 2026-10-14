import ModalityInference.Proofs.RewriteModels
import ModalityInference.Proofs.FlexibleSupport
import ModalityInference.Proofs.BoundedSupport
import ModalityInference.Proofs.GroundReification

/-! Ground factorization observes original identifiers and hides fresh auxiliaries. -/
namespace ModalityInference

/-- A residual solution recovers the original ground images after applying the
accumulated substitution, up to mutual ground subtyping. -/
def GroundFactorization (scope : Scope) (bounds : Bounds) (σ : Substitution)
    (ρ : GroundAssignment) : Prop :=
  ∃ η : GroundAssignment, GroundModels η bounds ∧
    (∀ v ∈ scope.types, ∃ t, (σ.type v).realize η = some t ∧
      Subtype [] t.reify (ρ.types v).reify ∧ Subtype [] (ρ.types v).reify t.reify) ∧
    (∀ v ∈ scope.modes, (σ.mode v).eval (some ∘ η.modes) = some (ρ.modes v))

theorem Deferred.ConfigModels.initial {scope cs ρ} (h : GroundModels ρ cs) :
    ConfigModels scope ⟨cs, [], {}⟩ ρ := by
  refine ⟨ρ, by simpa [RewriteConfig.constraints] using h, ?_, ?_⟩
  · intro v _
    exact ⟨ρ.types v, by cases v <;> rfl, .refl, .refl⟩
  · intro v _
    cases v <;> rfl

theorem Deferred.ConfigModels.factorization {scope s ρ} (h : ConfigModels scope s ρ)
    (hp : s.pending = []) : GroundFactorization scope s.bounds s.substitution ρ := by
  simpa only [ConfigModels, GroundFactorization, RewriteConfig.constraints, hp,
    List.nil_append] using h

theorem GroundAssignment.finiteSubstitution_realize (ρ : GroundAssignment)
    {nt nm a} (ha : a.Bounded nt nm) (hf : a.Flexible) :
    ((ρ.finiteSubstitution nt nm).ty a).realize ρ = a.realize ρ := by
  apply TypeExpr.realize_subst_congr
  · intro v hv
    obtain ⟨n, rfl⟩ := ((a.flexible_iff).mp hf).1 v hv
    rw [ρ.finiteSubstitution_type (nt := nt) (nm := nm) (n := n)
      (((a.bounded_iff nt nm).mp ha).1 _ hv)]
    exact GroundTy.realize_reify _ _
  · intro v hv
    obtain ⟨n, rfl⟩ := ((a.flexible_iff).mp hf).2 v hv
    rw [ρ.finiteSubstitution_mode (nt := nt) (nm := nm) (n := n)
      (((a.bounded_iff nt nm).mp ha).2 _ hv)]
    rfl

theorem GroundAssignment.finiteSubstitution_closed (ρ : GroundAssignment)
    {nt nm a} (ha : a.Bounded nt nm) (hf : a.Flexible) :
    ((ρ.finiteSubstitution nt nm).ty a).typeVars = ∅ ∧
      ((ρ.finiteSubstitution nt nm).ty a).modVars = ∅ := by
  apply TypeExpr.subst_closed
  · intro v hv
    obtain ⟨n, rfl⟩ := ((a.flexible_iff).mp hf).1 v hv
    rw [ρ.finiteSubstitution_type (nt := nt) (nm := nm) (n := n)
      (((a.bounded_iff nt nm).mp ha).1 _ hv)]
    simp
  · intro v hv
    obtain ⟨n, rfl⟩ := ((a.flexible_iff).mp hf).2 v hv
    rw [ρ.finiteSubstitution_mode (nt := nt) (nm := nm) (n := n)
      (((a.bounded_iff nt nm).mp ha).2 _ hv)]
    rfl

theorem GroundAssignment.finiteSubstitution_subtype (ρ : GroundAssignment)
    {nt nm a t} (ha : a.Bounded nt nm) (hf : a.Flexible) (ht : a.realize ρ = some t) :
    Subtype [] ((ρ.finiteSubstitution nt nm).ty a) t.reify ∧
      Subtype [] t.reify ((ρ.finiteSubstitution nt nm).ty a) :=
  TypeExpr.realize_closed_subtype (ρ.finiteSubstitution_closed ha hf).1
    (ρ.finiteSubstitution_closed ha hf).2 ((ρ.finiteSubstitution_realize ha hf).trans ht)

theorem GroundAssignment.finiteSubstitution_eval (ρ : GroundAssignment)
    {nt nm : Nat} {a : ModExpr} (ha : a.Bounded nm) (hf : a.Flexible)
    (η : ModVar → Option Mode) :
    (a.subst (ρ.finiteSubstitution nt nm).mode).eval η = a.eval (some ∘ ρ.modes) := by
  rw [ModExpr.eval_subst]
  apply ModExpr.eval_congr
  intro v hv
  obtain ⟨n, rfl⟩ := (a.flexible_iff.mp hf) v hv
  rw [ρ.finiteSubstitution_mode (nt := nt) (nm := nm) (n := n)
    (a.bounded_iff nm |>.mp ha _ hv)]
  rfl

theorem GroundAssignment.finiteSubstitution_wellFormed (ρ : GroundAssignment) (nt nm : Nat) :
    (ρ.finiteSubstitution nt nm).WellFormedUnder [] := by
  constructor
  · intro v
    cases v
    case rigid n => simp [Substitution.type, TypeExpr.DefinedUnder,
      TypeExpr.wellFormedBounds, ModeModels]
    case flex n =>
      cases he : (ρ.finiteSubstitution nt nm).types.lookup n
      case none => simp [Substitution.type, he, TypeExpr.DefinedUnder,
        TypeExpr.wellFormedBounds, ModeModels]
      case some a =>
        obtain ⟨before, after, hh, _⟩ := List.lookup_eq_some_iff.mp he
        have hm : (n, a) ∈ (ρ.finiteSubstitution nt nm).types := by simp [hh]
        simp only [finiteSubstitution, List.mem_map, Prod.mk.injEq] at hm
        obtain ⟨i, _, rfl, rfl⟩ := hm
        simp only [Substitution.type, he, Option.getD_some]
        exact TypeExpr.definedUnder_of_closed_realize (by simp)
          (GroundTy.realize_reify ρ _)
  · intro v
    cases v
    case rigid n => simp [Substitution.mode, Entails, ModExpr.WellFormed, ModExpr.eval]
    case flex n =>
      cases he : (ρ.finiteSubstitution nt nm).modes.lookup n
      case none => simp [Substitution.mode, he, Entails, ModExpr.WellFormed, ModExpr.eval]
      case some m =>
        obtain ⟨before, after, hh, _⟩ := List.lookup_eq_some_iff.mp he
        have hm : (n, m) ∈ (ρ.finiteSubstitution nt nm).modes := by simp [hh]
        simp only [finiteSubstitution, List.mem_map, Prod.mk.injEq] at hm
        obtain ⟨i, _, rfl, rfl⟩ := hm
        simp [Substitution.mode, he, Entails, ModExpr.WellFormed, ModExpr.eval]

theorem GroundAssignment.finiteSubstitution_solution (ρ : GroundAssignment)
    {nt nm cs} (hb : cs.Bounded nt nm) (hf : cs.Flexible) (hg : GroundModels ρ cs) :
    Solution cs [] (ρ.finiteSubstitution nt nm) := by
  let τ := ρ.finiteSubstitution nt nm
  have ht : ∀ v ∈ cs.typeVars, τ.type v = (ρ.types v).reify := by
    intro v hv
    obtain ⟨n, rfl⟩ := (cs.flexible_iff.mp hf).1 v hv
    exact ρ.finiteSubstitution_type (n := n) ((cs.bounded_iff nt nm).mp hb |>.1 _ hv)
  have hm : ∀ v ∈ cs.modVars, τ.mode v = .const (ρ.modes v) := by
    intro v hv
    obtain ⟨n, rfl⟩ := (cs.flexible_iff.mp hf).2 v hv
    exact ρ.finiteSubstitution_mode (n := n) ((cs.bounded_iff nt nm).mp hb |>.2 _ hv)
  have hmodel : GroundModels ρ (τ.bounds cs) := (GroundModels.subst_congr cs
    (fun v hv => by rw [ht v hv]; exact GroundTy.realize_reify _ _)
    (fun v hv => by rw [hm v hv]; rfl)).mpr hg
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  have hclosed := Substitution.constraint_closed (σ := τ) (c := d)
    (fun v hv => by rw [ht v ((cs.mem_typeVars_iff v).mpr ⟨d, hd, hv⟩)]; simp)
    (fun v hv => by rw [hm v ((cs.mem_modVars_iff v).mpr ⟨d, hd, hv⟩)]; rfl)
  exact (hmodel _ (List.mem_map.mpr ⟨d, hd, rfl⟩)).entails_closed hclosed.1 hclosed.2

/-- Flexible finite residuals and substitution images admit an actual finite
closed instance realizing the factorization. -/
theorem GroundFactorization.finite {scope cs σ ρ nt nm}
    (h : GroundFactorization scope cs σ ρ) (hb : cs.Bounded nt nm) (hf : cs.Flexible)
    (ht : ∀ v ∈ scope.types, (σ.type v).Bounded nt nm ∧ (σ.type v).Flexible)
    (hm : ∀ v ∈ scope.modes, (σ.mode v).Bounded nm ∧ (σ.mode v).Flexible) :
    ∃ τ : Substitution, τ.WellFormedUnder [] ∧ Solution cs [] τ ∧
      (∀ v ∈ scope.types, Subtype [] (τ.ty (σ.type v)) (ρ.types v).reify ∧
        Subtype [] (ρ.types v).reify (τ.ty (σ.type v))) ∧
      (∀ v ∈ scope.modes,
        Submode [] ((σ.mode v).subst τ.mode) (.const (ρ.modes v)) ∧
        Submode [] (.const (ρ.modes v)) ((σ.mode v).subst τ.mode)) := by
  obtain ⟨η, hη, htypes, hmodes⟩ := h
  refine ⟨η.finiteSubstitution nt nm, η.finiteSubstitution_wellFormed nt nm,
    η.finiteSubstitution_solution hb hf hη, ?_, ?_⟩
  · intro v hv
    obtain ⟨t, ht', hl, hr⟩ := htypes v hv
    have he := η.finiteSubstitution_subtype (ht v hv).1 (ht v hv).2 ht'
    exact ⟨he.1.trans hl, hr.trans he.2⟩
  · intro v hv
    have he : ∀ ξ, ((σ.mode v).subst (η.finiteSubstitution nt nm).mode).eval ξ =
        some (ρ.modes v) := fun ξ =>
      (η.finiteSubstitution_eval (hm v hv).1 (hm v hv).2 ξ).trans (hmodes v hv)
    refine ⟨.valid ?_, .valid ?_⟩
    · intro ξ _
      exact ⟨ρ.modes v, ρ.modes v, he _, rfl, Mode.le_refl _⟩
    · intro ξ _
      exact ⟨ρ.modes v, ρ.modes v, rfl, he _, Mode.le_refl _⟩

end ModalityInference
