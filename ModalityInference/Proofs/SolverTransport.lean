import ModalityInference.Proofs.TypeSeen
import ModalityInference.Proofs.EntailmentTransport

/-! Cached consequences under later type substitutions. Definedness of inserted
images is a premise here; full solver input entailment still needs to establish it. -/
namespace ModalityInference

theorem SolverState.TypeReady.duplicate_substitute_entails {s : SolverState}
    (hs : s.TypeReady) (hm : s.ModeInvariant) {c rest Δ} {σ : Substitution}
    (hp : s.pending = c :: rest) (hfix : s.substitution.constraint c = c)
    (hv : (s.substitution.constraint c).normalize ∈ s.seen) (hσ : σ.modes = [])
    (hΔ : EntailsAll Δ (σ.bounds (rest ++ s.bounds)))
    (ht : ∀ v ∈ c.typeVars, (σ.type v).DefinedUnder Δ) : Entails Δ (σ.constraint c) :=
  Entails.consequence_substitute_types (fun _ hΓ => hs.duplicate_entails hm hp hfix hv hΓ)
    hσ hΔ ht

theorem Constraint.normalize_substitute_entails (c : Constraint) (Δ : Bounds)
    {σ : Substitution} (hm : σ.modes = []) :
    Entails Δ (σ.constraint c.normalize) ↔ Entails Δ (σ.constraint c) :=
  Entails.equivalent_substitute_types (fun Γ => c.normalize_entails Γ) c.normalize_typeVars hm

theorem stepType_substitute_entails {s a b t Δ} {σ : Substitution}
    (h : stepType s a b = .success t) (hm : σ.modes = [])
    (hΔ : EntailsAll Δ (σ.bounds (t.pending ++ t.bounds)))
    (ht : ∀ v ∈ (Constraint.sub a b).typeVars, (σ.type v).DefinedUnder Δ) :
    Entails Δ (σ.constraint (.sub a b)) :=
  Entails.consequence_substitute_types (fun _ hΓ => stepType_entails h hΓ) hm hΔ ht

theorem stepMode_substitute_entails {s a b t Δ} {σ : Substitution}
    (h : stepMode s a b = .success t) (hm : σ.modes = [])
    (hΔ : EntailsAll Δ (σ.bounds (t.pending ++ t.bounds))) :
    Entails Δ (σ.constraint (.mode a b)) :=
  Entails.consequence_substitute_types (fun _ hΓ => stepMode_entails h hΓ) hm hΔ
    (by simp [Constraint.typeVars])

theorem SolverState.TypeReady.finished_substitute_entails {s : SolverState}
    (hs : s.TypeReady) (hm : s.ModeInvariant) (hp : s.pending = [])
    {c Δ} {σ : Substitution} (hc : c ∈ s.seen) (hσ : σ.modes = [])
    (hΔ : EntailsAll Δ (σ.bounds s.bounds))
    (ht : ∀ v ∈ c.typeVars, (σ.type v).DefinedUnder Δ) : Entails Δ (σ.constraint c) :=
  Entails.consequence_substitute_types (fun _ hΓ => hs.finished_seen hm hp hc hΓ) hσ hΔ ht

theorem Substitution.singleType_equal_entails {n a Δ}
    (hn : TypeVar.flex n ∉ a.typeVars) (ha : a.DefinedUnder Δ) :
    Entails Δ (({types := [(n, a)]} : Substitution).constraint (.equal (.flex n) a)) := by
  have hfix := Substitution.ty_fixed ({types := [(n, a)]} : Substitution) a rfl
    (by simpa using hn)
  simp only [Substitution.constraint, List.lookup_cons, beq_self_eq_true]
  rw [hfix]
  exact ⟨.refl, .refl, ha, ha⟩

end ModalityInference
