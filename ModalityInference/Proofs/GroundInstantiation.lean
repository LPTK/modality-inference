import ModalityInference.Proofs.GroundSubtyping
import ModalityInference.Proofs.Resources

/-! Syntactic scheme instantiation induces a ground instance. Defined results
and modeled bounds are preserved; all non-quantified identifiers remain fixed. -/
namespace ModalityInference

theorem ModExpr.eval_refinement (m : ModExpr) {σ τ : ModVar → Option Mode}
    (hσ : ∀ v n, σ v = some n → τ v = some n) {n : Mode}
    (h : m.eval σ = some n) : m.eval τ = some n := by
  induction m generalizing n <;> simp only [ModExpr.eval, bind, pure, Option.bind_eq_some_iff] at *
  all_goals aesop

/-- Fill undefined substitution images with arbitrary defaults. The lemmas below
prove that every successful type or constraint interpretation is unchanged. -/
def Substitution.ground (σ : Substitution) (ρ : GroundAssignment) : GroundAssignment :=
  ⟨fun v => ((σ.type v).realize ρ).getD (.unit Mode.identity),
   fun v => ((σ.mode v).eval (some ∘ ρ.modes)).getD Mode.identity⟩

theorem ModExpr.eval_ground {σ : Substitution} {ρ : GroundAssignment} {m : ModExpr} {n : Mode}
    (h : (m.subst σ.mode).eval (some ∘ ρ.modes) = some n) :
    m.eval (some ∘ (σ.ground ρ).modes) = some n := by
  rw [ModExpr.eval_subst] at h
  exact m.eval_refinement (fun v n hn => by simp [Substitution.ground, hn]) h

theorem TypeExpr.realize_ground (a : Ty) {σ : Substitution} {ρ : GroundAssignment}
    {t : GroundTy} (h : (σ.ty a).realize ρ = some t) :
    a.realize (σ.ground ρ) = some t := by
  induction a generalizing t <;>
    simp only [Substitution.ty, TypeExpr.subst, TypeExpr.realize, bind, pure,
      Option.bind_eq_some_iff] at *
  case modal a m ih =>
    exact let ⟨x, hx, n, hn, ht⟩ := h
      ⟨x, ih hx, n, ModExpr.eval_ground hn, ht⟩
  case var => simp [Substitution.ground, h]
  all_goals aesop

theorem GroundSatisfies.pullback {σ : Substitution} {ρ : GroundAssignment} {c : Constraint}
    (h : GroundSatisfies ρ (σ.constraint c)) : GroundSatisfies (σ.ground ρ) c := by
  cases c
  case equal v a =>
    cases v <;> simp only [Substitution.constraint, GroundSatisfies] at h ⊢
    case flex n =>
      cases he : σ.types.lookup n <;> simp only [he] at h
      case some t =>
        exact let ⟨x, y, hx, hy, hs⟩ := h
          ⟨y, a.realize_ground hy,
            by simpa [Substitution.ground, Substitution.type, he, hx] using hs⟩
      case none =>
        exact let ⟨y, hy, hs⟩ := h
          ⟨y, a.realize_ground hy,
            by simpa [Substitution.ground, Substitution.type, TypeExpr.realize, he] using hs⟩
    case rigid n => exact let ⟨y, hy, hs⟩ := h
      ⟨y, a.realize_ground hy, hs⟩
  case sub a b | equiv a b =>
    exact let ⟨x, y, hx, hy, hs⟩ := h
      ⟨x, y, a.realize_ground hx, b.realize_ground hy, hs⟩
  case mode a b =>
    exact let ⟨x, y, hx, hy, hs⟩ := h
      ⟨x, y, ModExpr.eval_ground hx, ModExpr.eval_ground hy, hs⟩
  case defined m =>
    exact let ⟨n, hn⟩ := Option.isSome_iff_exists.mp h
      Option.isSome_iff_exists.mpr ⟨n, ModExpr.eval_ground hn⟩

theorem GroundModels.pullback {σ : Substitution} {ρ : GroundAssignment} {cs : Bounds}
    (h : GroundModels ρ (σ.bounds cs)) : GroundModels (σ.ground ρ) cs :=
  fun c hc => (h (σ.constraint c) (List.mem_map.mpr ⟨c, hc, rfl⟩)).pullback

private theorem lookup_none_of_not_key {α : Type} {xs : List (Nat × α)} {n : Nat}
    (h : n ∉ xs.map Prod.fst) : xs.lookup n = none := by
  exact List.lookup_eq_none_iff.mpr fun p hp => by
    simpa only [bne_iff_ne] using
      (fun he : n = p.1 => h (List.mem_map.mpr ⟨p, hp, he.symm⟩))

theorem Instantiates.ground {σ : Substitution} {s : Scheme} {ρ : GroundAssignment}
    (h : Instantiates s σ) (hb : GroundModels ρ (σ.bounds s.bounds)) :
    GroundInstantiates ρ s (σ.ground ρ) := by
  refine ⟨?_, ?_, hb.pullback⟩
  all_goals rintro (n | n) hv
  case refine_1.flex =>
    have he : σ.types.lookup n = none := lookup_none_of_not_key fun hn =>
      hv (List.mem_map.mpr ⟨n, h.1.mem_iff.mp hn, rfl⟩)
    simp [Substitution.ground, Substitution.type, TypeExpr.realize, he]
  case refine_2.flex =>
    have he : σ.modes.lookup n = none := lookup_none_of_not_key fun hn =>
      hv (List.mem_map.mpr ⟨n, h.2.mem_iff.mp hn, rfl⟩)
    simp [Substitution.ground, Substitution.mode, ModExpr.eval, he]
  all_goals rfl

theorem BoundsSatisfiable.ground {cs : Bounds} (h : BoundsSatisfiable cs) :
    ∃ ρ, GroundModels ρ cs :=
  let ⟨σ, _, _, hs⟩ := h
  let ρ : GroundAssignment := ⟨fun _ => .unit Mode.identity, fun _ => Mode.identity⟩
  ⟨σ.ground ρ, (hs.groundModels (ρ := ρ) (by simp [GroundModels])).pullback⟩

theorem ResourceEnvironmentInterpretation.instantiated_lookup
    {ρ w Δ Γ γ reserved i s σ ground}
    (hγ : ResourceEnvironmentInterpretation ρ w Γ γ reserved) (hΔ : GroundModels ρ Δ)
    (hi : Γ[i]? = some (some s)) (hσ : Instantiates s σ)
    (hb : EntailsAll Δ (σ.bounds s.bounds)) (ha : (σ.ty s.body).realize ρ = some ground) :
    ResourceSemanticEvaluation w γ (.var i) ground (ContextResources Γ reserved) :=
  hγ.lookup hi (hσ.ground (hb.groundModels hΔ)) (s.body.realize_ground ha)

end ModalityInference
