import ModalityInference.Proofs.GuardedSourceTyping
import ModalityInference.Proofs.DefinedInstantiation
import ModalityInference.Proofs.GeneralizedSubstitution

/-! Defined comparison certificates for generation's context refinements. -/
namespace ModalityInference

/-- The written constraints establish the body guard for every instance. -/
def Scheme.GuardsBody (s : Scheme) : Prop :=
  ∀ (Δ : Bounds) (σ : Substitution), EntailsAll Δ (σ.bounds s.bounds) →
    (σ.ty s.body).DefinedUnder Δ

theorem Scheme.refineMode_guardsBody (s : Scheme) (p : Nat) :
    (s.refineMode p).GuardsBody := by
  intro Δ σ hb
  exact ((s.refineMode_instance_bounds σ p Δ).mp hb).2.2.2

theorem Scheme.lock_guardsBody (s : Scheme) (m : ModExpr) :
    (s.lock m).GuardsBody := by
  intro Δ σ hb
  have hh := ((s.lock_instance_bounds σ m Δ).mp hb).2
  exact TypeExpr.definedUnder_modal.mpr
    ⟨hh.2.1, Entails.defined_capture_of_future (TypeExpr.definedUnder_modal.mp hh.2.2).2⟩

theorem Scheme.GuardsBody.lockAll {s : Scheme} (h : s.GuardsBody) (ms : List ModExpr) :
    (s.lockAll ms).GuardsBody := by
  cases ms with
  | nil => exact h
  | cons m ms => exact (s.lockAll ms).lock_guardsBody m

theorem Scheme.GuardsBody.withAssumptions {s : Scheme} (h : s.GuardsBody) :
    s.withAssumptions.GuardsBody :=
  fun Δ σ hb => h Δ σ hb.of_subst_assumptions

theorem Scheme.GuardsBody.modal_const {s : Scheme} (h : s.GuardsBody) (m : Mode) :
    (s.modal (.const m)).GuardsBody := by
  intro Δ σ hb
  exact TypeExpr.definedUnder_modal.mpr ⟨h Δ σ hb, fun _ _ => rfl⟩

/-- Normalizing unused images preserves the original comparison and enforces
all image guards whenever its source bounds already establish the body guard. -/
theorem Subsumes.under_of_guardsBody {Δ : Bounds} {s t : Scheme}
    (h : Subsumes Δ s t) (hs : s.GuardsBody) : SubsumesUnder Δ s t := by
  obtain ⟨σ, hi, hb, ht⟩ := h
  obtain ⟨τ, hτ, he, hc⟩ := hi.exists_under hb (hs _ σ hb)
  exact ⟨τ, hτ, hc ▸ hb, he ▸ ht⟩

def Context.GuardsBodies (Γ : Context) : Prop :=
  ∀ s, some s ∈ Γ → s.GuardsBody

theorem ContextLe.guarded_of_source {Δ Γ Γ'} (h : ContextLe Δ Γ Γ')
    (hΓ : Γ.GuardsBodies) : GuardedContextLe Δ Γ Γ' := by
  induction h with
  | nil => exact .nil
  | drop _ ih => exact .drop (ih (fun s hs => hΓ s (List.mem_cons_of_mem _ hs)))
  | @keep Γ Γ' s t _ hs ih =>
    exact .keep (ih (fun s hs => hΓ s (List.mem_cons_of_mem _ hs)))
      (hs.under_of_guardsBody (hΓ s List.mem_cons_self))

theorem AlgorithmicContext.refinedContext_guardsBodies (Γ : AlgorithmicContext)
    (p : Nat) (ms : List ModExpr := []) : (Γ.refinedContext p ms).GuardsBodies := by
  induction Γ generalizing ms with
  | nil => exact fun _ h => False.elim (List.not_mem_nil h)
  | cons entry Γ ih =>
    cases entry with
    | lock m => exact ih _
    | binding entry =>
      cases entry with
      | none =>
        intro s hs
        simp only [refinedContext, Option.map_none, List.mem_cons, reduceCtorEq, false_or] at hs
        exact ih ms s hs
      | some s =>
        intro t ht
        simp only [refinedContext, Option.map_some, List.mem_cons, Option.some.injEq] at ht
        rcases ht with rfl | ht
        · exact ((s.refineMode_guardsBody p).lockAll ms).withAssumptions
        · exact ih ms t ht

/-- The target's refinement guard certifies the body of the reconstructed source
instance, including when the unrefined source scheme has no global body guard. -/
theorem Scheme.subsumesUnder_refined_of_instances {source base : Scheme} {p : Nat}
    (hp : base.freshModeIndex ≤ p) (Δ : Bounds)
    (hinst : ∀ θ, Instantiates base θ → ∃ τ, Instantiates source τ ∧
      τ.ty source.body = θ.ty base.body ∧
      ∀ Ξ, EntailsAll Ξ (τ.bounds source.bounds) ↔ EntailsAll Ξ (θ.bounds base.bounds)) :
    SubsumesUnder Δ source (base.refineMode p).withAssumptions := by
  let target := (base.refineMode p).withAssumptions
  let θ := base.freshSubstitution (source.subsumptionIndices Δ target).1
    (source.subsumptionIndices Δ target).2 true
  let m := ModExpr.var (.rigid ((source.subsumptionIndices Δ target).2 + base.modParams.length))
  have hi : Instantiates base θ := base.freshSubstitution_instantiates _ _ _
  have hb := (hi.refineMode_bounds hp m
    (Δ ++ ((θ.extendMode p m).bounds target.bounds).assumptions)).mp
      (EntailsAll.of_subst_assumptions (Bounds.assumptions_entails_append _ _))
  obtain ⟨τ, hi', ha', hb'⟩ := hinst θ hi
  have hd := ha'.symm ▸ hb.2.2.1
  obtain ⟨υ, hu, he, hc⟩ := hi'.exists_under ((hb' _).mpr hb.1) hd
  have hsub := ha'.symm ▸ (hi.refineMode_body hp m).symm ▸ hb.2.1
  have htarget (nt nm : Nat) (rigid : Bool) : target.freshSubstitution nt nm rigid =
      (base.refineMode p).freshSubstitution nt nm rigid := rfl
  change SubsumesUnder Δ source target
  simp only [SubsumesUnder, Scheme.instantiate, htarget, Scheme.refineMode_freshSubstitution]
  exact ⟨υ, hu, hc ▸ (hb' _).mpr hb.1, he ▸ hsub⟩

theorem Scheme.generalize_subsumesUnder_substAvoid_refined (cs : Bounds) (a : Ty)
    (σ : Substitution) (avoid Δ : Bounds) {p : Nat}
    (hp : ((generalize cs a).substAvoid σ avoid).freshModeIndex ≤ p) :
    SubsumesUnder Δ (generalize cs a)
      (((generalize cs a).substAvoid σ avoid).refineMode p).withAssumptions :=
  subsumesUnder_refined_of_instances hp Δ (fun _ hi => hi.unsubstAvoid_generalize)

theorem Scheme.subsumesUnder_substAvoid_refined (s : Scheme) (σ : Substitution)
    (avoid Δ : Bounds) {p : Nat} (hp : (s.substAvoid σ avoid).freshModeIndex ≤ p) :
    SubsumesUnder Δ (s.subst σ) ((s.substAvoid σ avoid).refineMode p).withAssumptions :=
  subsumesUnder_refined_of_instances hp Δ (fun _ hi => hi.unsubstitute_identity
    (Substitution.identityAt_type _ _) (Substitution.identityAt_mode _ _))

theorem Scheme.subsumesUnder_refineMode_withAssumptions {s : Scheme} {p : Nat}
    (hp : s.freshModeIndex ≤ p) (Δ : Bounds) :
    SubsumesUnder Δ s (s.refineMode p).withAssumptions :=
  subsumesUnder_refined_of_instances hp Δ (fun θ hi => ⟨θ, hi, rfl, fun _ => Iff.rfl⟩)

theorem Context.substAvoid_refined_guarded (Γ : Context) (σ : Substitution)
    (avoid Δ : Bounds) {p : Nat}
    (hp : ∀ s, some s ∈ Γ → (s.substAvoid σ avoid).freshModeIndex ≤ p) :
    GuardedContextLe Δ (Γ.subst σ)
      ((AlgorithmicContext.substAvoid (Γ.map ContextEntry.binding) σ avoid).refinedContext p) := by
  induction Γ with
  | nil => exact .nil
  | cons entry Γ ih =>
    cases entry with
    | none => exact .drop (ih (fun s hs => hp s (List.mem_cons_of_mem _ hs)))
    | some s =>
      exact .keep (ih (fun s hs => hp s (List.mem_cons_of_mem _ hs)))
        (s.subsumesUnder_substAvoid_refined σ avoid Δ (hp s List.mem_cons_self))

end ModalityInference
