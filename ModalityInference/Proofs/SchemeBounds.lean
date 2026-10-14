import ModalityInference.Proofs.GenerationInstantiation
import ModalityInference.Proofs.GroundSkolemization
import ModalityInference.Proofs.EntailmentTransport

/-! Explicit assumptions for scheme bounds. Equality directions and written
definedness guards preserve instances and support declarative context weakening. -/
namespace ModalityInference

theorem Substitution.wellFormedBounds_renaming (σ : Substitution) (a : Ty)
    (ht : ∀ v, ∃ w, σ.type v = .var w) :
    σ.bounds a.wellFormedBounds = (σ.ty a).wellFormedBounds := by
  induction a <;> simp_all [Substitution.bounds, Substitution.ty, TypeExpr.subst,
    TypeExpr.wellFormedBounds, Substitution.constraint, Constraint.subst]
  case var v => obtain ⟨w, hw⟩ := ht v; simp [hw, TypeExpr.wellFormedBounds]

theorem Substitution.constraint_assumptions_renaming (σ : Substitution) (c : Constraint)
    (ht : ∀ v, ∃ w, σ.type v = .var w) :
    σ.bounds c.assumptions = (σ.constraint c).assumptions := by
  have hg (a : Ty) : a.wellFormedBounds.map σ.constraint =
      (a.subst σ.type σ.mode).wellFormedBounds := σ.wellFormedBounds_renaming a ht
  cases c <;> simp only [Constraint.assumptions, Substitution.bounds,
    List.map_append, List.map_cons, List.map_nil]
  case equal v a =>
    cases v with
    | rigid n =>
      simpa [Substitution.constraint, Constraint.subst, Constraint.assumptions,
        TypeExpr.wellFormedBounds, Substitution.ty, TypeExpr.subst, Substitution.type]
        using σ.wellFormedBounds_renaming a ht
    | flex n =>
      obtain ⟨w, hw⟩ := ht (.flex n)
      cases he : σ.types.lookup n <;>
        simp [Substitution.type, he] at hw
      all_goals simpa [Substitution.constraint, Constraint.subst, Constraint.assumptions,
        TypeExpr.wellFormedBounds, Substitution.ty, TypeExpr.subst, Substitution.type, he, hw]
        using σ.wellFormedBounds_renaming a ht
  all_goals simp only [Substitution.constraint, Constraint.subst, hg]

theorem Substitution.bounds_assumptions_renaming (σ : Substitution) (cs : Bounds)
    (ht : ∀ v, ∃ w, σ.type v = .var w) :
    σ.bounds cs.assumptions = (σ.bounds cs).assumptions := by
  simp only [Bounds.assumptions, Substitution.bounds, List.map_flatMap, List.flatMap_map]
  exact congrArg (fun f => cs.flatMap f)
    (funext fun c => σ.constraint_assumptions_renaming c ht)

theorem Substitution.assumptions_renaming_entails (σ : Substitution) (cs Δ : Bounds)
    (ht : ∀ v, ∃ w, σ.type v = .var w) :
    EntailsAll (Δ ++ σ.bounds cs.assumptions) (σ.bounds cs) := by
  rw [σ.bounds_assumptions_renaming cs ht]
  exact fun c hc => c.assumptions_entail fun d hd =>
    List.mem_append_right Δ (List.mem_flatMap.mpr ⟨c, hc, hd⟩)

theorem Scheme.freshSubstitution_type_variable (s : Scheme) (nt nm : Nat)
    (rigid : Bool) (v : TypeVar) :
    ∃ w, (s.freshSubstitution nt nm rigid).type v = .var w := by
  cases v with
  | rigid n => exact ⟨.rigid n, rfl⟩
  | flex n =>
    cases he : (s.freshSubstitution nt nm rigid).types.lookup n
    · exact ⟨.flex n, by simp [Substitution.type, he]⟩
    · obtain ⟨i, _, rfl⟩ := lookup_fresh_some
        (xs := s.typeParams)
        (f := fun i => (TypeExpr.var (if rigid then .rigid (nt + i) else .flex (nt + i)))) he
      exact ⟨if rigid then .rigid (nt + i) else .flex (nt + i), by simp [Substitution.type, he]⟩

theorem Subsumes.refl (s : Scheme) (Δ : Bounds) : Subsumes Δ s s := by
  refine ⟨s.freshSubstitution (s.subsumptionIndices Δ s).1
    (s.subsumptionIndices Δ s).2 true, s.freshSubstitution_instantiates _ _ _, ?_, .refl⟩
  exact Bounds.assumptions_entails_append _ _

/-- Uniform syntactic instance preservation supplies the target's fresh skolem instance. -/
theorem Subsumes.of_instances {source target : Scheme} {Δ : Bounds}
    (h : ∀ Ξ θ, Instantiates target θ → EntailsAll Ξ (θ.bounds target.bounds) →
      ∃ σ, Instantiates source σ ∧ EntailsAll Ξ (σ.bounds source.bounds) ∧
        Subtype Ξ (σ.ty source.body) (θ.ty target.body)) : Subsumes Δ source target :=
  h _ _ (target.freshSubstitution_instantiates _ _ _) (Bounds.assumptions_entails_append _ _)

theorem ContextLe.refl (Γ : Context) (Δ : Bounds) : ContextLe Δ Γ Γ := by
  induction Γ with
  | nil => exact .nil
  | cons s Γ ih =>
    cases s with
    | none => exact .drop ih
    | some s => exact .keep ih (Subsumes.refl s Δ)

def Scheme.withAssumptions (s : Scheme) : Scheme :=
  {s with bounds := s.bounds.assumptions}

theorem Scheme.withAssumptions_instance (s : Scheme) (θ : Substitution) (Δ : Bounds) (a : Ty) :
    (Instantiates s.withAssumptions θ ∧
      EntailsAll Δ (θ.bounds s.withAssumptions.bounds) ∧ θ.ty s.withAssumptions.body = a) ↔
    (Instantiates s θ ∧ EntailsAll Δ (θ.bounds s.bounds) ∧ θ.ty s.body = a) := by
  simp only [Instantiates, withAssumptions, θ.bounds_assumptions_entails]

theorem Scheme.subsumes_addAssumptions (s : Scheme) (cs Δ : Bounds) :
    Subsumes Δ s {s with bounds := (s.bounds ++ cs).assumptions} := by
  refine ⟨s.freshSubstitution (s.subsumptionIndices Δ {s with bounds := (s.bounds ++ cs).assumptions}).1
    (s.subsumptionIndices Δ {s with bounds := (s.bounds ++ cs).assumptions}).2 true,
    s.freshSubstitution_instantiates _ _ _, ?_, .refl⟩
  exact (Solution.append.mp (EntailsAll.of_subst_assumptions
    (Bounds.assumptions_entails_append _ _))).1

theorem Scheme.subsumes_withAssumptions (s : Scheme) (Δ : Bounds) :
    Subsumes Δ s s.withAssumptions := by
  simpa [withAssumptions] using s.subsumes_addAssumptions [] Δ

theorem Scheme.withAssumptions_refl (s : Scheme) (Δ : Bounds) :
    Subsumes Δ s.withAssumptions s.withAssumptions := Subsumes.refl _ _

theorem Scheme.lock_withAssumptions {s : Scheme} {Δ : Bounds} {m : ModExpr}
    (hb : s.FreshForBounds Δ) (hm : s.FreshForMode m) :
    ∃ source, Subsumes Δ s source ∧
      Lock Δ m [some source] [some (s.lock m).withAssumptions] := by
  refine ⟨{s with bounds := (s.lock m).bounds.assumptions},
    s.subsumes_addAssumptions [.sub s.body (.modal s.body (.future m))] Δ,
    .keep .nil hb hm ?_⟩
  exact .bound (by simp [Scheme.lock, Bounds.assumptions, Constraint.assumptions])

theorem Subtype.modal_comm {Δ a m n} (hm : Entails Δ (.defined m))
    (hn : Entails Δ (.defined n)) :
    Subtype Δ (.modal (.modal a m) n) (.modal (.modal a n) m) := by
  refine .trans .compose (.trans (.congr .refl (.valid ?_)) .composeRev)
  intro η hη
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := And.intro
    (Option.isSome_iff_exists.mp (hm η hη)) (Option.isSome_iff_exists.mp (hn η hη))
  simp [ModExpr.Below, ModExpr.eval, hx, hy, Mode.compose_comm]

theorem Subtype.aliased_idempotent (Δ : Bounds) (a : Ty) :
    Subtype Δ (.modal (.modal a (.const Mode.aliased)) (.const Mode.aliased))
      (.modal a (.const Mode.aliased)) :=
  .trans .compose (.congr .refl (.valid fun _ _ =>
    ⟨Mode.aliased, Mode.aliased, rfl, rfl, by decide⟩))

theorem Subtype.share_result {Δ : Bounds} {a : Ty}
    (h : Subtype Δ a (.modal a (.const Mode.many))) :
    Subtype Δ a (.modal (.modal a (.const Mode.aliased)) (.const Mode.many)) :=
  h.trans ((Subtype.congr .refl (.valid fun _ _ =>
    ⟨Mode.many, Mode.aliased.compose Mode.many, rfl, rfl, by decide⟩)).trans .composeRev)

theorem Scheme.subsumes_share_withAssumptions (s : Scheme) (Δ : Bounds) :
    Subsumes Δ s (s.share.withAssumptions.modal (.const Mode.many)) := by
  let target := s.share.withAssumptions.modal (.const Mode.many)
  let θ := s.freshSubstitution (s.subsumptionIndices Δ target).1
    (s.subsumptionIndices Δ target).2 true
  have hs : EntailsAll (Δ ++ (θ.bounds target.bounds).assumptions) (θ.bounds s.share.bounds) :=
    (Bounds.assumptions_entails_append _ _).of_subst_assumptions
  refine ⟨θ, s.freshSubstitution_instantiates _ _ _, (Solution.append.mp hs).1, ?_⟩
  exact ((Solution.append.mp hs).2
    (θ.constraint (.sub s.body (.modal s.body (.const Mode.many))))
    (by simp [Substitution.bounds])).1.share_result

theorem Scheme.share_withAssumptions {s : Scheme} {Δ : Bounds} (hb : s.FreshForBounds Δ) :
    ∃ source, Subsumes Δ s source ∧
      ContextJoin Δ [some s.share.withAssumptions] [some s.share.withAssumptions] [some source] :=
  ⟨s.share.withAssumptions.modal (.const Mode.many), s.subsumes_share_withAssumptions Δ,
    .shared .nil hb (Subtype.aliased_idempotent _ _)⟩

def Context.withAssumptions (Γ : Context) : Context := Γ.map (Option.map Scheme.withAssumptions)

theorem Context.withAssumptions_le (Γ : Context) (Δ : Bounds) :
    ContextLe Δ Γ Γ.withAssumptions := by
  induction Γ with
  | nil => exact .nil
  | cons s Γ ih =>
    cases s with
    | none => exact .drop ih
    | some s => exact .keep ih (s.subsumes_withAssumptions Δ)

theorem Context.withAssumptions_refl (Γ : Context) (Δ : Bounds) :
    ContextLe Δ Γ.withAssumptions Γ.withAssumptions := by
  induction Γ with
  | nil => exact .nil
  | cons s Γ ih =>
    cases s with
    | none => exact .drop ih
    | some s => exact .keep ih (s.withAssumptions_refl Δ)

end ModalityInference
