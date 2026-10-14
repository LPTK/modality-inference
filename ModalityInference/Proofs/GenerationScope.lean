import ModalityInference.Proofs.GenerationCorrespondence
import ModalityInference.Proofs.ResourceSoundness

/-! A symbolic lock must remain outside the quantifiers of a captured scheme. -/
namespace ModalityInference.GenerationScope

def μ : ModExpr := .var (.flex 0)
def scheme : Scheme := {modParams := [0], body := .modal .credit μ}
def selected : Substitution := {modes := [(0, .epsilon)]}
def solution : Substitution := {modes := [(0, .const Mode.many)]}
def bodyType : Ty := selected.ty (scheme.lock μ).body
def resultType : Ty := .modal (.fn .unit bodyType) μ
def constraints : Bounds :=
  selected.bounds (scheme.lock μ).bounds ++
    [.sub bodyType bodyType] ++ [.sub .unit .unit, .defined μ]
def term : RawTerm := .lam () (.var 1)

theorem generated : Generates [.binding (some scheme)] term resultType constraints := by
  apply Generates.lam
  apply Generates.var (.there (.locked .here))
  simp [Instantiates, selected, scheme]

theorem source_scoped : Context.Scoped {} [some scheme] := by
  simp [Context.Scoped, Scheme.Scoped, scheme, Scheme.freeTypes, Scheme.freeModes,
    TypeExpr.typeVars, TypeExpr.modVars, Bounds.typeVars, Bounds.modVars, μ, ModExpr.vars]

theorem lock_collision : ¬scheme.FreshForMode μ := by
  simp [Scheme.FreshForMode, scheme, μ, ModExpr.vars]

theorem not_hygienic : ¬generated.Hygienic := by
  intro h
  obtain ⟨a, b, m, he, hf⟩ := h.lam_fresh
  change TypeExpr.modal (.fn .unit bodyType) μ = .modal (.fn a b) m at he
  cases he
  exact lock_collision (hf scheme (by simp))

theorem solved : Solution constraints [] solution := by
  simp [Solution, constraints, bodyType, scheme, Scheme.lock, selected, solution,
    μ, Substitution.bounds, Substitution.constraint, Constraint.subst,
    Substitution.ty, TypeExpr.subst, Substitution.mode, ModExpr.subst,
    EntailsAll, Entails, TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds,
    ModeModels, ModeSatisfies, ModExpr.WellFormed, ModExpr.eval, ModExpr.epsilon]
  refine ⟨Subtype.identityRev.trans (.congr .refl (.valid ?_)), .refl, .refl⟩
  intro η hη
  simp [ModExpr.Below, ModExpr.eval, ModExpr.epsilon, Mode.future, Mode.identity, Mode.le]

def assignment : GroundAssignment := ⟨fun _ => .unit Mode.identity, fun _ => Mode.identity⟩
def world : World := ⟨{0}⟩
def supplies : Supplies := {heap := ⟨1, 1⟩}

theorem compatible : world.Compatible supplies [.unit, .credit (.heap 0)] := by
  refine ⟨?_, by decide, ?_, ?_⟩
  · simp [supplies, Supplies.Valid, Supply.at]
  · simp [supplies, world, Supply.at]
  rintro l ⟨v, hv, hr⟩ hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · cases hr
  · cases hr
    simp [supplies, Supplies.FreshLocation, Supply.at, Nat.add_comm] at hf

theorem environment : ResourceEnvironmentInterpretation assignment world
    (Context.subst [some scheme] solution) [.credit (.heap 0)] (fun _ => {.heap 0}) := by
  change ResourceEnvironmentInterpretation assignment world
    [some {modParams := [1], body := .modal .credit (.var (.flex 1))}]
    [.credit (.heap 0)] (fun _ => {.heap 0})
  apply ResourceEnvironmentInterpretation.singleton
  refine ⟨fun _ hl => (Set.mem_singleton_iff.mp hl).symm ▸ References.credit, ?_⟩
  intro η t hη ht
  simp [TypeExpr.realize, ModExpr.eval, GroundTy.modal] at ht
  subst t
  exact ⟨_, cellResources_subset _ _, .credit (by simp [World.Live]) (Or.inr trivial)⟩

theorem realizes : (solution.ty resultType).realize assignment =
    some (.fn (.unit Mode.identity) (.credit Mode.identity) Mode.many) := rfl

theorem no_reusable_capture (captured : Capture) (owned : Resources) :
    ¬ ResourceInterpretation world
      (.fn (.unit Mode.identity) (.credit Mode.identity) Mode.many) Mode.identity
      (.closure [.credit (.heap 0)] captured (.var 1)) owned := by
  intro h
  have hz : owned = ∅ := h.2.2.2.1 rfl
  have hlive : ∀ v ∈ [Value.credit (.heap 0)], world.ValidValue v := by
    rintro v hv l hl
    cases List.mem_singleton.mp hv
    cases hl
    simp [World.Live]
  have hu : ResourceInterpretation world (.unit Mode.identity) Mode.identity .unit ∅ := by
    exact ⟨(fun _ h => nomatch h), (by simp), rfl⟩
  obtain ⟨result, resources, he, hr, hb⟩ :=
    h.2.2.2.2 world .unit ∅ hlive hu (by simp) supplies compatible
  have heq : result = .credit (.heap 0) := he.deterministic (.var rfl)
  subst result
  have hr0 : resources = {.heap 0} := hr.2.2.2
  have hc := hb (show Location.heap 0 ∈ resources by rw [hr0]; exact Set.mem_singleton _)
  simp [hz, supplies, Supplies.FreshLocation, Supply.at, Nat.add_comm] at hc

theorem not_typable :
    ¬RawTyping [] (Context.subst [some scheme] solution) term (solution.ty resultType) := by
  rintro ⟨t, he, ht⟩
  cases t <;> simp [term, Term.erase, Term.mapAnnotation] at he
  rename_i captured body
  cases body <;> simp [Term.mapAnnotation] at he
  rename_i i
  subst i
  have hsup : world.Compatible supplies [.credit (.heap 0)] :=
    ⟨compatible.1, compatible.2.1, compatible.2.2.1,
      fun l ⟨v, hv, hr⟩ => compatible.2.2.2 l ⟨v, List.mem_cons_of_mem _ hv, hr⟩⟩
  obtain ⟨v, owned, hv, hr, _⟩ :=
    ht.resource_semantic (by simp [GroundModels]) environment realizes supplies hsup
  have heq : v = .closure [.credit (.heap 0)] captured (.var 1) :=
    hv.deterministic (by simpa [trimEnvironment, Term.freeVars] using
      (Eval.lam (s := supplies) (γ := [.credit (.heap 0)])
        (captured := captured) (body := .var 1)))
  exact no_reusable_capture captured owned (heq ▸ hr)

/-- Archived unrestricted contract, refuted even with a well-scoped source context. -/
def UnrestrictedGenerationSoundness : Prop := ∀ {Γ : Context} {t a cs Δ σ},
    Generates (Γ.map ContextEntry.binding) t a cs → Solution cs Δ σ →
    RawTyping Δ (Γ.subst σ) t (σ.ty a)

theorem no_unrestricted_generation_sound : ¬UnrestrictedGenerationSoundness := by
  intro h
  exact not_typable (h generated solved)

end ModalityInference.GenerationScope
