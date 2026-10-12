import ModalityInference.Proofs.Interpretation
import ModalityInference.Proofs.Evaluation
import ModalityInference.Proofs.Annotations

/-! A focused check of scheme instantiation and symbolic closure captures. -/
namespace ModalityInference.PolymorphicCapture

def creditScheme : Scheme := .mono (.modal .credit (.var (.flex 0)))
def functionScheme : Scheme :=
  { modParams := [0], body := .fn .unit creditScheme.body }
def value : Value := .closure [.credit (.heap 0)] [some creditScheme] (.var 1)

theorem interpreted (ρ : GroundAssignment) (w : World) :
    ValueInterpretation ρ w
      (.fn (.unit Mode.identity) (.credit (ρ.modes (.flex 0))) Mode.identity)
      Mode.identity value := by
  simp only [value, ValueInterpretation, GroundTy.mode, Mode.compose, Mode.identity,
    Bool.true_and, Bool.true_eq_false, false_implies, true_and]
  constructor
  · intro l hl
    cases hl with | closure hv hr =>
    cases List.mem_singleton.mp hv
    cases hr; trivial
  · intro w' x hγ _ _ supplies _
    refine ⟨.credit (.heap 0), .var rfl, ⟨hγ _ (by simp), Or.inr trivial⟩, ?_⟩
    intro l hl
    refine Or.inl ⟨0, creditScheme, _, rfl, rfl, ρ, _, ?_, ?_, hl⟩
    all_goals simp [GroundInstantiates, GroundModels, creditScheme, Scheme.mono,
      TypeExpr.realize, ModExpr.eval, GroundTy.modal, Mode.identity, Mode.compose]

theorem scheme_interpreted (ρ : GroundAssignment) (w : World) :
    SchemeInterpretation ρ w functionScheme value := by
  intro η t _ ht
  simp [functionScheme, creditScheme, Scheme.mono, TypeExpr.realize, ModExpr.eval,
    GroundTy.modal, Mode.identity, Mode.compose] at ht
  exact ht ▸ interpreted η w

def assignment : GroundAssignment :=
  ⟨fun _ => .unit Mode.identity, fun _ => Mode.aliased⟩

theorem no_capture_ownership (l : Location) :
    ¬ EnvironmentOwns assignment [.credit (.heap 0)] [some creditScheme] l := by
  rintro ⟨i, s, v, hs, hv, η, t, hη, ht, ho⟩
  cases i <;> simp_all only [List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.getElem?_nil, Option.some.injEq, reduceCtorEq]
  subst s v
  have hm : η.modes (.flex 0) = Mode.aliased := hη.2.1 _ (by
    simp [creditScheme, Scheme.mono, Scheme.freeModes, TypeExpr.modVars, ModExpr.vars,
      Bounds.modVars])
  simp [creditScheme, Scheme.mono, TypeExpr.realize, ModExpr.eval,
    GroundTy.modal, Mode.identity, Mode.compose, hm] at ht
  subst t
  cases ho; contradiction

def world : World := ⟨{0}⟩
def supplies : Supplies := { heap := ⟨1, 1⟩ }

theorem compatible : world.Compatible supplies [.unit, .credit (.heap 0)] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals simp [supplies, world, Supplies.Valid, Supply.at, Supplies.FreshLocation]
  rintro l ⟨v, hv, hr⟩
  rcases List.mem_cons.mp hv with rfl | hv
  · cases hr
  · cases List.mem_singleton.mp hv
    cases hr; omega

theorem not_instantiated :
    ¬ ValueInterpretation assignment world
      (.fn (.unit Mode.identity) (.credit Mode.identity) Mode.identity)
      Mode.identity value := by
  intro h
  obtain ⟨result, he, _, hs⟩ := h.2.2.2 world .unit
    (by
      rintro v hv l hl
      cases List.mem_singleton.mp hv
      cases hl; trivial)
    ⟨(fun _ hl => nomatch hl), trivial⟩
    (fun _ h => nomatch h.2) supplies compatible
  have hresult : result = .credit (.heap 0) := he.deterministic (.var rfl)
  subst result
  rcases hs (.heap 0) (.credit rfl) with ho | ho | hf
  · exact no_capture_ownership _ ho
  · cases ho
  · exact compatible.2.2.2 _ ⟨_, by simp, .credit⟩ hf

def uniqueInstance : Substitution := { modes := [(0, .const Mode.identity)] }

theorem variable_typed : Typing [] [some functionScheme] (.var 0)
    (uniqueInstance.ty functionScheme.body) := by
  apply Typing.var (σ := uniqueInstance) rfl
  all_goals simp [Instantiates, uniqueInstance, functionScheme, EntailsAll, Substitution.bounds]

theorem environment_interpreted :
    EnvironmentInterpretation assignment world [some functionScheme] [value] := by
  have index : ∀ i s, [some functionScheme][i]? = some (some s) →
      i = 0 ∧ s = functionScheme := by
    intro i s
    cases i <;> simp [eq_comm]
  constructor
  · intro i s hs
    rcases index i s hs with ⟨rfl, rfl⟩
    exact ⟨value, rfl, scheme_interpreted _ _⟩
  · intro i j s t v w l hij hi hj _ _
    exact (hij ((index i s hi).1.trans (index j t hj).1.symm)).elim

theorem instance_realizes : (uniqueInstance.ty functionScheme.body).realize assignment =
    some (.fn (.unit Mode.identity) (.credit Mode.identity) Mode.identity) := rfl

theorem references (l : Location) (h : References value l) :
    EnvironmentReferences [.unit, .credit (.heap 0)] l := by
  cases h with
  | closure hv hr => exact ⟨_, List.mem_cons_of_mem _ hv, hr⟩

theorem compatible_value : world.Compatible supplies [value] :=
  ⟨compatible.1, compatible.2.1, compatible.2.2.1,
    fun l ⟨_, hv, hr⟩ => compatible.2.2.2 l
      (references l (List.mem_singleton.mp hv ▸ hr))⟩

theorem variable_not_semantic : ¬ SemanticEvaluation assignment world [some functionScheme]
    [value] (.var 0) (.fn (.unit Mode.identity) (.credit Mode.identity) Mode.identity) := by
  intro h
  obtain ⟨v, he, hv, _⟩ := h supplies compatible_value
  exact not_instantiated (he.deterministic (.var rfl) ▸ hv)

/-- The current fundamental statement is false: lookup instantiates the type but
leaves capture annotations interpreted by the ambient assignment. This witness
uses no admitted metatheory. A repair must also transport the capture metadata. -/
theorem no_unrestricted_soundness : ¬ (∀ {Δ Γ t a ρ w γ ground},
    Typing Δ Γ t a → GroundModels ρ Δ → EnvironmentInterpretation ρ w Γ γ →
    a.realize ρ = some ground → SemanticEvaluation ρ w Γ γ t ground) := by
  intro h
  exact variable_not_semantic (h variable_typed (by simp [GroundModels])
    environment_interpreted instance_realizes)

/-- Transporting the same instantiation into the capture makes its ownership
annotation concrete; it leaves the heap cell and the closure body unchanged. -/
theorem transported_value : value.substTypes uniqueInstance =
    .closure [.credit (.heap 0)] [some (.mono (.modal .credit (.const Mode.identity)))]
      (.var 1) := by
  simp [Value.substTypes, Value.mapAnnotation, value, uniqueInstance, creditScheme,
    Scheme.mono, Scheme.subst, Scheme.fresheningIndices, Scheme.instantiate, Scheme.freshSubstitution,
    Substitution.bounds, Substitution.ty, Substitution.mode,
    TypeExpr.subst, ModExpr.subst, Term.mapAnnotation]

theorem transported_capture_owns (ρ : GroundAssignment) :
    EnvironmentOwns ρ [.credit (.heap 0)]
      [some (.mono (.modal .credit (.const Mode.identity)))] (.heap 0) := by
  refine ⟨0, _, _, rfl, rfl, ρ, .credit Mode.identity, ?_, rfl, .credit rfl⟩
  simp [GroundInstantiates, GroundModels, Scheme.mono]

/-- The transported closure satisfies the unique-result contract under every
ambient assignment, including the aliased assignment in the counterexample. -/
theorem transported_interpreted (ρ : GroundAssignment) (w : World) :
    ValueInterpretation ρ w
      (.fn (.unit Mode.identity) (.credit Mode.identity) Mode.identity)
      Mode.identity (value.substTypes uniqueInstance) := by
  have hv : w.ValidValue (value.substTypes uniqueInstance) :=
    (Value.valid_mapAnnotation _ _ _).mpr (interpreted ρ w).1
  rw [transported_value] at hv ⊢
  refine ⟨hv, (fun h => Bool.noConfusion h), (fun h => Bool.noConfusion h), ?_⟩
  intro w' x hγ _ _ s _
  refine ⟨.credit (.heap 0), .var rfl, ⟨hγ _ (by simp), Or.inr trivial⟩, ?_⟩
  intro l ho
  cases ho; exact Or.inl (transported_capture_owns ρ)

end ModalityInference.PolymorphicCapture
