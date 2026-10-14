import ModalityInference.Proofs.Grounding
import ModalityInference.Proofs.Subtyping
import ModalityInference.Proofs.VariableOccurrences

/-! Skolemization must avoid ambient bounds as well as both schemes. -/
namespace ModalityInference

theorem freshFold_bounds {α : Type} (index : α → Nat) (xs : List α) (start : Nat) :
    start ≤ xs.foldl (fun n v => max n (index v + 1)) start ∧
      ∀ v ∈ xs, index v < xs.foldl (fun n v => max n (index v + 1)) start := by
  induction xs generalizing start
  case cons head tail ih =>
    have hs := ih (max start (index head + 1))
    simpa only [List.foldl_cons, List.forall_mem_cons] using
      And.intro ((Nat.le_max_left _ _).trans hs.1)
        (And.intro ((Nat.lt_succ_self _).trans_le ((Nat.le_max_right _ _).trans hs.1)) hs.2)
  case nil => simp

theorem Bounds.lt_freshTypeIndex {Δ : Bounds} {v : TypeVar} (h : v ∈ Δ.typeVariables) :
    v.index < Δ.freshTypeIndex := (freshFold_bounds TypeVar.index Δ.typeVariables 0).2 v h

theorem Bounds.lt_freshModeIndex {Δ : Bounds} {v : ModVar} (h : v ∈ Δ.modeVariables) :
    v.index < Δ.freshModeIndex := (freshFold_bounds ModVar.index Δ.modeVariables 0).2 v h

theorem Scheme.lt_freshTypeIndex {s : Scheme} {v : TypeVar}
    (h : v ∈ s.body.typeVars ∪ s.bounds.typeVars) : v.index < s.freshTypeIndex := by
  apply (freshFold_bounds TypeVar.index _ 0).2 v
  simp only [List.mem_append, TypeExpr.mem_typeVariables, Bounds.mem_typeVariables]
  exact (Finset.mem_union.mp h).elim (fun h => Or.inl (Or.inr h)) Or.inr

theorem Scheme.lt_freshModeIndex {s : Scheme} {v : ModVar}
    (h : v ∈ s.body.modVars ∪ s.bounds.modVars) : v.index < s.freshModeIndex := by
  apply (freshFold_bounds ModVar.index _ 0).2 v
  simp only [List.mem_append, TypeExpr.mem_modeVariables, Bounds.mem_modeVariables]
  exact (Finset.mem_union.mp h).elim (fun h => Or.inl (Or.inr h)) Or.inr

theorem Scheme.modeParam_lt_freshModeIndex {s : Scheme} {n : Nat} (h : n ∈ s.modParams) :
    n < s.freshModeIndex := by
  apply (freshFold_bounds ModVar.index _ 0).2 (.flex n)
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem h))

theorem Scheme.subsumptionIndices_type_fresh {Δ : Bounds} (s t : Scheme)
    {v : TypeVar} (h : v ∈ Δ.typeVariables) :
    v.index < (s.subsumptionIndices Δ t).1 :=
  (Bounds.lt_freshTypeIndex h).trans_le (Nat.le_max_right _ _)

theorem Scheme.subsumptionIndices_mode_fresh {Δ : Bounds} (s t : Scheme)
    {v : ModVar} (h : v ∈ Δ.modeVariables) :
    v.index < (s.subsumptionIndices Δ t).2 :=
  (Bounds.lt_freshModeIndex h).trans_le (Nat.le_max_right _ _)

theorem Scheme.subsumption_type_skolem_fresh (Δ : Bounds) (s t : Scheme) (i : Nat) :
    TypeVar.rigid ((s.subsumptionIndices Δ t).1 + i) ∉ Δ.typeVariables :=
  fun h => (Nat.not_lt.mpr (Nat.le_add_right _ _)) (s.subsumptionIndices_type_fresh t h)

theorem Scheme.subsumption_mode_skolem_fresh (Δ : Bounds) (s t : Scheme) (i : Nat) :
    ModVar.rigid ((s.subsumptionIndices Δ t).2 + i) ∉ Δ.modeVariables :=
  fun h => (Nat.not_lt.mpr (Nat.le_add_right _ _)) (s.subsumptionIndices_mode_fresh t h)

@[simp] theorem Scheme.subsumptionIndices_empty (s t : Scheme) :
    s.subsumptionIndices [] t =
      (max s.freshTypeIndex t.freshTypeIndex, max s.freshModeIndex t.freshModeIndex) := by
  simp [Scheme.subsumptionIndices, Bounds.freshTypeIndex, Bounds.freshModeIndex,
    Bounds.typeVariables, Bounds.modeVariables]

namespace SubsumptionScope

def source : Scheme := .mono .unit
def target : Scheme := {typeParams := [0], body := .var (.flex 0)}
def bounds : Bounds := [.sub .unit (.var (.rigid 1))]
def ambient : GroundAssignment :=
  ⟨fun _ => .unit Mode.identity, fun _ => Mode.identity⟩

/-- The original comparison reused the rigid identifier already in `bounds`. -/
def FormerSubsumes (Δ : Bounds) (s t : Scheme) : Prop :=
  let nt := max s.freshTypeIndex t.freshTypeIndex
  let nm := max s.freshModeIndex t.freshModeIndex
  let (assumptions, type) := t.instantiate nt nm true
  ∃ σ, Instantiates s σ ∧ EntailsAll (Δ ++ assumptions) (σ.bounds s.bounds) ∧
    Subtype (Δ ++ assumptions) (σ.ty s.body) type

theorem former_comparison : FormerSubsumes bounds source target := by
  refine ⟨{}, ?_, ?_, ?_⟩
  all_goals simp [Instantiates, source, target, Scheme.mono, EntailsAll,
    Substitution.bounds, Scheme.freshSubstitution, Scheme.freshTypeIndex,
    Scheme.freshModeIndex, TypeExpr.typeVariables, TypeExpr.modeVariables,
    Bounds.typeVariables, Bounds.modeVariables, Substitution.ty, TypeExpr.subst,
    Substitution.type]
  exact .bound (by simp [bounds, TypeVar.index])

theorem ambient_models : GroundModels ambient bounds := by
  simp [GroundModels, bounds, GroundSatisfies, TypeExpr.realize, ambient]
  exact .refl

theorem source_interpreted (w : World) : SchemeInterpretation ambient w source .unit := by
  exact fun _ _ _ ht => (Option.some.inj ht) ▸ ⟨(fun _ h => nomatch h), trivial⟩

def creditInstance : GroundAssignment :=
  {ambient with types := fun v => if v = .flex 0 then .credit Mode.identity else ambient.types v}

theorem credit_instantiates : GroundInstantiates ambient target creditInstance := by
  simp [GroundInstantiates, target, creditInstance, GroundModels]
  exact fun _ h he => (h he).elim

theorem target_not_interpreted (w : World) : ¬ SchemeInterpretation ambient w target .unit :=
  fun h => (h creditInstance (.credit Mode.identity) credit_instantiates rfl).2

/-- This is a shape error, independent of capture metadata or ownership. -/
theorem former_weakening_unsound (w : World) :
    GroundModels ambient bounds ∧ FormerSubsumes bounds source target ∧
      SchemeInterpretation ambient w source .unit ∧
      ¬ SchemeInterpretation ambient w target .unit :=
  ⟨ambient_models, former_comparison, source_interpreted w, target_not_interpreted w⟩

def refutingAssignment : GroundAssignment :=
  {ambient with types := fun v => if v = .rigid 2 then .credit Mode.identity else ambient.types v}

theorem refuting_models : GroundModels refutingAssignment bounds :=
  fun _ hc => (List.mem_singleton.mp hc) ▸ ⟨_, _, rfl, rfl, .refl⟩

theorem new_skolem_cannot_be_unit : ¬ Subtype bounds .unit (.var (.rigid 2)) :=
  fun h => (h.semantic (ρ := refutingAssignment) (w := ⟨∅⟩) (v := .unit)
    (ambient := Mode.identity) refuting_models rfl rfl
    ⟨(fun _ hr => nomatch hr), trivial⟩).1.2

theorem corrected_comparison_rejects : ¬ Subsumes bounds source target := by
  rintro ⟨⟨ts, ms⟩, hσ, _, h⟩
  simp [Instantiates, source, Scheme.mono] at hσ
  rcases hσ with ⟨rfl, rfl⟩
  exact new_skolem_cannot_be_unit h

end ModalityInference.SubsumptionScope
