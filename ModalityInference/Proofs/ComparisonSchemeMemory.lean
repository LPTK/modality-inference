import ModalityInference.Proofs.ComparisonDefinedInstances
import ModalityInference.Proofs.ComparisonObserverMachine
import ModalityInference.Proofs.Normalization
import ModalityInference.ComparisonObserverBoundary
import ModalityInference.Proofs.ComparisonDefiniteTreeMachines

/-! A scheme comparison whose shared images require auxiliary observer memory.
The source and target are join-free and have no modality guards. Every solution,
including arbitrary admissible internal lattice images, fails to make the pair
of image observations a transition congruence. This rules out compressing a
realizing machine to its output tuple; it does not rule out an input-only bound
on a machine with auxiliary states. -/
namespace ModalityInference.ComparisonSchemeMemory

open ComparisonObserverMachine

def A : Ty := .var (.rigid 0)
def B : Ty := .var (.rigid 1)
def X : Ty := .var (.flex 0)
def Y : Ty := .var (.flex 1)
def test : Ty := .fn A A
def imageX : Ty := .fn test A
def imageY : Ty := .fn A imageX

def source : Scheme :=
  { typeParams := [0, 1],
    bounds := [.sub X Y, .sub X (.fn X A), .sub (.fn Y A) X,
      .sub Y (.fn A X), .sub (.fn A X) Y],
    body := .unit }

def target : Scheme :=
  { bounds := [.sub A B, .sub A (.fn B A), .sub test B], body := .unit }

def bounds : Bounds := target.bounds.assumptions

def action : Substitution := { types := [(0, imageX), (1, imageY)] }

theorem bounds_defined : bounds.TypeBoundsDefined := by
  simp [Bounds.TypeBoundsDefined, bounds, target, Bounds.assumptions, Constraint.assumptions,
    A, B, test, TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels,
    or_imp, and_imp, forall_and]

theorem no_finite_shape_model : ¬∃ρ, ComparisonShape.Models bounds ρ := by
  rintro ⟨ρ, hρ⟩
  have h := hρ (.var (.rigid 0), .fn (.var (.rigid 1)) (.var (.rigid 0))) (by decide)
  have hs := congrArg sizeOf h
  simp only [ComparisonShape.subst, ComparisonShape.fn.sizeOf_spec] at hs
  omega

/-- The two coordinates are the observations of the same two type images. -/
abbrev Output := Bool × Bool

/-- The exact local relation imposed by the five source bounds when `A` is
false. A left function branch reverses the child observation. -/
def Relation (left : Bool) (parent child : Output) : Prop :=
  parent.1 ≤ parent.2 ∧
  parent.1 ≤ (if left then !child.1 else false) ∧
  (if left then !child.2 else false) ≤ parent.1 ∧
  parent.2 = (if left then true else child.1)

private theorem forced_outputs :
    ∀ c u v : Output, Relation true c c → Relation false u v → Relation true v u →
      c = (false, true) ∧ u = (false, true) ∧ v = (true, true) := by
  unfold Relation
  decide

def nodes {State : Type} (left : State → Bool) (next : State → State)
    (i : State) : Node State where
  atom v := decide (v = .rigid 1)
  unitValue := false
  creditValue := false
  action _ x := x
  branch _ := ⟨left i, next i⟩
  range _ := true

theorem nodes_certified {State : Type} (left : State → Bool) (next : State → State) :
    Certified bounds (nodes left next) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor <;> simp [nodes, Monotone]
  · constructor <;> simp [nodes]
  · constructor <;> simp [nodes]
  · simp [BoundsHold, bounds, target, Bounds.assumptions, Constraint.assumptions,
      A, B, test, TypeExpr.wellFormedBounds, or_imp, and_imp, forall_and,
      CompareTy.ofTy, value, nodes]

def outputs {State : Type} (left : State → Bool) (next : State → State)
    (σ : CompareSubstitution) (i : State) : Output :=
  (value (nodes left next) (σ.type (.flex 0)) i,
   value (nodes left next) (σ.type (.flex 1)) i)

/-- Actual source bounds imply precisely the counterexample's local relation
in every member of this sound observer family. -/
theorem action_relation {State : Type} (left : State → Bool) (next : State → State)
    (σ : CompareSubstitution) (h : AlgebraEntailsAll bounds (σ.bounds source.bounds))
    (i : State) :
    Relation (left i) (outputs left next σ i) (outputs left next σ (next i)) := by
  simp only [AlgebraEntailsAll, source, CompareSubstitution.bounds, List.map_cons,
    List.map_nil, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, CompareSubstitution.constraint, CompareSubstitution.ty, X, Y, A,
    CompareTy.ofTy, CompareTy.subst, CompareSubstitution.type] at h
  have hv {a b} (hab : AlgebraEntails bounds (.sub a b)) :
      value (nodes left next) a i ≤ value (nodes left next) b i :=
    subtype_mono (nodes_certified left next).modal (nodes_certified left next).range
      (nodes_certified left next).coherent (nodes_certified left next).bounds
      bounds_defined hab.2.1 hab.2.2 hab.1 i
  have hvals := And.intro (hv h.1) (And.intro (hv h.2.1)
    (And.intro (hv h.2.2.1) (le_antisymm (hv h.2.2.2.1) (hv h.2.2.2.2))))
  simpa [Relation, outputs, value, nodes, CompareSubstitution.type] using hvals

inductive State where
  | steady | even | odd

def left : State → Bool
  | .steady | .odd => true
  | .even => false

def next : State → State
  | .steady => .steady
  | .even => .odd
  | .odd => .even

/-- All declared-bound subterms and the fixed body are available at the root.
The remaining non-successor node data are constant, apart from `left`. -/
def label (i : State) : Bool × List Bool :=
  (left i, (ComparisonObserverBoundary.boundary bounds [.unit]).map
    (fun a => value (nodes left next) a i))

theorem label_eq : label .steady = label .odd := rfl

theorem action_outputs (σ : CompareSubstitution)
    (h : AlgebraEntailsAll bounds (σ.bounds source.bounds)) :
    outputs left next σ .steady = (false, true) ∧
    outputs left next σ .even = (false, true) ∧
    outputs left next σ .odd = (true, true) :=
  forced_outputs _ _ _ (action_relation left next σ h .steady)
    (action_relation left next σ h .even) (action_relation left next σ h .odd)

/-- Even with the original declared-bound subterm observations in the input,
no solution's output tuples form a transition congruence. The two equal child
tuples require different parents under the same input label. This includes all
admissible lattice witnesses, not just the explicit join-free witness below. -/
theorem no_output_transition (σ : CompareSubstitution)
    (h : AlgebraEntailsAll bounds (σ.bounds source.bounds)) :
    ¬∃ step : (Bool × List Bool) → Output → Output, ∀ i,
      outputs left next σ i = step (label i) (outputs left next σ (next i)) := by
  rintro ⟨step, hstep⟩
  obtain ⟨hc, hu, hv⟩ := action_outputs σ h
  have he := (hstep .steady).trans
    (show step (label .steady) (outputs left next σ (next .steady)) =
      outputs left next σ .odd by
        simpa only [label_eq, next, hc, hu] using (hstep .odd).symm)
  simp only [hc, hv, Prod.mk.injEq, Bool.false_eq_true, false_and] at he

private theorem image_order :
    Subtype bounds imageX test ∧ Subtype bounds test imageY := by
  have h : Subtype bounds A (.fn B A) := .bound (by decide)
  exact ⟨Subtype.fn_congr (h.trans (.fn_congr (.bound (by decide)) .refl)) .refl,
    Subtype.fn_congr .refl (h.trans (.fn_congr (.bound (by decide)) .refl))⟩

theorem action_bounds : EntailsAll bounds (action.bounds source.bounds) := by
  change EntailsAll bounds
    [.sub imageX imageY, .sub imageX (.fn imageX A), .sub (.fn imageY A) imageX,
     .sub imageY imageY, .sub imageY imageY]
  simp only [EntailsAll, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Entails]
  refine ⟨⟨image_order.1.trans image_order.2, ?_, ?_⟩,
    ⟨Subtype.fn_congr image_order.1 .refl, ?_, ?_⟩,
    ⟨Subtype.fn_congr image_order.2 .refl, ?_, ?_⟩,
    ⟨.refl, ?_, ?_⟩, .refl, ?_, ?_⟩
  all_goals simp [imageX, imageY, test, A, TypeExpr.DefinedUnder,
    TypeExpr.wellFormedBounds, ModeModels]

theorem instance_defined :
    CompareInstantiatesUnder bounds source (.ofSubstitution action) := by
  refine ⟨⟨List.Perm.refl _, List.Perm.refl _⟩, ?_, ?_⟩
  · apply CompareSubstitution.wellFormedUnder_of_images
    all_goals simp [CompareSubstitution.ofSubstitution, action, imageX, imageY, test, A,
      CompareTy.ofTy, CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels]
  · simp [source, CompareSubstitution.ty, CompareTy.ofTy, CompareTy.subst,
      CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels]

/-- The counterexample is an admissible comparison of actual public schemes,
with exact domains and defined images and body under the original bounds. -/
theorem algebra_subsumes : AlgebraSubsumesUnder [] source target := by
  refine ⟨.ofSubstitution action, instance_defined.domain,
    CompareSubstitution.wellShaped_ofSubstitution _ _, instance_defined.images,
    instance_defined.body, ?_, ?_⟩
  · simpa only [CompareSubstitution.ofSubstitution_bounds] using
      action_bounds.to_shaped.to_algebra
  · exact .shaped (.refl (CompareTy.wellShaped_ofTy .unit _))

/-- On a branch word `a b c ...`, the concrete witness returns
`(a ∧ ¬b, a ∨ (b ∧ ¬c))`, the three-level counterexample. -/
theorem witness_observations {State : Type} (left : State → Bool) (next : State → State)
    (i : State) :
    outputs left next (.ofSubstitution action) i =
      (left i && !(left (next i)),
       left i || (left (next i) && !(left (next (next i))))) := by
  simp [outputs, CompareSubstitution.ofSubstitution, CompareSubstitution.type,
    action, List.lookup_cons, imageX, imageY, test, A, CompareTy.ofTy, value, nodes]

/-- Retain the observation of the fixed input subterm `A → A` in addition to
the two output bits. This extra bit repairs this example's failed quotient. -/
abbrev Memory := Bool × Bool × Bool

def advance (a : Bool) (child : Memory) : Memory :=
  (a, a && !child.1, a || child.2.1)

def memory {State : Type} (left : State → Bool) (next : State → State)
    (i : State) : Memory :=
  (value (nodes left next) (.ofTy test) i,
   value (nodes left next) (.ofTy imageX) i,
   value (nodes left next) (.ofTy imageY) i)

theorem memory_transition {State : Type} (left : State → Bool) (next : State → State)
    (i : State) :
    memory left next i = advance (left i) (memory left next (next i)) := by
  simp [memory, advance, test, imageX, imageY, A, CompareTy.ofTy, value, nodes]

/-- The augmented machine forgets every frontier after three steps. This is a
construction for the example, not a bound for arbitrary comparison inputs. -/
theorem memory_forgets :
    ComparisonDefiniteTreeMachines.Forgets
      (fun a (child : Unit → Memory) => advance a (child ())) 3 := by
  intro x u v
  rfl

end ModalityInference.ComparisonSchemeMemory
