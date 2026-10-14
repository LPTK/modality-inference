# First-class modalities: Lean specification and prototype

This library covers the corrected core calculus in Sections 3–5 of *First-Class
Modalities in OxCaml*, including the POPL response's **closed-RHS restriction on
polymorphic `def`**. It contains independent declarative judgments, concrete
semantic definitions, executable algorithms, and constructor-based examples.

**Semantic soundness is proved for the whole corrected core.**
`Typing.resource_semantic` in `Proofs/ResourceSoundness` covers every typing
constructor. A typed term in an interpreted, separated environment evaluates
under every compatible supply to a live result with ownership drawn from the
input reserves or fresh allocation. `Proofs/Soundness` now proves
`semantic_soundness`, `termination_no_stuck`, `live_result`, and `ownership_bound`
without admissions. Small fuel budgets may exhaust; no budget rejects a typed
term satisfying those premises. `Typing.resource_closed` additionally gives
a closed program's ground result, evaluation, interpretation, and fresh-only
ownership without assuming an interpreted value or an already realized type.

**The semantic-soundness milestone is complete.** `Proofs/Soundness` is a standalone
entry point: its complete local import closure contains **51 modules and zero
admissions**. The dedicated semantic audit checks 21 fundamental, structural-semantic
and evaluator results transitively, allowing only `propext`, `Classical.choice`
and `Quot.sound`. CI builds and audits this target independently. The historical
`Deferred` namespace on the exported corollaries remains only for name compatibility.

**Inference verification is in progress.** Six direct admissions remain for solver
termination/completeness, generation soundness/completeness, and elaborated
inference soundness/completeness. Closed-definition generalization is now derived
from generation soundness; it still transitively depends on that admission.
`Proofs/Obligations` preserves closed-term substitution, abstract solver
correspondence, principal factorization, and both scheme-subsumption checker
contracts as **unproved proposition definitions**, with no admissions. Principality
remains required for the paper's stronger completeness-and-principality claim;
eventual inference success alone is insufficient. The other contracts remain
available as supporting or separate verification tasks. Their established
prerequisites and counterexamples remain available. Neither the semantic
entry point nor its dependencies import those worklists. The public library and
executables also remain independent of them. The original generic solver is
unchanged. The full-project audit continues to check
1098 public or established declarations transitively, including the complete
fundamental theorem, all three soundness corollaries, executable solver soundness,
and executable generator correspondence.

## Corrected semantics and proof

The former annotation-dependent fundamental assertion is false and remains
recorded as the proposition `Deferred.SemanticSoundness`.
`Proofs/PolymorphicCapture.no_unrestricted_soundness` is the checked counterexample:
a scheme instance changes a closure's result type while its old symbolic capture
annotations remain interpreted under a different ambient assignment.

`ResourceSemantics` repairs that defect by attaching erasable ownership evidence
to **each ground instance**. A credit owns its location exactly when unique.
Products retain full field types and separation between the cell and both fields.
A closure owns only actual capture references, has no ownership when reusable,
and accounts for every call result using captured, argument, or fresh resources.
Each scheme binding reserves enough resources for every admissible instance;
lookup chooses the evidence for the selected instance within that common reserve.
The interpretation does not read authoritative ownership from old annotations.
`Proofs/ResourceCapture` checks the original captured-credit witness against this
contract without changing its runtime value.

The repair changes no term constructor or evaluation rule. Annotation erasure
preserves evaluation, references, and the same resource evidence. The fundamental
proof strengthens the induction to the bindings actually read, while the ordinary
theorem accepts a full interpreted environment. Used bindings are proved to have
an admissible ground instance; unused schemes need not be inhabited.

The proved ingredients include:

- Semantic subtyping and scheme/context subsumption, preserving resource subsets;
  fresh target skolems preserve ambient bounds and source free identifiers.
- Context joins, polymorphic sharing, and symbolic locks, preserving separation;
  reusable captures admit empty reserves across every instance.
- Trimmed closure construction and application in every live calling world,
  with separate supplies for function evaluation, argument evaluation, and call.
- Heap/stack allocation, fresh-cell exclusion, and three-component credit reuse.
- Both sum eliminations and split's three bindings, with their original usage routing.
- Region entry into a fresh frame and exit using globality of **all references**,
  including aliased ones.
- Closed `def`: consistency supplies one RHS evaluation, and determinism makes
  that same value satisfy every generalized ground instance in one fresh reserve.

These results are in `Proofs/ResourceSubtyping`, `ResourceSubsumption`,
`ResourceContexts`, `ResourceClosure`, `ResourceApplication`, `ResourceProducts`,
`ResourceReuse`, `ResourceRegions`, `ResourceEliminations`, and `ResourceDefinitions`.
The full induction uses these proved steps without assuming its own conclusion.
The separate algorithmic generalization theorem is still open.

## Proved local constraint rewriting

`Proofs/GroundOrder` characterizes ground declarative subtyping by constructor,
including inherited field modes, function variance and future comparison, and
credit affinity. Both directions are proved using the original declarative rules.
For products and sums with different outer modes `m ≤ n`, the composed mode
`m ∘ n` mediates the common-mode rule; no new subtyping rule is assumed.

`ConstraintReduction.groundModels` and the preserved `Deferred.rewrite_sound`
prove exact equivalence of ground solutions for every local reduction: structural
decomposition, joins, meets, both guarded residual adjunctions, closure, and
reduction inside a larger constraint list. This removes one algorithmic admission.
`Proofs/TypeElimination` also proves the complete equality-elimination step,
including prior substitution images, definedness guards, and preservation of
every observed solution modulo mutual ground subtyping. `GroundEquivalence`
proves congruence for realized types and constraint models; `ConstraintModels`
connects declarative entailment equivalence with ground solution equivalence.
`Proofs/ShapeExpansion` constructs every ground shape using only fresh auxiliary
identifiers. `RewriteScope` proves that the old configuration support covers
substitution images and observations. Together, these prove the complete
`rewrite_solution_preservation` theorem for every abstract rewrite constructor:
equivalence, discharge, reduction, recording, hypotheses, both expansions,
substitution, propagation, and permutation. Every original observed solution is
preserved, with fresh auxiliaries hidden existentially. Executable correspondence,
termination, and the solver/inference results remain separate obligations.

`Proofs/Normalization` proves that executable modality normalization preserves
partial evaluation exactly, and type normalization preserves ground realization.
It also proves mutual declarative subtyping for every defined type, preservation
of each constraint's declarative entailment, and simulation of pending-list
normalization by the existing `Rewrites.equivalence` rule. Undefined residuals
remain undefined. This discharges normalization as a prerequisite of executable
correspondence; the complete correspondence theorem remains open.

`Proofs/ReductionEntailment` proves backward declarative entailment for every
local reduction, including reductions within larger lists and partial residuals.
The common composed mode derives product and sum decomposition using the existing
subtyping rules. `Proofs/SolverLocalSoundness` connects this result to executable
`stepType` and `stepMode`: entailment of a successful step's pending constraints
and retained bounds entails its original input. Outer-modality flattening and
normalization preserve realization, definedness and mutual subtyping. The proof
also covers alternative residual orientations, concrete checks and retained
bounds. `Proofs/SolverSoundness` lifts these results through the complete worklist
using the cache and substitution invariants described below.

`Proofs/SolverSubstitution` proves acyclicity for every successful worklist
transition and run, including updates to all prior substitution images.
`SubstitutionSupport` proves the required absence of eliminated keys, and type
normalization preserves type-variable support. `Proofs/SolverResidual` proves
preservation of the residual grammar. Consequently, successful `solve` and
`solveFrom` calls return an acyclic substitution and residual-form bounds. These
two conjuncts of `solve_sound` are proved independently; `SolverSoundness` now
proves its solution-entailment conjunct as well. Completeness and principality
remain open. Residual consistency is
proved below, including its finite closed-instantiation contract.

`Proofs/ModeSearch` proves that successful Boolean search returns an assignment
satisfying a selected frontier problem and preserves assignments outside that
problem's atoms. Projection then proves that the actual witness returned by
`satisfiableModes`, `solveFrom`, and `solve` models the residual modality
constraints. `Proofs/ModeSearchComplete` now proves Boolean search termination
with an explicit frontier bound and shows that rejected frontiers contain no
satisfiable problem. Assigning an occurring atom strictly decreases the number
of distinct atoms; summing `3 ^ atomCount` over the frontier pays for both branches.
CNF normalization eventually returns the same clauses at every larger budget,
including its finite clause-product check. Consequently, modality consistency
search terminates and succeeds for every satisfiable modality-bound set with
sufficient fuel, for flexible and rigid identifiers alike. Full worklist
correctness remains open.

`Proofs/SolverDefinedness` proves that modalities written in every returned type
bound are defined under every model of the residual modality constraints. The
worklist invariant separates pending definedness obligations from already visited
guards, whose truth follows from retained bounds. It covers duplicate discharge,
normalization, shape expansion, and equality elimination's reset of bounds and
visited constraints. `Proofs/ResidualModels` assigns every residual type variable
unit at the absorbing mode. Once the written modalities are defined, all residual
type bounds become reflexive. Thus `solve_ground_model` and
`solveFrom_ground_model` prove a model of **all returned residual constraints**,
using the actual returned modality witness. This does not establish entailment
of the original input.

`Proofs/FlexibleSupport` and `Proofs/SolverFlexible` prove that flexible inputs
stay flexible through substitution, normalization, fresh shape expansion, bound
propagation, equality elimination, and every worklist run. `Proofs/GroundReification`
constructs a finite closed substitution for any ground model of flexible bounds.
Closed realized types are mutually declarative subtypes of their reifications;
this transports the ground model to entailment of the substituted constraints.
Together these prove the original `Deferred.solve_consistency` statement with
its full `BoundsSatisfiable` conclusion. Rigid identifiers are never replaced.

`Proofs/ModeOrientation` proves a well-founded rank decreases for every new
modality or definedness obligation emitted by `stepMode`, including after
normalization. The rank compares total syntax size, whether the least flexible
variable is shared by both sides, and the size of the side with the smaller
minimum. All residual, composition, closure, join and meet branches are covered,
including permitted ties and absent flexible variables. Normalization preserves
variable support and the minimum and never increases syntax size. This excludes
cycles among modality descendants.

`Proofs/ModeSeen` uses that rank to prove the modality-cache invariant throughout
the complete executable worklist, including type expansion and equality
elimination. A visited modality or definedness constraint follows from retained
bounds and only strictly smaller normalized pending modality obligations.
`ModeInvariant.duplicate_entails` therefore justifies removing a duplicate without
letting it justify itself. On successful completion, `runSolver_seen_entails`
reconstructs every modality/definedness constraint still in the visited cache
under any ambient context entailing the returned bounds. `TypeSeen` extends cache
soundness to type constraints below; `SolverSoundness` reconstructs full input entailment.

`Proofs/BoundedSupport` and `Proofs/SolverFresh` prove that allocation counters
bound every identifier in pending constraints, retained bounds, visited entries,
and accumulated substitutions throughout complete solver runs. The actual
initial counters chosen by `solve` satisfy this invariant. Executable skeletons
meet the abstract `FreshFor` premise, and normalized flexible heads lie outside
the saved substitution's domain. The fresh skeleton is fixed by that substitution;
its equality cannot match an old cache entry or trigger the occurs check.
`Fresh.skeleton_eliminated` proves the exact following transition, which eliminates
that equality and clears the cache before reprocessing the original constraint.
These facts justify the intermediate expansion state in the type-cache invariant.

`Proofs/TypeOrientation` counts nonmodal type constructors and distinguishes
equality/equivalence from subtyping at the same structural size. Normalization
preserves this rank. Every successful type step either adds strictly smaller
obligations or enters an expansion state whose head cannot be skipped and whose
next successful transition clears the cache. The result applies to actual
normalized worklist heads using the proved freshness and acyclicity invariants.

`Proofs/SolverUnbound` proves that pending constraints, retained bounds, and
visited entries contain no type identifier already eliminated by the saved
substitution. Fresh expansion preserves this property; equality elimination
removes the new identifier without reintroducing earlier ones. Together with
the empty modality substitution, this makes all three lists fixed by the saved
substitution throughout complete runs. `solve_bounds_fixed` proves the same for
the bounds returned by `solve`.

`Proofs/TypeSeen` proves the complete type-cache invariant using these results.
A visited type constraint follows from retained bounds and pending constraints of
strictly smaller structural rank. Modality obligations have rank zero and use the
existing modality-cache proof. Expansion may temporarily leave this invariant,
but its next head cannot be skipped and its next successful step clears the cache.
Every solver transition and complete run preserves this disjunction.
`TypeReady.duplicate_entails` justifies duplicate discharge for every constraint
kind. `runSolver_all_seen_entails` reconstructs every constraint still cached after
a successful run from a fresh state with empty substitution and cache, under any
context entailing the returned bounds. The backward proof below also recovers
input constraints cleared from the cache by equality elimination.

`Proofs/EntailmentTransport` proves context transport and transport through the
solver's type-only substitutions. Definedness after substitution is characterized
exactly by the original written guards and the images of variables occurring in
the type. The existing `Constraint.assumptions` construction supplies a context
of subtype assumptions and explicit guards that entails the original constraints.
Using it, `Entails.consequence_substitute_types` transports any consequence valid
under every ambient context, provided the conclusion's inserted type images are
defined. Entailment of substituted constraints supplies definedness for their
own images; equivalences preserving type-variable support therefore transport
without an extra premise.

`Proofs/SolverTransport` applies this result to duplicate discharge, local type
and modality steps, the final cache, and normalization. It also proves that a
single occurs-free type substitution satisfies the equality it eliminates when
its image is defined. `SolverImages` supplies image definedness for actual results.

`Proofs/SolverStepEntailment` proves backward entailment of the entire pending and
retained constraint list for every step preserving the saved substitution,
including duplicate discharge. It also identifies the exact equality-elimination
case when that substitution changes. `Proofs/SolverImages` uses these results and
entailment transport to prove that all accumulated type images are defined under
any context entailing the remaining constraints, through every step and complete
run. Equality elimination's queued guards establish the new image's definedness;
transport handles its insertion into all earlier images. Returned residual bounds
entail themselves, and `solve_images_defined` proves that every returned type
image is defined under those bounds. `solve_substitution_wellFormed` packages
this result with modality-image definedness as `Substitution.WellFormedUnder`.
Thus actual solver outputs satisfy the inference theorems' substitution premise.

`Proofs/SolverExtension` proves that later substitutions preserve every earlier
eliminated equation: the final substitution acts identically on an original
variable and its saved image. This relation passes backward through every step
and complete run. It transports constraint entailment even when substitution
changes an equality into an equivalence.

`Proofs/SolverSoundness` combines this extension property with the cache, support,
freshness and image-definedness invariants to reconstruct every original input
constraint under the returned substitution and residual bounds.
`solveFrom_solution` requires bounded initial supplies; `solve_solution` requires
only successful execution. The original `Deferred.solve_sound` theorem is now
fully proved: solution entailment, residual grammar, and acyclicity. Abstract
rewrite correspondence, termination, completeness and principality remain open.

## Corrections and retained witnesses

`Proofs/ModePropagation` proves that the former transitive mode work could grow
forever. The flexible input `(μ / global) ≤ μ`, `μ ≤ μ ∘ many` has the finite
solution `μ = bottom`. Nevertheless, each six-step worklist round added another
outer `global` composition and regenerated a pending inequality. The archived
worklist, validated entry and complete solve are proved to exhaust **every** fuel
budget, refuting their termination and completeness obligations. This is an
unbounded proof, beyond the initial finite experiment.

`recordModeBound` now retains the bound directly for finite consistency checking.
`record_entails` proves equivalence with the former recorder's obligations under
every ambient context; `record_groundModels` proves equality of their ground
model sets. The discarded transitive work adds no information. The corrected
solver succeeds on the witness for every fuel budget at least 100. Regressions
compare all eight models in 64 constant-pair variants and check the reversed
input order. Full worklist termination and completeness still require proofs.

`Proofs/PrincipalAmbient` refutes the former unrestricted ambient principality
statement. Solving `(α × unit) ≤ (unit × unit)` gives `α` a modal-unit image.
Under an ambient assumption consisting of that whole-product inequality, the
identity substitution is a solution, but no `α ≤ unit @ m` follows. The witness
is flexible and finitely satisfiable; inconsistent assumptions are not the cause.
The former proposition is archived and its negation proved. The retained
`Obligations.PrincipalFactorization` statement requires `Residual Δ`, matching the paper's
grammar of variable-to-variable type bounds. Its equivalence-based conclusion
and the paper's ground principality claim are unchanged and remain unproved.

`Proofs/ModeCycle` records an unsatisfiable modality set formerly accepted by the
worklist. With `a = absorbing`, `b = μ ∘ bottom`, and `c = μ ∘ many`, the
constraints `a / b ≤ c` and `μ ≤ identity` have no model. The former `sub2`
orientation swapped `b` and `c` twice, then duplicate suppression discarded the
unresolved inequality. Its remaining definedness guards were satisfiable.
The archived executable is proved to succeed without satisfying `Solution`.
The corrected swap requires the denominator's least variable to be strictly
smaller than both other operands' minima; a tie retains the exact inequality for
finite projection. The corrected solver rejects this witness for every fuel
budget at least 100. Regressions compare all eight valuations in 1,024 related
single-variable cases, including both residual and composition entry forms.
This repairs a soundness counterexample; `SolverSoundness` proves the corrected
worklist's input solution contract.

`Proofs/ModalEquality` records a satisfiable flexible constraint formerly rejected
by the syntactic equality occurs check: `α = α @ bottom`. Assigning `α` unit at
the absorbing mode is a finite closed solution. The archived former policy is
proved never to succeed at any fuel budget. The corrected equality branch emits
the two subtype obligations when the variable occurs in its image; their exact
declarative equivalence and simulation by abstract rewriting are proved. The
corrected solver succeeds on the witness for every fuel budget at least 12.
Structural recursive types still fail the finite-shape precheck, and undefined
modalities still fail their retained guards. Regressions cover all eight concrete
modes, undefined modal equality and wrapped structural recursion. This removes
a counterexample to solver completeness; the general theorem remains open.

The worklist entry validates its accumulated substitution with
`Substitution.checkAcyclic`; `checkAcyclic_iff` proves that the executable check
matches `Substitution.Acyclic`, including distinct keys and normalized images.
The former entry checked only pending/residual type shapes. `SolverEntry`
records a supplied state with `α₀ ↦ α₀ → unit`: the former precheck succeeds and
the former entry exhausts twenty steps; the corrected entry rejects it at every
fuel budget. Empty-substitution behavior is proved unchanged for every fuel
budget, covering the entry states used by inference. These are finite checked
witnesses and an entry-invariant proof; full worklist termination remains open.

The entry also applies the accumulated substitution before checking shapes.
`Proofs/ShapeEntry` records the acyclic saved substitution `α₀ ↦ α₁ × unit`
with pending bounds `α₁ ≤ α₂`, `α₂ ≤ α₀`. The raw precheck succeeds, while
the substituted bounds have no finite ground model: ground subtyping preserves
constructor count, so `α₁` cannot have the same shape as `α₁ × unit`.
The archived former entry exhausts twenty steps; this bounded witness does not
claim all-fuel divergence. The corrected entry rejects for every fuel at least
two, and its behavior with an empty substitution is proved unchanged for every
budget. Regressions cover reversed bounds, splitting them between pending and
residual lists, and a valid nonempty saved substitution. Successful entry now
implies that the substituted shapes passed the precheck.


`GroundInstantiates` fixes every identifier outside the quantified domain,
including identifiers absent from a scheme. Sharing and locking require scheme
binders fresh for ambient bounds; locking also requires freshness for its symbolic
modality. `ContextScoping` checks that the former collision between an ambient
`aliased ≤ μ₀` and independently quantified `∀μ₀. credit@μ₀` allowed two owned
copies, and that alpha-renaming satisfies the corrected conditions.
`SubsumptionScope` records a separate target-skolem collision and proves the
corrected comparison fresh for ambient bounds as well as both schemes.

Typing checks definedness of introduced internal types and modalities.
`Typing.realize_defined` covers every rule, and the guards hold automatically
for ordinary source types. `UndefinedDomain` records the former non-function
application counterexample using `top / bottom` as an undefined function-domain
modality. `UndefinedBounds` records a second vacuous instance whose reflexive
bound had no ground model. Entailment now guards type operands, and equality
elimination retains the substituted type's well-formedness bounds. Both witnesses
are rejected by the corrected rules without narrowing the source language.

`PartialSubstitution` refutes unrestricted subtyping substitution for undefined
residual images. `Subtype.substitute` includes the necessary definedness premise;
`Subtype.substitute_ordinary` discharges it for ordinary modalities.
`Annotations` retains an independently proved alternative repair mechanism:
binder-aware transport and `SchemeValue.instantiate` preserve runtime structure,
references, liveness, and instantiation guards. The nested `ScopedCaptures`
witness records why uniform annotation substitution is insufficient. Those
operations are not required by the proved resource semantics and are not inserted
into `infer` or `evalFuel`.

Inference solutions require `Substitution.WellFormedUnder`: all type and modality
images must be defined under the resulting bounds. Partial internal expressions
are allowed when those bounds ensure definedness. Fresh lambda domains, closure
modes, and unused sum branches therefore need no extra constraints. The executable
generator and independent `Generates` relation both follow this convention.
Lookup validates only modalities already written in the instantiated scheme;
this check matters because Lean's raw input syntax also admits partial expressions.
`GenerationDefinedness` records the former acceptance of an undefined input scheme
and a separate raw substitution with an undefined lambda-domain image. The latter
violates the substitution hypothesis; it is not a source-calculus counterexample.
`Generates.definedUnder` proves result definedness for every constructor under
solution entailment and well-formed substitution images. These proofs use no
admissions. Full generation and inference soundness remain open.

`Proofs/GenerationExecution` proves that every successful `generate` result
erases to its original source term and retains the initial constraints as an
exact prefix, including order and multiplicity. Both inductions cover all term
constructors, including nested closed definitions. `infer_erases` additionally
accounts for the final substitution of capture annotations, discharging the
erasure conjunct of `inference_sound`. Its typing conjunct remains deferred.
`Proofs/GenerationCorrespondence` now proves the full independent `Generates`
derivation, with output constraints equal up to permutation to the initial
constraints followed by those generated. The proof covers every constructor,
including fresh instantiation, lazy locks, context usage routing, and nested
closed definitions. `SolverCounters`, `GenerationInstantiation`,
`GenerationContexts`, and `GenerationSupplies` prove monotone allocation counters,
bounded identifiers, and flexible support. These establish solution entailment,
consistency, and well-formed substitution images for each closed RHS solve. The original
`generator_correspondence` statement is discharged without additional premises;
declarative generation soundness and the inference typing conjunct remain open.

`Proofs/GenerationScope` refutes the former unrestricted generation-soundness
contract. A lambda lock named `μ₀` can occur below a scheme binding that also
quantifies `μ₀`; lookup then instantiates the lock along with that quantifier.
The checked witness has well-formed substitution images and satisfies all generated
constraints but gives a reusable closure a captured unique credit as its result.
The proved resource semantics
rules out any declarative typing, even though the source context is well scoped.

`GenerationHygiene` records the missing scope condition: every lambda lock is
fresh for the quantifiers in the schemes below it, and recursive derivations obey
the same condition. `generate_correspondence_hygienic` proves this property when
those quantifiers lie below the allocation supply; `generate_initial_hygienic`
proves it for every context using the existing inference initializer. Closed
RHS generalization preserves the supply invariant. The executable algorithm and
source language are unchanged. Deferred generation soundness and closed-definition
generalization now require this scope evidence, and generation completeness must
produce it. Full declarative generation soundness is still open.

`Proofs/SchemeInstantiation` supplies the syntactic instance-transport step.
`Proofs/GeneralizationDefinedness` records the same missing substitution hypothesis
in the deferred closed-definition generalization contract. The hygienic derivation
for `λx. ()` has an identity solution with empty residual bounds. A later raw
substitution can assign its argument variable an undefined internal type, but such
a substitution fails `WellFormedUnder []`. `no_unguarded_generalization` refutes
the former statement without this hypothesis; `defined_instance_typable` proves
the example for every well-formed instance substitution. Ordinary source images
satisfy the hypothesis automatically. No fresh-variable constraint is needed;
the full generalization theorem remains deferred.

`Instantiates.substitute` constructs an instance of a capture-avoiding substituted
scheme whose body is exactly the outer substitution of the original instance.
Its bounds have equivalent entailment under every ambient context; raw constraint
syntax can differ when an equality becomes an equivalence. The proof covers
repeated quantified names and arbitrary internal modality images.
`Typing.var_substitute` derives the variable-typing case using the transported
instance, with result definedness explicit.

`Proofs/SchemeBounds` makes equality directions and written definedness guards
explicit in a scheme's bound assumptions. `Substitution.bounds_assumptions_entails`
proves that this preserves bound entailment under arbitrary substitutions, including
partial modality images; `Scheme.withAssumptions_instance` preserves precisely
the original instances. The original context weakens to the context with explicit
assumptions. Fresh skolem renaming commutes with the assumption construction.
The corrected comparison expands target assumptions itself, so `Subsumes.refl`
and `ContextLe.refl` now hold for every scheme and context.

`Proofs/GenerationContextTyping` builds declarative witnesses for symbolic context
operations. `UsageSplit.declarative_bindings` handles every split of a context
consisting of bindings, including sharing, and produces both the declarative join
and weakening from the source. `Context.lock_withAssumptions` similarly constructs
a whole-context lock. These results retain quantified freshness for ambient bounds
and, for locking, the lock mode. Transport through arbitrary solution substitutions,
enclosing symbolic locks, closed-definition generalization and typing of the actual
generated annotations remain necessary for full generation and inference soundness.

`Proofs/SchemeFreshening` supplies fresh contexts for those structural witnesses.
`Scheme.freshenedFor` renames binders beyond any supplied ambient bounds and makes
their assumptions explicit. It preserves exactly the same instance types under
every ambient context, and the original scheme subsumes the freshened scheme.
`Instantiates.unsubstitute_identity` provides the reverse instance transport;
mapping substitution images keeps exactly the original quantified domain, including
repeated names. A finite identity substitution raises the existing binder supply
without changing type or modality variables. Equality constraints can still change
syntax, so their preservation is stated as equivalent entailment.

`Context.freshenedFor_le` and `freshenedFor_fresh` lift these facts to contexts.
Including the lock mode among the avoided bounds gives `freshenedFor_lock` for
every context, ambient bound list and mode. Generation still needs transport
through enclosing symbolic locks and arbitrary solutions, and inference still
requires the actual generated capture annotations.

`Proofs/SubsumptionInstances` proves syntactic instance preservation for declarative
scheme subsumption. Given a target instance with entailed bounds and a defined
body, `Subsumes.instantiate` constructs a source instance with entailed bounds
whose body is a subtype of that target body. `SkolemSubstitution` transports
subtyping, submoding, entailment and definedness while fixing the ambient bounds.
`InstanceDefinedness` extracts defined images only for variables that occur in the
target body or bounds. Unused quantified images can be partial; reconstruction
replaces their skolems with defined defaults. The proof permits repeated parameter
names and retains the source witness's exact quantified domain. It requires no
self-entailment premise for the ambient bounds and does not assert that subtyping
preserves `DefinedUnder` under arbitrary raw bounds.

`Proofs/TypingAdmissibility` supplies that stronger result when each ambient
subtype assumption has defined operands. Successful solver residuals meet this
condition by the existing definedness invariant. Under it, subtyping preserves
`DefinedUnder` in both directions, every typing result is defined, and declarative
scheme subsumption preserves admissible syntactic instances. Every free binding
actually used by a typed term has such an instance, including through context
subsumption, sharing, locks and closed definitions. The same necessary condition
holds for every used scheme recorded in a typed lambda's capture annotation.
Unused bindings need no admissible instance. These theorems keep the ambient
definedness premise explicit and add no restriction to the declarative rules.

`Proofs/SharingLockCapture` now refutes the current emitted-annotation contract
of `inference_sound`. In the context `x : α`, inference succeeds on `λy. (x,x)`
with identity substitution. Its capture scheme requires the unaliased crossing
bound `α ≤ α @ future μ`, but the residual constraints contain the crossing bound
only after aliasing, together with `α ≤ α @ many`. `TypeVariablePredicates` gives
a syntactic subtyping invariant proving that the missing bound is not derivable.
The capture-admissibility theorem then rules out typing the emitted annotation
under any context and at any result type. This is a proved defect, not merely a
computed example or an unproved generation prerequisite.

`Proofs/CaptureRefinement` types a replacement annotation for the exact successful
inference result, with the same source context, residual bounds and inferred type.
The source capture scheme quantifies a fresh modality `p`, assumes `α ≤ α @ p`
and `α @ p ≤ (α @ p) @ future μ`, and captures `(α @ p) @ capture μ`.
The shared body selects `p = aliased`. Source subsumption, locking, the body join
and the complete lambda derivation are all proved. The executable still emits the
old annotation: integrating refinement into complete algorithmic contexts and
freshening relative to final residual bounds remain necessary before
`inference_sound` can hold.
No admission has been discharged by this counterexample or its positive witness.

`Scheme.refineMode` now defines the quantified weakening for arbitrary schemes.
`Proofs/ModalRefinement` proves source subsumption, exact instantiated body and
bound contracts, and retention of every defined original instance. Refinement
before a symbolic lock retains every unshared locked instance up to mutual
subtyping and every shared locked instance with exactly the same body type.
These results allow repeated original parameter names and arbitrary instance
images; the new parameter must be fresh for the scheme and lock mode.

The refined capture subsumes both the original prepared locked scheme and the
many-modified scheme used when joining two shared locked bindings. The latter
join is also proved, with quantified freshness for ambient bounds explicit.
`freshened_refineMode_lock` constructs a suitable refined lock for any scheme,
ambient bounds and lock mode by freshening the original binders and choosing the
new parameter above both supports. `Subsumes.of_instances` packages uniform
syntactic instance preservation as declarative scheme subsumption.
The commutation lemma `Subtype.modal_comm` now lives in `SchemeBounds`.

`Scheme.lockAll` resolves a list of symbolic locks, with the outermost lock first.
`Proofs/NestedLockRefinement` proves that one refinement at the binding, before
all locks, retains every shared instance through any finite list, with exactly
the same resulting type. It also retains every defined unshared instance up to
mutual subtyping. The generic `lockAll_transport` reconstructs all source crossing
bounds from mutually subtyped base bodies and equal substituted lock modes;
it assumes no cancellation of aliasing or captured modes. The refined capture
subsumes the many-modified prepared shared capture, and the latter supports a
declarative join. Unshared scheme subsumption requires a nonempty lock list,
whose crossing bounds supply body definedness. These statements retain the
explicit freshness premises on the refinement parameter and quantified names.
`RefinedSharing` additionally reconstructs instances of an already refined shared
branch, selecting `aliased` composed with that branch's refinement modality.
It preserves all enclosing crossing bounds and proves the corresponding scheme
comparison and join. `Substitution.dropMode` recovers the original exact quantified
domain and preserves the remaining variable images.

`RefinedContexts` resolves a whole algorithmic context by refining each binding
before its enclosing locks. `UsageSplit.declarative_refined` supplies a declarative
join and source weakening for arbitrary interleavings of locks and bindings.
Its explicit freshness invariant survives both branches of every split.
`Lookup.refinedContext_instance` retains every defined original lookup instance
at the same binding index, with entailed bounds and mutual body subtyping.
`RefinedLocks` now proves lambda locking for these complete contexts, variable
typing at every retained instance, source-context weakening, and the lambda
typing step with its exact refined capture annotation. Whole-term generation,
solution transport, and actual emitted annotations remain future work. Neither
`refineMode` nor `lockAll` is yet used by `captureContext` or `infer`, so the
recorded counterexample still describes the current executable.

Evaluator correspondence, determinism, fuel stability, Boolean CNF reduction,
and all-axis modality projection are also proved independently. Backend modality
entailment agrees with `ModeModels`; a positive inequality report establishes
`Submode`. An executable scheme-comparison report is still data pending the
remaining algorithmic proofs.

`GeneralizationTransport` proves that any defined instance of a fully generalized
scheme has defined images for every identifier its substitution can replace.
Its entailed bounds therefore transport all solved consequences through arbitrary
partial substitutions. `Solution.generalize_instance` composes the original solve
with that instance. The closed-definition-generalization theorem now follows
from `generation_sound`; this removes its separate admission, but does not make
the theorem admission-free until generation soundness is proved.

## Build and run

Build and audit the completed semantic milestone independently:

```sh
lake build ModalityInference.Proofs.Soundness
python3 scripts/audit_admissions.py --semantic
```

The semantic audit rejects any admission or escape hatch anywhere in the local
import closure and checks the selected results' complete Lean axiom dependencies.
It does not import or require the optional inference/solver proof worklists.

Use the existing pins; do not run `lake update` for this milestone:

```sh
elan toolchain install leanprover/lean4:v4.25.0-rc2
lake exe cache get
lake build
lake build ModalityInference.Examples ModalityInference.Regression ModalityInference.Proofs
python3 scripts/audit_admissions.py
```

Mathlib remains locked at `bd350e6b5fe8a1dd9a2729913b022f3b5761787a` in
`lake-manifest.json`. The pinned toolchain and dependency cache were restored and
the original solver was built before extending the development. CI builds the
regressions and optional proof statements and audits the admission boundary.
Warnings about the explicitly deferred theorems are expected.

Create a Lean file containing this example and run `lake env lean Example.lean`:

```lean
import ModalityInference
open ModalityInference

def idTerm : RawTerm := .lam () (.var 0)
def program : RawTerm := .defn idTerm
  (.pair (.app (.var 0) .unit)
         (.app (.var 0) (.pair .unit .unit)))

#eval (infer 5000 [] program).isSuccess  -- true
#eval do
  let result ← infer 5000 [] program
  evalFuel 100 {} [] result.elaborated

#eval solve 500 [
  .mode (.const Mode.bottom) (.var (.flex 0)),
  .mode (.var (.flex 0)) (.const Mode.identity)]

#eval (checkSubsumption 20000
  (.generalize [] (.fn (.var (.flex 0)) (.var (.flex 0))))
  (.mono (.fn .unit .unit))).isSuccess  -- true
```

Explicit scheme/value instantiation is also runnable:

```lean
import ModalityInference.Examples
open ModalityInference
#eval Examples.polymorphicCapturedCredit.instantiate [] [.const Mode.identity]
```

The result includes the instantiated type, transported closure, substitution and
residual obligations. Supplying an undefined residual still produces a definedness
obligation when its parameter does not occur in the body; solving those bounds
rejects the instance.

The API is in namespace `ModalityInference`:

| Function | Result on success |
| --- | --- |
| `infer fuel context term` | `Inferred`: scheme, annotated term, substitution, residual bounds, rewrite trace |
| `solve fuel constraints` | `Solved`: substitution, residual bounds, concrete consistency witness, fresh counters, trace |
| `checkSubsumption fuel inferred declared` | `SubsumptionEvidence`: structural substitution, preserved assumptions, obligations, flexible Boolean atoms, normalized query and backend report |
| `evalFuel fuel supplies environment term` | A `Value` |

All four return `RunResult`: `success`, `rejected diagnostic`, or `exhausted`.
Increase the fuel after exhaustion; it is **not evidence of rejection**. Fuel is a
prototype budget for recursive depth, worklist/search steps, and intermediate
normalization work. It is not a machine-instruction counter or a complexity bound.

## Representations and boundaries

- Modes have locality, affinity and uniqueness Boolean axes. The first two are
  covariant; the last is contravariant. `Modality` is the ordinary
  constant/variable/composition grammar. `PolarMod` and `PolarTy` distinguish
  positive and negative expressions. Internal `ModExpr` additionally represents
  joins, meets, partial residuals and deferred lock projections. Undefined
  residuals remain explicit well-formedness obligations.
- Term binders are de Bruijn indices. `split` puts the credit at index 0, the first
  field at 1 and the second at 2. `case`, `lam` and the body of `defn` bind one
  variable. A `defn` RHS is checked in an empty term context. Types and modalities
  have different identifier types, each distinguishing flexible variables and
  rigid skolems. Scoping, free variables, lifting, renaming, substitution,
  fresh instantiation and generalization are defined explicitly.
- Schemes retain residual bounds. `infer` does not commit its finite consistency
  witness to the result: doing so would discard polymorphism. At a closed `def`,
  the entire RHS is solved and checked before all remaining variables are
  generalized. At an open inference boundary, context-free variables are excluded
  from generalization. Sharing and locks on polymorphic bindings stay under their
  quantifiers and are freshened on each use.
- The solver uses pending constraints, residual bounds, substitutions, a visited
  set, fresh counters and a trace. It folds concrete expressions, checks finite
  constructor shapes (including
  indirect cycles), expands types, records bounds and applies guarded residual
  rewrites. Remaining symbolic projection obligations are retained, not dropped.
  Transitive modality consequences are checked through their retained premises;
  they are not re-enqueued as potentially growing expressions. Boolean CNF
  propagation checks consistency. This finite fallback is part
  of the executable prototype; it is not a claim of a polynomial solver.
- Declared schemes use the paper's residual variable-bound grammar. Subsumption
  freshens the inferred quantifiers and skolemizes **every** declared quantifier,
  including body-only ones. Rigid type bounds are retained, closed under concrete
  modal congruence and transitivity, and used in entailment. The prototype searches
  finite base-type representatives for residual flexible types and eliminates
  flexible mode atoms in Boolean queries. Completeness of that representative
  search and reconstruction of admissible modality witnesses are **deferred
  obligations**, not consequences of the existing solver theorem.
- `ModeBackend` keeps future and past comparisons in opposite directions. CNF
  clauses become `Equation Bool n` using an explicit sorted identifier list and
  checked `Fin n` lookup. The existing `Equation.decide` discharges those queries.
  Projection, normalization, and reduction correctness are proved.

## Evaluation, ownership and liveness

`Eval` is an independent environment-passing big-step judgment; `evalFuel` is its
executable counterpart. They cover unit, variables, closures, application,
products, sums, case, split, closed definitions, heap/stack allocation, reuse and
regions. Runtime capture selection uses syntax free variables, independently of
type annotations. Unused environment slots become unit so indices remain stable.

`Supplies` partitions infinite arithmetic progressions for heap cells, cells in
the current stack frame, and identities of future frames. `World` records live
frames separately. Soundness requires `World.Compatible`: positive strides, an
active current frame, fresh future frames and no collision with any input
reference. Evaluation itself is not a dynamic ownership or liveness checker.

`GroundTy` and `GroundInstantiates` define ground types and quantified assignments.
`ResourceInterpretation`, `ResourceSchemeInterpretation`,
`ResourceEnvironmentInterpretation`, and `ResourceSemanticEvaluation` are the
corrected concrete contracts used by whole-core soundness. `References` includes
aliased locations; separation uses owned resource sets while world validity uses
all references. The earlier `ValueInterpretation`, `Owns`, and associated scheme,
environment, and evaluation definitions are retained to state the historical
counterexample and their independently proved properties. `firstOrderSupport`
is executable on first-order values and does not guess an instance for closures.

The critical counterexample is a unique pair at heap cell 0 containing an aliased
credit for stack cell `(9,1)`. At the declared type its ownership support is only
`[heap 0]`, while its references still include `stack 9 1`. The former mode-only
support definition incorrectly resurrected ownership of the field. Empty field
support also does not make that stack reference valid after frame 9 dies.

## Module dependencies and paper coverage

All paths below are relative to `ModalityInference/`.

| Paper material | Modules | Status |
| --- | --- | --- |
| §3 syntax, three axes, polarized grammar and residuals | `Core/Mode`, `Core/Syntax`, `Core/Scoping` | Definitions and exhaustive finite regressions |
| §3 subtyping, schemes, weakening, joins, locks, all typing rules | `Declarative` | Independent inductive judgments |
| §3 allocation and environment semantics | `Evaluation` | Independent judgment plus runnable evaluator |
| §3 ground types, ownership, separation and liveness | `Semantics`, `ResourceSemantics` | Ground definitions and corrected instance-indexed resource interpretation; old annotation-dependent interpretation retained for its counterexample |
| §4 independent constraint-generation relation | `Generation` | Inductive rules, including closed `def` and `region` |
| §4 inference and elaboration | `Inference` | Executable prototype |
| Generation and elaboration invariants | `Proofs/GenerationExecution` | Proved source erasure for generation and inference, and exact-prefix preservation of accumulated constraints; typing remains deferred |
| Executable generator correspondence | `Proofs/GenerationCorrespondence` | Proved independent relational derivations for every constructor, including closed-definition solves, with constraints preserved up to permutation |
| Generation lock scope | `GenerationHygiene`, `Proofs/GenerationHygiene`, `Proofs/GenerationScope` | Refuted unrestricted generation soundness; proved lock hygiene for every initialized executable generation, including nested closed definitions |
| Generator allocation and support | `Proofs/SolverCounters`, `Proofs/GenerationInstantiation`, `Proofs/GenerationContexts`, `Proofs/GenerationSupplies` | Proved monotone counters and bounded/flexible support through fresh instantiation, lookup, splitting, locks, generation and closed-definition solves |
| Executable normalization | `Proofs/Normalization` | Proved preservation of partial evaluation, ground realization, definedness and declarative entailment; simulated by abstract rewriting |
| Local solver soundness | `Proofs/ReductionEntailment`, `Proofs/SolverLocalSoundness` | Proved backward declarative entailment of every local reduction and successful type/modality step, including outer normalization and alternative residual orientations |
| Executable solver output invariants | `Proofs/SubstitutionSupport`, `Proofs/SolverSubstitution`, `Proofs/SolverResidual` | Proved normalized acyclic substitution preservation and residual output grammar |
| §4 constraint rewriting | `Rewriting`, `Constraints` | Independent relation and executable worklist |
| §5 scheme subsumption | `SchemeSubsumption` | Executable prototype; reduction correctness deferred |
| §5 future/past projection and modality entailment | `ModeBackend`, `Proofs/Projection` | Proved all expression projections, partial definedness, both flexible/rigid identifier encodings, bounds entailment and positive-query declarative soundness |
| Modality consistency search | `Proofs/ModeSearch`, `Proofs/ModeSearchComplete` | Proved returned witness soundness, Boolean search termination and rejection correctness, eventual CNF normalization, and modality-search completeness |
| Residual consistency | `Proofs/SolverDefinedness`, `Proofs/ResidualModels`, `Proofs/SolverFlexible`, `Proofs/GroundReification` | Proved type-bound definedness, a ground model using the actual modality witness, preservation of flexible support, and a finite closed syntactic witness for `solve_consistency` |
| Modal self-equality | `Proofs/ModalEquality` | Proved finite satisfiability, failure of the former occurs policy at every fuel, equivalence of the corrected reduction, and corrected success for every fuel at least 12 |
| Tied residual orientation | `Proofs/ModeCycle` | Proved an unsatisfiable set was formerly accepted without a solution; corrected retention and rejection for every fuel at least 100 |
| Transitive mode work | `Proofs/ModePropagation` | Proved all-fuel exhaustion of a satisfiable input under the former policy; direct retention preserves exact declarative obligations and ground models, and succeeds on the witness for every fuel at least 100 |
| Modality orientation | `Proofs/ModeOrientation` | Proved a well-founded rank decreases for every newly emitted modality/definedness obligation, including after normalization; full worklist termination remains open |
| Visited modality constraints | `Proofs/ModeSeen` | Proved the modality-cache invariant through every solver transition and complete runs, sound duplicate discharge, and entailment of the final visited modality/definedness constraints |
| Solver identifier freshness | `Proofs/BoundedSupport`, `Proofs/SolverFresh` | Proved allocation bounds through complete runs, executable skeleton freshness for abstract expansion, and exact elimination of the scheduled equality with cache reset |
| Type-step orientation | `Proofs/TypeOrientation` | Proved normalization preserves structural rank and every type step either adds smaller obligations or enters a state whose next step clears the cache |
| Eliminated identifiers and substitution fixed points | `Proofs/SolverUnbound` | Proved exclusion of eliminated identifiers from pending, retained, and visited constraints through complete runs; all three lists and returned solver bounds are fixed by the accumulated substitution |
| Complete constraint cache | `Proofs/TypeSeen` | Proved type-cache preservation with the forced-reset expansion case, duplicate discharge for every constraint kind, and entailment of all constraints still cached after successful runs |
| Entailment under later substitutions | `Proofs/EntailmentTransport`, `Proofs/SolverTransport` | Proved context and type-only substitution transport with explicit image-definedness premises, including cached consequences, local steps and normalization |
| Accumulated image definedness | `Proofs/SolverStepEntailment`, `Proofs/SolverImages` | Proved backward entailment for steps preserving the substitution and image definedness through all steps/runs; every returned type image is defined under the returned residual bounds |
| Full executable solver soundness | `Proofs/SolverExtension`, `Proofs/SolverSoundness` | Proved preservation of eliminated equations through later substitutions and complete backward reconstruction of original input constraints; all conjuncts of `Deferred.solve_sound` are admission-free |
| Saved-substitution shape checking | `Proofs/ShapeEntry`, `Proofs/SolverEntry` | Proved a cyclic-shape witness with an acyclic saved substitution, rejection at every fuel at least two after applying that substitution, and unchanged empty-substitution behavior; full termination remains open |
| Ambient principality assumptions | `Proofs/PrincipalAmbient` | Refuted unrestricted whole-type assumptions using a finitely satisfiable witness; the deferred theorem now requires the paper's residual-bound grammar |
| Boolean normalization and solver reduction | `Proofs/Backend` | Proved truth preservation for both polarities, duplicate/tautology elimination, and validity equivalence of successful backend reports; no admissions |
| §5 generic concrete modality solver | `Subsumption` | **Existing proved correctness and stabilization, unchanged** |
| Core programs and regressions | `Examples`, `Regression` | Executed during validation/CI |
| Evaluator metatheory | `Proofs/Evaluation` | Proved soundness, completeness, determinism and fuel stability; no admissions |
| Interpretation properties | `Proofs/Interpretation` | Proved global references and empty shared ownership; no admissions |
| Semantic subtyping | `Proofs/Mode`, `Proofs/Subtyping` | Proved all declarative subtyping rules preserve interpretation, decrease ownership, and preserve definedness under modeled bounds; no admissions |
| Annotation erasure | `Proofs/Erasure` | Proved for all evaluation rules and capture trimming; no admissions |
| Recursive annotation transport | `Annotations`, `Proofs/Annotations` | Executable value substitution; proved evaluation, erasure, reference and freshness preservation |
| Scheme-instance transport | `Proofs/SchemeInstantiation` | Proved transport through capture-avoiding substitution with exact body equality and equivalent bound entailment, including repeated parameters and partial images; proved the substituted variable-typing case with definedness explicit |
| Scheme assumptions and symbolic context witnesses | `Proofs/SchemeBounds`, `Proofs/GenerationContextTyping` | Proved instance-preserving explicit assumptions, reflexive prepared contexts, binding-context splits and whole-context locks with freshness premises; substitution and the full generation induction remain open |
| Fresh schemes and contexts | `Proofs/SchemeFreshening` | Proved freshening beyond arbitrary ambient bounds, exact instance equivalence, source subsumption and context weakening; a fresh context supplies all lock freshness premises |
| Target assumptions in scheme comparison | `Proofs/SubsumptionAssumptions`, `Proofs/ConstraintModels`, `Proofs/SchemeBounds` | Refuted reflexivity of the raw-target rule on an inhabited equality scheme; corrected comparison is reflexive for every scheme, preserves every former comparison, and retains whole-core resource soundness |
| Defined generalized instances | `Proofs/GeneralizationDefinedness` | Refuted a contract missing well-formed instance substitutions; the corrected constant-function example is proved for every substitution satisfying that hypothesis |
| Syntactic subsumption instances | `Proofs/SkolemSubstitution`, `Proofs/InstanceDefinedness`, `Proofs/SubsumptionInstances` | Proved source-instance reconstruction and subtyping for every defined target instance, retaining arbitrary ambient bounds, repeated parameters and unused partial images |
| Admissibility of used bindings | `Proofs/TypingAdmissibility` | With defined ambient subtype operands, proved result definedness and admissible syntactic instances for used bindings and lambda capture annotations; solver residuals satisfy the premise |
| Sharing below capture locks | `Proofs/TypeVariablePredicates`, `Proofs/SharingLockCapture`, `Proofs/CaptureRefinement` | Refuted the current inferred capture annotation and proved a refined annotation at the same inferred type and residual bounds; executable repair and its general proof remain open |
| Quantified modal refinement | `Inference`, `Proofs/ModalRefinement`, `Proofs/NestedLockRefinement`, `Proofs/RefinedSharing`, `Proofs/RefinedContexts` | Proved nested instance retention, refined shared-branch comparison, complete context splitting and freshness preservation, and lookup-instance recovery; whole-term and executable integration remain open |
| Simultaneous substitution | `Proofs/Substitution` | Proved composition for types, modalities, constraints and bounds, plus agreement of scheme substitution with its exposed binder action; no admissions |
| Transport through scheme binders | `Annotations`, `Proofs/Annotations`, `Proofs/ScopedCaptures` | Executable per-capture binder transport and paired scheme/value substitution; proved erasure, reference, liveness and evaluation preservation; nested polymorphic witness |
| Explicit value instantiation | `Annotations`, `Proofs/Instantiation`, `Proofs/ScopedCaptures` | Ordered arguments transport metadata; proved instantiation, definedness-guard and erasure contracts; optional transport route, not required by resource soundness |
| Subtyping substitution | `Proofs/PartialSubstitution` | Proved with explicit definedness of modality images, and for all ordinary modality images; proved counterexample to the former unrestricted statement |
| Term scope | `Proofs/Scoping` | Proved capture-avoiding substitution and renaming preserve scope for every term constructor; no admissions |
| Context routing and lookup | `Proofs/Generation` | Proved usage splitting and both directions of symbolic lookup correspondence; no admissions |
| Declarative weakening | `Proofs/Declarative` | Proved context weakening for annotated and raw typing; no admissions |
| Well-formed intermediate types | `Proofs/TypingDefinedness`, `Proofs/UndefinedDomain` | Proved ground definedness for every typing rule and automatic guards for ordinary source types; retained and excluded the former undefined-domain counterexample |
| Ambient assignment and quantified scope | `Proofs/Grounding`, `Proofs/ContextScoping` | Scheme instantiation fixes all non-quantified identifiers; proved monomorphic contracts and a witness requiring fresh quantifiers in sharing/locking |
| Ambient skolem scope | `Proofs/SubsumptionScope` | Proved the former comparison could confuse an ambient rigid identifier with a new quantifier; corrected skolem indices avoid every ambient type and modality identifier |
| Ownership evidence for ground instances | `ResourceSemantics`, `Proofs/Resources`, `Proofs/ResourceCapture` | Proved semantic repair; erasure invariance, global references, empty shared ownership, semantic lookup, and the original captured-credit witness |
| Resource interpretation under subtyping | `Proofs/ResourceSubtyping` | Proved all declarative subtyping rules preserve instance-indexed interpretation while shrinking ownership, including symbolic bounds and arbitrary inherited modalities; no admissions |
| Semantic context joins | `Proofs/GroundAssignment`, `Proofs/ResourceContexts` | Proved fresh ground instantiation, empty ownership for polymorphic sharing, and valid, contained, disjoint component environments for every join rule |
| Polymorphic capture diagnostic | `Proofs/PolymorphicCapture` | Proved counterexample to the former annotation-dependent fundamental statement; no admissions |
| Whole-core fundamental theorem and corollaries | `Proofs/ResourceSoundness`, `Proofs/Soundness` | Proved for every typing constructor, with termination/no-stuck, live references, resource bounds, and a closed-program corollary; no admissions |
| Remaining structural and algorithmic metatheory | `Proofs/Structural`, `Proofs/Algorithms` | 12 explicit admitted obligations |

```text
Core/Mode → Core/Syntax → Core/Scoping
                      → Declarative → Generation
                      → Evaluation
Declarative + Evaluation → Semantics
Core/Syntax + Subsumption → ModeBackend
ModeBackend + Declarative → Constraints → Inference
                                       → Rewriting
                                       → SchemeSubsumption
Definitions + executables → Examples → Regression
Definitions + executables → Proofs/Structural → Proofs/Soundness
                                             → Proofs/Algorithms
```

`import ModalityInference` includes the complete definitions and executables.
`import ModalityInference.Subsumption` retains the original independent solver API.
The optional `import ModalityInference.Proofs` includes the admitted theorem
worklist alongside the established proofs. Tests do not import it. The audit scans source imports and also
uses Lean's `#print axioms` to check transitive dependencies of all public
executables, declarative/semantic definitions, and the two established solver
results.

## Corrections and regression witnesses

The source paper and its new full-system specification section record the same
corrections. The POPL reviews and response are in the enclosing paper repository's
`popl27/` directory.

| Correction | Minimal regression/witness |
| --- | --- |
| Explicit bounds instead of joins/meets in ordinary object modalities | `stackPair`: `localLower ≤ μ`; `stackEscape` rejects |
| Separate lower and upper `BOUND` rules | A mode constrained between `bottom` and `identity` |
| Symbolic function subtyping ignores past | Same arrow at aliased/unique outer modes |
| Symbolic locks depend only on future; typed capture metadata | Modes differing only in uniqueness have identical captures |
| Closed `def` inference solves before generalizing | `polyIdentity`, `nonClosedDef`, `inconsistentUnused`; an unused `stackEscape` also rejects |
| Missing `region` inference | `stackScoped` succeeds, `stackEscape` rejects |
| Reuse locality follows the credit | `reusePair` keeps its stack location; it cannot escape its region |
| Case routing includes both branches, excluding binders | `branchUsage`: right branch alone uses the outer argument |
| Reversed past projection in `ModSplit` | Unique-to-aliased succeeds; aliased-to-unique rejects |
| Closure adjoint orientation | Exhaustive 64 comparisons; same-operator swap has a counterexample |
| Generated locks stay outside scheme quantifiers | `GenerationScope`: a lock/quantifier collision gave a reusable closure a captured unique result; the scoped generation contract excludes it and the unchanged public initializer establishes the required invariant |
| Definedness survives generation and later type substitution | `GenerationDefinedness`: lookup checks written partial modalities; well-formed substitution images exclude undefined lambda-domain images without fresh-variable guards |
| Partial residual side conditions survive rewrites | Both undefined residuals reject, including inside type-variable bounds |
| Substitution updates residual bounds and previous images | `α = β; β = unit`; conflicting repeated assignments reject |
| Subtyping substitution requires defined modality images | `unit@μ ≤ unit@top` fails after substituting the undefined residual `top / bottom`; checked in `Proofs/PartialSubstitution` |
| Cycles and occurs checks | Benign mode cycle succeeds; direct and indirect recursive type bounds reject |
| Modal self-equality is not structural recursion | `α = α @ m` succeeds for every concrete mode; undefined `m` and wrapped function recursion reject |
| All target quantifiers skolemized; assumptions retained | `polyId` versus a monomorphic identity; `bounded` with/without its declared assumption |
| Allocation source, exclusive upper index and future-frame partition | Tail slices start at 1 and 2; distinct branches enter distinct fresh frames |
| Typed ownership and separate reference validity | `aliasedField` inside a unique pair and a dead stack frame |
| Instantiation fixes every non-quantified identifier | `AmbientCaptureScope`: a variable absent from the scheme can still occur in capture metadata; changing it is rejected |
| Scheme binders are fresh for ambient bounds and symbolic locks | `ContextScoping`: the former sharing premise allows two copies of the same owned credit; alpha-renaming removes the bound/quantifier collision |
| Scheme-comparison skolems are fresh for ambient bounds | `SubsumptionScope`: under `unit ≤ rigid₁`, the former comparison incorrectly accepted `unit` as `∀α. α`; the corrected comparison chooses `rigid₂` |
| Target constraints supply usable assumptions | `SubsumptionAssumptions`: `∀α. (α = unit) ⇒ α` has a unit instance but the former raw-target rule cannot compare it with itself; expanding equality directions and written guards restores general reflexivity |
| Generalized instances retain result definedness | `GeneralizationDefinedness`: undefined internal argument images violate the substitution hypothesis; `λx. ()` is proved typable for every well-formed instance substitution |
| Fuel is not rejection | Small-budget inference/evaluation exhaust; larger budgets succeed |

The regression checks also compare small two-mode queries and all concrete mode
comparisons against exhaustive valuation checking before accepting backend results.
They exercise every term constructor and both sum branches.

## Remaining inference obligations

Each of the six remaining directly admitted theorems has a prerequisite comment immediately above it.
The former annotation-dependent fundamental claim remains separately recorded
as a refuted proposition. Its corrected resource formulation and corollaries are
proved for the whole core. Five further contracts are preserved as proposition
definitions in `Proofs/Obligations`; none supplies a proof or adds an admission.
Principality remains required for the paper's claim. Solver correspondence may
support its proof; scheme-checker correctness and closed-term substitution remain
separate tasks. The semantic proof uses environments and does not need the latter.
Inference work must validate the remaining contracts and justify corrections with
retained evidence. Admission counts do not measure these unproved specifications.

`GroundInstantiates` fixes every identifier outside the quantified domain, including
ones absent from a scheme's body and bounds. This preserves the interpretation of
ambient identifiers used only by capture metadata. Sharing and locking now require
scheme binders fresh for ambient bounds, and locking additionally requires them
fresh for its symbolic modality. The checked counterexample uses the ambient
bound `aliased ≤ μ₀` with the separately quantified scheme `∀μ₀. credit@μ₀`:
the former sharing premise holds but both components own the same credit at a
unique instance. `ContextScoping.renamed_fresh` verifies that alpha-renaming makes
the scope valid while retaining polymorphism. The resource interpretation resolves the distinct variable-instantiation metadata
defect below; the historical interpretation and its counterexample are retained.

Scheme comparison also freshens its target skolems above ambient bounds, not only
above the two schemes. `SubsumptionScope.former_weakening_unsound` proves that the
former rule accepts `unit` as `∀α. α` under the satisfiable bound `unit ≤ rigid₁`:
it reused `rigid₁` for the target quantifier. The unit value fails the credit
instance of that scheme. The corrected `Scheme.subsumptionIndices` accounts for
ambient type and modality identifiers, with general freshness proofs. Closed
scheme comparison retains its previous indices; the generic solver is unchanged.

The target's instantiated bounds must also expose their equality directions and
written modality-definedness guards. `SubsumptionAssumptions.raw_not_reflexive`
refutes the former rule on `∀α. (α = unit) ⇒ α`, whose unit instance is proved.
The raw skolemized equality was invisible to the subtype bound rule. `Subsumes`
now uses `Δ ++ assumptions.assumptions`. The existing assumption construction
lives in `Declarative`, and `Bounds.assumptions_ground_iff` proves that it has
exactly the same ground models as the original bounds. `RawTargetSubsumes.corrected`
preserves every former comparison; `Subsumes.refl` and `ContextLe.refl` cover all
schemes and contexts. Resource subsumption, realizability, freshening, locking,
sharing and whole-core semantic soundness remain proved. This declarative repair
does not establish the still-deferred executable scheme-comparison contracts.

The counterexample binds a closure with scheme `∀μ. unit → credit@μ`. Its capture
metadata assigns the captured heap credit type `credit@μ`. The current scheme
interpretation accepts this closure for every ground choice of `μ`. Looking up
the binding with `μ := unique` returns the same closure, while the ambient
assignment can still interpret its capture's `μ` as aliased. Calling the closure
then returns an owned credit with empty captured ownership, no argument ownership,
and no fresh allocation. `no_unrestricted_soundness` proves the contradiction
using a typed variable, a satisfying environment and compatible supplies.
The issue concerns ghost capture metadata; no runtime stack escape is asserted.
`transported_interpreted` proves that applying the same instantiation to the
captured value restores this example's unique-result contract under every ambient
assignment. This is a checked annotation-transport witness; whole-core soundness is now
proved by the independent resource interpretation.

A second capture witness tests nested polymorphism. Substituting into a closure
that captures `∀μ₀. unit → credit@μ₀` renames that capture scheme's binder to `μ₁`.
Uniform annotation mapping leaves the nested captured value's credit annotated
with `μ₀`. `substCapturedTypes` transports that value using the scheme's exposed
`substitutionAction`, so its annotation becomes `μ₁` too. The example proves both
the difference in annotations and equality of runtime structure after erasure.
These mechanisms remain available for annotation-aware elaboration. The proved
fundamental theorem instead uses instance-indexed resource evidence with the
original evaluator.

The former unrestricted subtyping-substitution statement also had a missing
precondition: arbitrary internal modality expressions include undefined residuals.
`PartialSubstitution.no_unrestricted_subtyping_substitution` refutes that statement
without admissions. The corrected `Subtype.substitute` is proved assuming each
modality image is defined in every model of the substituted bounds.
`Subtype.substitute_ordinary` discharges that condition for ordinary modalities;
their evaluations are proved total. Residual substitutions must retain their
definedness obligations.

| Proof module | Obligations | Prerequisites/dependencies |
| --- | --- | --- |
| `Structural` | None; the unused admitted closed-term-substitution statement was removed | Freshening and alpha-renaming, scheme instantiation and closure capture; substitution composition, subtyping substitution with defined modality images, term scope, weakening, usage splitting, symbolic lookup, instance-indexed context joins and locking are proved |
| `Obligations` | Unproved proposition definitions for principal factorization, solver correspondence, scheme-checker soundness/completeness, and optional closed-term substitution; no admissions | Preserves the removed contracts and their side conditions. Principality still needs a proof; merely defining its proposition does not establish the paper's claim |
| `Soundness` | None: corrected fundamental soundness, termination/no-stuck, live results, and ownership bound are proved | Complete typing induction in `ResourceSoundness`; independently built and audited without either deferred worklist |
| `Algorithms` | Scheduled termination, solve completeness, generation soundness/completeness, elaborated inference soundness and completeness; closed-definition generalization is derived but still depends on generation soundness | Full executable solver soundness, generator correspondence and initialized lock hygiene, local rewrite equivalence, configuration solution preservation, substitution output invariants, solver allocation freshness, Boolean projection/CNF correctness, modality-search termination/completeness and finite closed residual consistency are proved; remaining prerequisites include worklist simulation/termination, representative-search completeness, rigid entailment and subsumption witness reconstruction |

Completeness statements require a sufficiently large fuel budget. Rewrite
expansion requires distinct flexible variables fresh for the complete original
constraint, pending/residual constraints and accumulated substitution. Subsumption
statements require distinct scheme parameters and residual declared bounds.
Rewrite termination is a separate obligation from the already-proved generic solver
stabilization theorem. The paper's operation-count discussion is not a Lean cost
model, and the finite search/CNF prototype may take exponential time or space.

Borrowing, references as language constructs, concurrency, local let-polymorphism,
a parser/CLI and compiler integration remain future work.
