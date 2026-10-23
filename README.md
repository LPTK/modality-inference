# First-class modalities in Lean

This library defines and implements the core calculus of *First-Class Modalities
in OxCaml*: functions, products, sums, closed polymorphic definitions, heap and
stack allocation, space-credit reuse, and regions. It provides independent typing
and evaluation judgments, executable inference and evaluation, and checked proofs
of source soundness, closed inference completeness, and ground principality.

The executable syntax is `RawTerm`; inference returns the input term unchanged.
`Runtime.Value.closure` stores a trimmed environment and a raw body. `GuardedSourceTyping`
states typing directly for this syntax. An annotated representation supports the
semantic proofs through proved erasure correspondences.

## Build and use

Use the toolchain in `lean-toolchain` and dependencies in `lake-manifest.json`.
Mathlib is pinned to `bd350e6b5fe8a1dd9a2729913b022f3b5761787a`.

```sh
elan toolchain install leanprover/lean4:v4.25.0-rc2
lake exe cache get
lake build
lake build ModalityInference.Examples ModalityInference.Regression ModalityInference.Proofs
python3 scripts/audit_admissions.py
```

The source semantic target can also be built and audited independently of
inference and solver proofs:

```sh
lake build ModalityInference.Proofs.SourceSoundness
python3 scripts/audit_admissions.py --semantic
```

There are no Lean admissions. The audits reject admissions and dependencies on
`sorryAx`. The semantic audit also checks the complete local import closure and permits only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`. Unproved contracts are proposition
definitions, not assumptions available to established proofs.

Save this example in a Lean file and run `lake env lean Example.lean`:

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
  Runtime.evalFuel 100 {} [] result.elaborated

#eval solve 500 [
  .mode (.const Mode.bottom) (.var (.flex 0)),
  .mode (.var (.flex 0)) (.const Mode.identity)]
```

All public functions below are in namespace `ModalityInference` and return
`RunResult`: `success`, `rejected diagnostic`, or `exhausted`.

| Function | Successful result |
| --- | --- |
| `infer fuel context term` | Scheme, unchanged term, type substitution, symbolic residual bounds, and rewrite trace |
| `solve fuel constraints` | Substitution, residual bounds, concrete consistency witness, fresh counters, and trace |
| `satisfiableModes fuel constraints` | A concrete modality assignment modeling the modality constraints |
| `Runtime.evalFuel fuel supplies environment term` | A runtime value |
| `checkSubsumption fuel inferred declared` | Internal comparison substitution and residual validity evidence; soundness, termination, and completeness under residual declared bounds or a finite declared-shape model |

Exhaustion is not rejection. Increasing fuel permits deeper recursion and more
worklist or normalization steps. The Horn check's `requiredFuel` is a threshold
based on expression size and the number of atoms; it is not a bound on total
work. No complete inference time or space bound is proved.

`ModalSynthesis.synthesize fuel flexibleAtoms formula` performs uniform symbolic
modality synthesis for arbitrary Boolean formulas, with locality separated from
affinity and uniqueness. It returns expressions with the required dependencies
and guaranteed modality reification. The checker uses this path and returns
actual modality images through `SchemeModeSynthesis.run`; it does not expand
Boolean assignments. The wrapper proves validity under the assembled modality
interpretation, exact finite domains, and removal of selected fresh variables.

The structural checker uses scope-preserving preparation and compatible internal
witnesses. `checkSubsumption` requires the instantiated body and every quantified
image to be defined under the ambient and declared bounds. Symbolic residual
expressions remain allowed when those bounds entail their guards. It appends
body/image guards to source obligations; the declared assumptions and fresh
skolem indices remain unchanged. Exact
witness equivalence with `AlgebraSubsumesUnder` is proved, so this transformation
preserves every witness in the intended domain.

`CompareTy` is a finite internal language with binary joins and meets between
compatible shapes. Public `Ty` and `Scheme` remain join-free. Two-stage shape
unification freezes declared parameters before solving fresh source shapes.
Structural templates, positive certificates, and finite-basis propagation
reconstruct one substitution satisfying all original bounds and the body goal.
The actual evidence's domain and body/image definedness are proved.

`ComparisonPropagation` computes least positive type polynomials by ordered
clause projection and relational propagation. Upper and constant obligations
remain symbolic residuals. Compilation, finite stabilization, least solutions,
reification, and exactness for the supplied finite basis are proved. Signed
controls supply positive basis representations for supported modality actions.
`ComparisonJointChecker` combines all opaque groups with one shared modality
assignment, reconstructs compatible finite type images, and restores the complete
source obligations and body. The public interface preserves successful direct
certificates and invokes this joint driver when they reject.
If the joint driver rejects, `ComparisonDeclaredAnchors` constructs joins of
fixed lower endpoints or meets of fixed upper endpoints and certifies every
original obligation against whole declared edges. This accepts structured
declared bounds without treating them as component inequalities. Its returned
substitution has the same soundness, definedness, and fuel-stability guarantees.
If declared shape equations have no finite model, their shape-compatibility
conditions hold vacuously; this phase still requires subtype certificates and
all scalar guards. Thus it accepts a declared cyclic edge without treating
shape inconsistency as a proof of arbitrary subtyping.
`checkSubsumption_declared_edge_complete` proves eventual public acceptance of
every literal monomorphic declared subtype edge, including its original guards.

For finite declared shape models, `Proofs/ComparisonStructuralBasis` gives
defined type images finite lattice normal forms at their resolved image shapes.
The bases retain fixed names at compound shapes and include constructor
combinations and signed modality controls. `ComparisonStructuralPrepared`
connects these forms to supported admissible witnesses under arbitrary ambient
bounds. `ComparisonShapeSelection` obtains valid local shape cuts from finite
input anchors. Retraction preserves algebraic order and guarded modality
actions, while leaving retained subtrees literal. `ComparisonStructuralMatrix`
compiles finite constructor tables and proves their exact interpretation on
reconstructed child polynomials. `ComparisonPreparedDriver` connects these
components to one shared prepared comparison: guarded shape alternatives, all
original endpoint queries, and scalar obligations use one type image family and
one modality strategy. A necessary scalar preflight rejects infeasible guards
before structural compilation; its witness is discarded. Actual reconstruction
is sound, terminates, and preserves completed results.
`checkSubsumption_finite_shape_complete` proves eventual public acceptance of
every admissible comparison with distinct source binders and a finite declared
shape model. Support, mode idempotence, and all solver side conditions are
derived from the original witness.

## Constraint solving

`solve` first runs the deterministic structural worklist in `Constraints`.
It normalizes types and modalities, checks finite constructor shapes, expands
forced type shapes with fresh variables, eliminates type equalities, and orients
residual and closure transformations by variable order. It retains symbolic
bounds and every required partial-expression definedness guard. Proved cache and
substitution invariants justify duplicate discharge and updates to saved images.
`runSolver_correspondence` proves that the actual worklist produces an abstract
guarded-rewriting derivation. Every completed derivation entails its substituted
input and has defined substitution images. Under residual ambient bounds,
`principal_factorization` proves that every defined symbolic solution factors
through the result, preserving any finite observed scope reserved before solving.

`ModeConsistency.solve`, exported as `satisfiableModes`, then checks modality
consistency by deterministic propagation:

- **Ordinary inference uses direct Horn propagation.** `PolarizedConstraints`
  distinguishes monomial modalities in types from polarized residual expressions
  in bounds. Monomial projections use only constants, variables, and conjunction.
  Generation, freshening, sharing, locks, normalization, type substitution, and the executable worklist preserve this domain. Boolean
  projection preserves both inequalities and residual definedness in the Horn
  grammar. `HornPropagation` translates these formulas directly to the existing
  generic Horn solver using a sorted atom domain. It computes the least fixed
  point and checks the remaining constant conclusions; a successful check returns
  the least Boolean model. `Proofs/PropagationSchedule` relates this execution to
  the finite update schedule in the paper. This path does not construct CNF or
  branch on assignments.
- **The unrestricted constraint API has a separate compatibility path.** Arbitrary
  `Bounds` and externally supplied schemes may lie outside the polarized domain.
  `CNFPropagation` eliminates Boolean atoms in order by combining their lower and
  upper bounds, then reconstructs an assignment in reverse order. This path does
  not branch on valuations, but CNF construction and elimination may require
  exponential time or space.

The domain guarantee covers the full core and open contexts satisfying
`Context.IsInference`. In particular, every closed inference consistency query
uses the Horn path. `generate_defn_eq_horn` and `infer_eq_horn` establish the actual
executable equations without assuming a successful final outcome: a nested or
unused definition cannot reach the compatibility path merely because it or its
enclosing run later rejects or exhausts fuel.

`Solved.witness` certifies consistency and remains separate from the symbolic
substitution and residual bounds. Generalization does not replace modality
variables by this concrete witness. The optional DPLL oracle is
`searchSatisfiableModes`; normal `solve` and `infer` do not call it. The original
generic solver in `Subsumption.lean` is unchanged and remains independently
available through `import ModalityInference.Subsumption`.

`SubsumptionLinear` supplies an equivalent synchronous implementation used by
the compiled modality backend. Every antecedent reads the pass's input while
conclusions accumulate with one scalar join per variable occurrence.
`Equation.decideLinear_operation_bound` proves a bound of
`(n + 1) * rightSize R + 6 * leftSize L + 1` primitive Heyting operations,
including the final order test. Expression sizes include implication antecedents;
the bound counts algebra operations, not valuation lookup or storage costs.

## Representation and semantic conditions

Modes have locality, affinity, and uniqueness Boolean coordinates. Modality
comparison reverses the uniqueness coordinate. Ordinary `Modality` expressions
contain constants, variables, and composition. Internal `ModExpr` also contains
joins, meets, partial residuals, and lock operations. Undefined residuals remain
explicit obligations through normalization, rewriting, and substitution.

Term variables use de Bruijn indices. A lambda, case branch, or definition body
binds one variable; `split` binds the credit at index 0 and fields at indices 1
and 2. A definition RHS must be closed in term variables and is inferred and
solved in an empty term context, including when its binding is unused. Open
inference excludes context-free identifiers from generalization. Type and
modality identifiers are distinct, with flexible and rigid variants.

Scheme substitution freshens binders. Quantifiers must be fresh for ambient
bounds and symbolic locks; instantiation fixes all identifiers outside its
quantified domain. Sharing and locking retain constraints under the scheme's
quantifiers so each use receives fresh instances. Declarative scheme comparison
freshens its target skolems beyond ambient identifiers and makes target equality
directions and definedness guards available as assumptions.

`Runtime.Eval` is an independent big-step semantics. The executable evaluator
trims closures by syntax free variables, replacing unused slots with unit to
preserve indices. It uses separate supplies for subcomputations and fresh region
frames. Its soundness premises include modeled bounds, an interpreted input
environment with pairwise disjoint reserves, and compatible allocation supplies:
positive strides, a live current frame, fresh future frames, and no collision
with any input reference. Evaluation does not dynamically check these premises.

Resource evidence is indexed by each admissible ground scheme instance. Each
binding reserves resources sufficient for all its instances; a use selects the
appropriate subset. Products preserve full field types and separation from the
cell and other fields. Reusable closures own no resources, and every call must
account for its result using captures, the argument, or fresh allocation.
Liveness concerns **all references**, including aliases; ownership and separation
use the selected owned resources. Region escape therefore requires globality
of aliased references as well as owned ones.

## Verified guarantees

| Guarantee | Proof entry point |
| --- | --- |
| Direct source typing, full open-environment resource soundness, eventual evaluation without rejection, live results, ownership bounds, and fresh-only ownership for closed programs | `Proofs/SourceSoundness` |
| Evaluator soundness, completeness, determinism, fuel stability, and exact correspondence with the proof representation, including rejection and exhaustion | `Proofs/Runtime` |
| Exact source preservation, hygienic generation, and correspondence with the independent generation relation | `Proofs/GenerationExecution`, `Proofs/GenerationCorrespondence`, `Proofs/GenerationSoundness` |
| Successful inference gives a `GuardedSourceTyping` derivation with defined instances and guarded context comparisons, plus defined returned body/images under its residual bounds | `Proofs/GuardedSourceInference` |
| Every declaratively typable closed source term is accepted with sufficiently large fuel; every successful result covers all its valid ground result instances up to subtyping | `Proofs/InferenceCompleteness`, `Proofs/SourceInference` |
| Solver output entails the original constraints after substitution and preserves acyclicity and definedness; flexible inputs have a ground model using the returned witness | `Proofs/SolverSoundness`, `Proofs/SolverImages`, `Proofs/ResidualModels` |
| Initialized solving terminates on every input; on flexible inputs it eventually accepts every satisfiable input and factors every original ground solution through every successful result | `Proofs/SolverTermination`, `Proofs/SolverCompleteness` |
| Actual worklist runs produce abstract rewriting derivations; completed derivations entail their input and preserve definedness | `Proofs/WorklistCorrespondence`, `Proofs/SolverRewriting`, `Proofs/RewriteEntailment` |
| Every defined symbolic solution under residual ambient bounds factors through the returned solver result, including every reserved observed identifier | `Proofs/SymbolicPrincipality` |
| The compiled synchronous modality decision worker equals the generic decision procedure and has a measured primitive-algebra operation bound | `SubsumptionLinear`, `Proofs/SubsumptionCost` |
| Actual generation and rewriting preserve the direct Horn domain; both consistency paths are sound, complete, terminating, and preserve successful results at larger budgets | `Proofs/PolarizedConstraints`, `Proofs/HornPropagation`, `Proofs/CNFPropagation`, `Proofs/ModeConsistency` |
| Symbolic Horn elimination has an exact accepted grammar, a uniform expression witness, an equivalent residual query, and no selected flexible atoms; supported modality images reify and assemble with the specified domain and definedness | `Proofs/SymbolicModes`, `Proofs/SymbolicSchemeModes` |
| Scheme preparation preserves scope and provides fresh source and target ranges; a solution of its prepared goals reconstructs an instantiation with exactly the source quantifier domain | `Proofs/SchemePreparation`, `Proofs/SchemePreparedScope` |

`SourceTyping.resource_semantic` retains the full interpreted open environment
and every admissible polymorphic instance. `inference_source_semantic` connects
the actual inferred term to that theorem under modeled residual bounds and an
interpreted substituted context. Symbolic principality additionally covers
solutions with defined images under residual ambient bounds.

`import ModalityInference` provides definitions and executables.
`import ModalityInference.Proofs` adds established proofs and the explicit
unproved specifications in `Proofs/Obligations`. Neither the source semantic entry
point nor public executables depend on those unproved specifications.

## Remaining work and scope

`checkSubsumption_defined_subsumes` proves `AlgebraSubsumesUnder` for every
successful public check, and `checkSubsumption_evidence_instantiatesUnder` proves
the discipline for its actual evidence. The strong relation preserves public
ground instances and resource interpretations for every source scheme, without
a typing premise. Successful closed inference followed by signature checking
therefore gives safe execution at every admissible declared instance.
Termination and completed-result fuel stability are proved on every input.

`inference_guarded_source_defined` proves body and returned-substitution
definedness under the actual residual bounds, together with the paper's guarded
source derivation. Every variable instance has defined body/images, every changed
context binding has a defined scheme-comparison witness, and unchanged bindings
use identity. All constructors are covered without a global well-formedness
premise on the input context. Independent semantic soundness, closed completeness,
and ground principality are proved for this guarded source judgment.

`scheme_subsumption_complete` proves `Obligations.SchemeSubsumptionComplete`:
every `AlgebraSubsumesUnder [] source target` witness is eventually accepted
when the binders are duplicate-free and target bounds are residual. There is
no additional closedness, consistency, or global-totality premise. Symbolic
residual expressions remain allowed under their original definedness guards.
Preparation, shape solving, reduction, and collection retain one defined
witness through the actual templates. Boundary summaries and selector
propagation solve all groups with the same modality strategy. Compatible
coordinates reconstruct one finite type per leaf with proved shape, definedness,
and identifier support; restoration establishes the complete original body and
source bounds. The returned substitution has exactly the quantified domain.
Annotation classification includes source-bound operands, so guarded residuals
appearing only inside a bound remain covered.
`checkSubsumption_finite_shape_complete` additionally covers structured declared
bounds admitting a finite shape model, with the same admissibility requirements.
For contexts without such a model, `ComparisonRankedBasis` and
`ComparisonRankedWitness` give finite generated-basis normal forms at a common
constructor rank for every admissible witness. The general terminating
comparison algorithm still needs an effective bound or decision for those ranks,
as well as the arbitrary-ambient-context bridge.
`ComparisonRankedOrderSimulation` gives exact recursive positivity and
constant-boundary tests for that basis, retaining different constructor choices,
function-domain variance, and modal controls. Saturating their interleaving with
the original constraint edges across all ranks remains unproved.
`ComparisonLeastPropagationLimitation` proves that finite witness existence
cannot be reduced to finite stabilization of least forward propagation: a
defined finite prefixed witness can exist while every ascending lower iterate
fails the required inequality.
`ComparisonAmbientDriver.run` accepts explicit ambient bounds and proves
unconditional successful-result soundness, termination, and fuel stability.
Complete acceptance under raw partial ambient bounds still needs a finite
comparison procedure preserving their partial endpoints and original guards.
`ComparisonBalancedDerivation` extracts fully defined derivations when each
declared subtype edge has either two defined endpoints or two partial endpoints.
`ComparisonBalancedContext` supplies guarded context transport, and
`ComparisonBalancedProjection` removes partial subtype edges while separately
retaining every original shape equation. Defined comparisons and the same
prepared substitution are preserved in both directions, with identical scalar
models, exact domains, and body/image guards.
`ComparisonBalancedDecision` connects this mathematical projection to the exact
fixed-endpoint observer checker when the original context has no finite shape
model. The projection is noncomputable as defined;
these are internal transfer theorems, not an extension of the public driver.
The regression module covers a non-reflexive partial edge, retention of shape
information, and why bounds crossing between defined and partial endpoints
cannot simply be deleted.
In `ComparisonRawCarrierSoundness`,
`ComparisonRawCarrierRestriction.finite_capsule_locality` proves an exact
restriction of arbitrary mixed-bound comparisons to a finite set of literal
partial capsules determined by the raw bounds and requested endpoints.
Its independent restricted calculus permits all well-shaped joins and meets
of partial terms. Carrier ideals factor finite covers through monotone actions
and structural constructors; this validates every original rule, including
partial products, literal composition, function variance, and guarded equations.
The guarded-join carrier refuted by `ComparisonRawCarrierCountermodel` remains
separate from this replacement.
In `ComparisonRawCarrierPrepared`,
`ComparisonRawCarrierRestriction.prepared_witnessUnder_iff_restricted` preserves
the same prepared type and modality substitution, exact domains, and original
body/image guards with a capsule boundary depending only on the prepared input.
The restriction leaves defined constructor structure and partial lattice
expressions unbounded; it does not yet supply an arbitrary-context order checker
or the input-only rank bound needed for complete witness synthesis.
`ComparisonRawHeadLocality` strengthens this to a finite boundary of whole
partial constructor heads for raw types and defined witnesses. Its independent
restricted calculus explicitly checks constructor and congruence outputs. Indexed sparse tables
synchronize ordered total controls, retain exact partial prefixes, and handle
function-domain variance. The coordinate interpretation validates every original
rule and reflects guarded endpoints; raw types and defined witnesses satisfy
that guard automatically. `ComparisonRawHeadPrepared` preserves the same
admissible substitution and original guards with an input-only head boundary.
The tightened carrier excludes total actions on naked partial lattice nodes;
`ComparisonRawHeadModeOrbits` gives executable finite representatives for the
supported total controls on partial heads. Optional-cut separation and the
observer range product provide exact lower/upper shadow constraints, including
contravariant function rows and empty cuts. `ComparisonRelativeIntervals` and
the relative-table modules extend the defined algebra and recorded boundary
rows simultaneously. `ComparisonObserverShadowActions` constructs a finite
optional-cut diagram carrying the finite monoid of supported total controls.
The constructor tables preserve both the whole defined range algebra and every
recorded raw row, including contravariant function inputs and literal partial
prefixes. `ComparisonObserverShadowModelReflection` proves all-rule soundness
and exact order reflection at the finitely many raw interpreter calls, without
requiring defined ambient type bounds. `ComparisonObserverShadowQueries` retains
joint query patterns through finite extraction, including arbitrary defined
internal lattice terms. `ComparisonObserverShadowQueryModel` constructs one
finite interpreter reflecting raw/raw, defined/defined, and both mixed query
directions. These results assume the original context has no finite shape model.
Effective finite-model certificate checking and public integration remain
necessary; the rank of unknown witnesses is still unbounded.
Finite observer machines decide fixed defined-endpoint comparisons
under defined type bounds without a finite shape model. Their boundary and state
bound are computed from those endpoints, and finite coordinate certificates have
an exact symbolic encoding connected to the validity backend, with proved
positive/negative correctness and eventual stable return. This does not bound
the constructor rank of unknown scheme images.
`ComparisonRankedObservers` extends the finite observer bound uniformly to every
defined, supported endpoint at a fixed constructor rank, independently of its
lattice-polynomial size. `ComparisonRankedSubstitution` bounds instantiated
endpoint rank by the common image rank plus the written endpoint's constructor
depth. These results supply a fixed-rank observer bound, not a stopping bound
across ranks.
`ComparisonRankedDecision.run` compiles all endpoint obligations over that finite
observer family and synthesizes one shared family of finite lattice images for
a supplied common modality substitution. Its exact machine contract proves
soundness, completeness, rejection correctness, termination, and completed-result
stability. `prepared_run_eventual` derives eventual acceptance at some rank from
every admissible prepared witness under defined declared type bounds without a
finite shape model, deriving endpoint guards from the original assumptions.
`ComparisonRankedJoint.synthesize` now computes the observer bound, checks the
original scalar obligations, and synthesizes both the shared type images and
one common modality action. Under the same defined-bound, no-shape-model
conditions, `synthesize_complete` derives eventual success at some rank from
every admissible witness; `synthesize_sound` proves the actual returned action
admissible under the original assumptions. `compare` restores exact source
domains, including unused parameters, with all body and image guards.
Each fixed-rank call terminates and completed results are fuel-stable. These
internal interfaces do not yet decide when to stop increasing the rank, do not
cover arbitrary partial ambient bounds, and are not the public scheme checker.
Finite forgetting-machine criteria preserve shared outputs, monotonicity, and
constant boundaries; general comparison still requires a complete bound on the
machines synthesized from the input. Exact raw-token abstraction preserves the
same admissible substitution and original guards for partial ambient bounds.
`ComparisonNormalizedAmbientDriver` conservatively removes reflexive ambient
edges while preserving names and fresh indices. Its results are certified under
the original context; an unused partial annotation no longer prevents the
reflexive ambient comparison from succeeding.
See [TODO.md](../TODO.md) and [LEAN_PROOF_HANDOFF.md](../LEAN_PROOF_HANDOFF.md).

`runSolver_correspondence` and `principal_factorization` establish the exact
named contracts in `Obligations`. Optional closed-term syntactic
substitution also remains an unproved contract; semantic soundness uses environments.

The development does not prove an operation-count bound for the whole pipeline
outside its verified concrete modality phase. Borrowing, references as
language constructs, concurrency, local let-polymorphism, a parser, and compiler
integration are outside this core. Current proof tasks and interfaces are tracked
in [TODO.md](../TODO.md) and [LEAN_PROOF_HANDOFF.md](../LEAN_PROOF_HANDOFF.md).
