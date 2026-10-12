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

**The overall verification objective is still incomplete: 15 admissions remain.**
They are closed term substitution and 14 algorithmic obligations, including
solver correctness/completeness/principality, generation, elaborated
inference, and scheme subsumption. The public library and executables do not
import proof-worklist modules. The original generic solver is unchanged and its
correctness/stabilization results remain admission-independent. The audit checks
234 public or established declarations transitively, including the complete
fundamental theorem and all three soundness corollaries.

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

## Corrections and retained witnesses

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

`GenerationDefinedness` records a further algorithmic mismatch: the former
variable-inference path accepted an undefined function type, and a generated
unused lambda domain could later be replaced by an undefined type under a vacuous
solution. The corrected generator and independent `Generates` relation emit
reflexive type guards for lookup, lambda domains, and unused sum branches, plus
a definedness constraint for lambda modes. A type guard is retained as `a ≤ a`,
so it survives later type substitution; inspecting only the modalities already
written in a type variable would emit no guard. `Generates.definedUnder` proves
that every generated result is defined under every declarative solution, for all
constructors. The counterexamples and corrected rejection proofs are checked
without admissions. Full generation and inference soundness remain open.

Evaluator correspondence, determinism, fuel stability, Boolean CNF reduction,
and all-axis modality projection are also proved independently. Backend modality
entailment agrees with `ModeModels`; a positive inequality report establishes
`Submode`. An executable scheme-comparison report is still data pending the
remaining algorithmic proofs.

## Build and run

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
  indirect cycles), expands types, propagates bounds and applies guarded residual
  rewrites. Remaining symbolic projection obligations are retained, not dropped.
  Boolean CNF propagation checks their consistency. This finite fallback is part
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
| §4 constraint rewriting | `Rewriting`, `Constraints` | Independent relation and executable worklist |
| §5 scheme subsumption | `SchemeSubsumption` | Executable prototype; reduction correctness deferred |
| §5 future/past projection and modality entailment | `ModeBackend`, `Proofs/Projection` | Proved all expression projections, partial definedness, both flexible/rigid identifier encodings, bounds entailment and positive-query declarative soundness |
| Boolean normalization and solver reduction | `Proofs/Backend` | Proved truth preservation for both polarities, duplicate/tautology elimination, and validity equivalence of successful backend reports; no admissions |
| §5 generic concrete modality solver | `Subsumption` | **Existing proved correctness and stabilization, unchanged** |
| Core programs and regressions | `Examples`, `Regression` | Executed during validation/CI |
| Evaluator metatheory | `Proofs/Evaluation` | Proved soundness, completeness, determinism and fuel stability; no admissions |
| Interpretation properties | `Proofs/Interpretation` | Proved global references and empty shared ownership; no admissions |
| Semantic subtyping | `Proofs/Mode`, `Proofs/Subtyping` | Proved all declarative subtyping rules preserve interpretation, decrease ownership, and preserve definedness under modeled bounds; no admissions |
| Annotation erasure | `Proofs/Erasure` | Proved for all evaluation rules and capture trimming; no admissions |
| Recursive annotation transport | `Annotations`, `Proofs/Annotations` | Executable value substitution; proved evaluation, erasure, reference and freshness preservation |
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
| Remaining structural and algorithmic metatheory | `Proofs/Structural`, `Proofs/Algorithms` | 15 explicit admitted obligations |

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
| Definedness survives generation and later type substitution | `GenerationDefinedness`: former variable inference accepted an undefined function; an unconstrained lambda domain admitted a partial image; corrected guards reject both |
| Partial residual side conditions survive rewrites | Both undefined residuals reject, including inside type-variable bounds |
| Substitution updates residual bounds and previous images | `α = β; β = unit`; conflicting repeated assignments reject |
| Subtyping substitution requires defined modality images | `unit@μ ≤ unit@top` fails after substituting the undefined residual `top / bottom`; checked in `Proofs/PartialSubstitution` |
| Cycles and occurs checks | Benign mode cycle succeeds; direct and indirect recursive type bounds reject |
| All target quantifiers skolemized; assumptions retained | `polyId` versus a monomorphic identity; `bounded` with/without its declared assumption |
| Allocation source, exclusive upper index and future-frame partition | Tail slices start at 1 and 2; distinct branches enter distinct fresh frames |
| Typed ownership and separate reference validity | `aliasedField` inside a unique pair and a dead stack frame |
| Instantiation fixes every non-quantified identifier | `AmbientCaptureScope`: a variable absent from the scheme can still occur in capture metadata; changing it is rejected |
| Scheme binders are fresh for ambient bounds and symbolic locks | `ContextScoping`: the former sharing premise allows two copies of the same owned credit; alpha-renaming removes the bound/quantifier collision |
| Scheme-comparison skolems are fresh for ambient bounds | `SubsumptionScope`: under `unit ≤ rigid₁`, the former comparison incorrectly accepted `unit` as `∀α. α`; the corrected comparison chooses `rigid₂` |
| Fuel is not rejection | Small-budget inference/evaluation exhaust; larger budgets succeed |

The regression checks also compare small two-mode queries and all concrete mode
comparisons against exhaustive valuation checking before accepting backend results.
They exercise every term constructor and both sum branches.

## Deferred proof work and prerequisites

Each of the 15 remaining deferred theorems has a prerequisite comment immediately above it.
The former annotation-dependent fundamental claim remains separately recorded
as a refuted proposition. Its corrected resource formulation and corollaries are
proved for the whole core; this does not discharge the algorithmic obligations.
Each remaining statement must still be validated and proved, with any required
correction justified by retained evidence.

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
| `Structural` | Closed term substitution | Freshening and alpha-renaming, scheme instantiation and closure capture; substitution composition, subtyping substitution with defined modality images, term scope, weakening, usage splitting, symbolic lookup, instance-indexed context joins and locking are proved |
| `Soundness` | None: corrected fundamental soundness, termination/no-stuck, live results, and ownership bound are proved | Complete typing induction in `ResourceSoundness`, with resource semantics independent of capture metadata |
| `Algorithms` | Scheduled termination, worklist correspondence, solve soundness/consistency/completeness, principal factorization, generation correspondence/soundness/completeness, closed-definition generalization, elaborated inference soundness and completeness, scheme-subsumption soundness/completeness | Local rewrite equivalence, configuration solution preservation and backend reduction are proved; remaining prerequisites include substitution invariants, freshness, representative-search completeness, rigid entailment, Boolean projection/CNF correctness, modal witness reconstruction, established `Equation.decide_correct` |

Completeness statements require a sufficiently large fuel budget. Rewrite
expansion requires distinct flexible variables fresh for the complete original
constraint, pending/residual constraints and accumulated substitution. Subsumption
statements require distinct scheme parameters and residual declared bounds.
Rewrite termination is a separate obligation from the already-proved generic solver
stabilization theorem. The paper's operation-count discussion is not a Lean cost
model, and the finite search/CNF prototype may take exponential time or space.

Borrowing, references as language constructs, concurrency, local let-polymorphism,
a parser/CLI and compiler integration remain future work.
