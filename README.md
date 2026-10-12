# First-class modalities: Lean specification and prototype

This library covers the corrected core calculus in Sections 3–5 of *First-Class
Modalities in OxCaml*, including the POPL response's **closed-RHS restriction on
polymorphic `def`**. It contains independent declarative judgments, concrete
semantic definitions, executable algorithms, and constructor-based examples.

**Proof status:** the original generic modality solver and the evaluator's
soundness, completeness, determinism, and fuel stability are proved. The semantic
interpretation's global-reference and empty shared-support properties are also
proved, including nested fields and polymorphic closure captures. Annotation
erasure preserves evaluation and the runtime structure of results. Every
declarative subtyping rule preserves the interpretation and decreases ownership,
with symbolic bounds and partial-modality definedness accounted for. The Boolean
reduction is also proved: successful backend reports characterize validity
under every Boolean valuation, through polarity-aware CNF normalization and an
explicit identifier-to-`Fin n` translation to the original solver. Modality
projection is proved for all operations, preserving residual definedness and the
reversed uniqueness comparison. Backend modality entailment agrees with
`ModeModels`, and positive inequality reports yield the independent `Submode`
judgment. Full scheme subsumption still has separate proof obligations.
Full-system metatheory remains incomplete: deferred theorem statements use isolated `sorry`s under
`ModalityInference/Proofs/`. Neither the public library nor the executables nor the
original solver import those files. An executable acceptance report is data,
not a kernel-checked proof of scheme subsumption.

**Known semantic defect:** `Proofs/PolymorphicCapture` proves that the current
fundamental semantic soundness statement is false. Scheme instantiation changes
the result type without transporting the closure's symbolic capture metadata.
The false assertion has been replaced by the proposition `Deferred.SemanticSoundness`;
repairing the semantics and proving the corrected theorem remain required.
`Annotations` now provides `Value.substTypes`, which transports substitutions
through captured values, capture schemes and closure bodies. Its runtime
preservation properties and the repaired captured-credit witness are proved;
integration into polymorphic elaboration and the fundamental theorem remains open.
`Value.substCapturedTypes` now follows each captured scheme's own binder renaming,
and `SchemeValue.subst` transports a scheme and its value together. These operations
preserve runtime structure, references and liveness; evaluation is preserved up to
annotation erasure. The nested witness in `Proofs/ScopedCaptures` checks why uniform
transport is insufficient when a captured scheme itself quantifies variables.
`SchemeValue.instantiate` now applies ordered type and modality arguments to both
the scheme and its value, retaining definedness guards even for unused arguments.
Its substitution-domain and erasure contracts are proved, as is the unique-credit
witness after instantiation. This operation generates bounds for the caller to
discharge; it is not yet integrated into `infer` or `evalFuel`.

An alternative repair is under development in `ResourceSemantics`: ownership
evidence accompanies each ground instance of a value, instead of reading
authoritative ownership from symbolic runtime annotations. Credits and product
cells still own their location exactly when unique; fields retain their complete
types, and a closure must account for its result using captured, argument, or
fresh resources. A scheme reserves enough resources for every admissible instance.
`Proofs/Resources` proves annotation-erasure invariance with the same ownership
set, global-reference preservation, empty ownership for many aliased values, and
semantic lookup. `Proofs/ResourceCapture` proves that the recorded polymorphic
counterexample satisfies this lookup contract with the original runtime closure.
`Proofs/ResourceSubtyping` now proves that every declarative subtyping rule
transports this ownership evidence to a subset of the source resources, under
arbitrary modeled bounds and inherited modalities. The proof includes both
function variances, future-only closure comparison, credit conversion, and
pairwise separation of product cells and fields.
`Proofs/GroundAssignment` proves that fresh quantified instantiation preserves
ambient bounds and lock expressions. `Proofs/ResourceContexts` uses that result
to prove polymorphic sharing with empty ownership and the complete context-join
contract: both component environments are valid, own subsets of the original
resources, and have disjoint ownership. `Deferred.context_join_semantics` now
uses this proved contract in place of its annotation-dependent admission.
The same module proves semantic locking: each retained polymorphic binding
satisfies its captured type within its original reserve, separation is preserved,
and the locked context owns a subset of the original resources.
`Deferred.locking_semantics` now uses that proved resource contract.
This route changes no term constructor or evaluation rule. Its connection to all
declarative typing rules remains unfinished; it is not yet a replacement
fundamental soundness theorem.

**Intermediate type correction:** typing now checks definedness when introducing
a variable instance, a unit modality, a lambda's domain and outer modality, or an
unused sum branch. `Proofs/TypingDefinedness` proves that every typed result has a
ground realization under modeled bounds, by induction over all typing rules.
It also proves that all ordinary source types satisfy these guards automatically.
`Proofs/UndefinedDomain` records the former rules' counterexample: with the
undefined residual `r = top / bottom`, a binding of type `(unit@r) → unit` could
be interpreted by the unit value, because that function type has no ground
realization. The old rules typed `x () : unit`, which the evaluator rejects as an
application of a non-function. The corrected rules reject the invalid function
type in every context. All term constructors and closed-RHS `def` are retained.

**Constraint definedness correction:** entailment of subtype and type-equality
constraints now requires definedness of their type operands. Reflexive subtyping
alone does not establish satisfaction of an undefined constraint.
`Proofs/UndefinedBounds` archives the earlier entailment and the resulting
`x ()` counterexample: the bound `unit@r ≤ unit@r`, where `r = top / bottom`,
has no ground instance but was discharged by reflexivity. Even a fully defined
function body type then accepted a non-function value vacuously. The new rules
reject this bound under every instantiation and as a closed-definition
consistency witness. Lean proves the guards automatic for ordinary source
subtyping and both forms of type equality. Equality elimination in the solver
and abstract rewriting now retains the substituted type's definedness guards;
regressions cover undefined and defined images, including nested function types.

`Proofs/GroundSubtyping` now proves that every declarative subtyping rule
preserves ground subtyping and that constraint entailment preserves all modeled
bounds. `Proofs/GroundInstantiation` constructs a ground scheme instance from
every syntactic instantiation with satisfied bounds and a defined result. It
preserves all non-quantified identifiers, including skolems, and does not require
unused substitution images to be defined. The variable lookup theorem now follows
from these actual declarative premises, with its resource bound. A separate
proved corollary shows that `BoundsSatisfiable` supplies a genuine ground model
for the closed-definition rule. These are ingredients of the still-unfinished
fundamental theorem, not a complete typing induction.
`Proofs/GroundSchemes` proves that the resource interpretation of a scheme depends
only on its free identifiers, while retaining the full quantified-domain condition
on each instance. `Proofs/ResourceWorlds` transports values, schemes, and
environments between worlds when their actual references remain live, preserving
exact ownership sets. `Lock.resource_many_semantics` strengthens semantic locking
for reusable closures: every retained binding admits an empty resource reserve,
uniformly across its polymorphic instances. Closure construction and the full
typing induction still require further work.

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
  The new projection/normalization/reduction proofs remain deferred.

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

`GroundTy`, `ValueInterpretation`, `GroundInstantiates`,
`SchemeInterpretation`, `EnvironmentInterpretation` and `SemanticEvaluation`
are concrete definitions, not interpretation axioms. `Owns` depends on the full
type and composes inherited modes with each field's own annotation. Closures
retain typed capture schemes; ownership is the union over their admissible
instances. `References` separately includes aliased locations. Separation uses
ownership; world validity uses references. `firstOrderSupport` is executable on
first-order values and intentionally does not guess an instance for closures.

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
| §3 semantic interpretation, typed support, separation and liveness | `Semantics` | Concrete definitions; metatheory deferred |
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
| Explicit value instantiation | `Annotations`, `Proofs/Instantiation`, `Proofs/ScopedCaptures` | Ordered arguments transport metadata; proved instantiation, definedness-guard and erasure contracts; integration with typing and evaluation remains open |
| Subtyping substitution | `Proofs/PartialSubstitution` | Proved with explicit definedness of modality images, and for all ordinary modality images; proved counterexample to the former unrestricted statement |
| Term scope | `Proofs/Scoping` | Proved capture-avoiding substitution and renaming preserve scope for every term constructor; no admissions |
| Context routing and lookup | `Proofs/Generation` | Proved usage splitting and both directions of symbolic lookup correspondence; no admissions |
| Declarative weakening | `Proofs/Declarative` | Proved context weakening for annotated and raw typing; no admissions |
| Well-formed intermediate types | `Proofs/TypingDefinedness`, `Proofs/UndefinedDomain` | Proved ground definedness for every typing rule and automatic guards for ordinary source types; retained and excluded the former undefined-domain counterexample |
| Ambient assignment and quantified scope | `Proofs/Grounding`, `Proofs/ContextScoping` | Scheme instantiation fixes all non-quantified identifiers; proved monomorphic contracts and a witness requiring fresh quantifiers in sharing/locking |
| Ambient skolem scope | `Proofs/SubsumptionScope` | Proved the former comparison could confuse an ambient rigid identifier with a new quantifier; corrected skolem indices avoid every ambient type and modality identifier |
| Ownership evidence for ground instances | `ResourceSemantics`, `Proofs/Resources`, `Proofs/ResourceCapture` | Candidate semantic repair; proved erasure invariance, global references, empty shared ownership, semantic lookup, and the original captured-credit witness; full typing connection remains open |
| Resource interpretation under subtyping | `Proofs/ResourceSubtyping` | Proved all declarative subtyping rules preserve instance-indexed interpretation while shrinking ownership, including symbolic bounds and arbitrary inherited modalities; no admissions |
| Semantic context joins | `Proofs/GroundAssignment`, `Proofs/ResourceContexts` | Proved fresh ground instantiation, empty ownership for polymorphic sharing, and valid, contained, disjoint component environments for every join rule |
| Polymorphic capture diagnostic | `Proofs/PolymorphicCapture` | Proved counterexample to the current fundamental statement; no admissions |
| Remaining structural, semantic and algorithmic metatheory | `Proofs/Structural`, `Proofs/Soundness`, `Proofs/Algorithms` | Explicit admitted obligations |

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
Only `import ModalityInference.Proofs` brings the admitted theorem worklist into
an environment. Tests do not import it. The audit scans source imports and also
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

The 99 regression checks also compare small two-mode queries and all concrete mode
comparisons against exhaustive valuation checking before accepting backend results.
They exercise every term constructor and both sum branches.

## Deferred proof work and prerequisites

Each of the 20 remaining deferred theorems has a prerequisite comment immediately above it.
The fundamental semantic soundness claim is separately recorded as a proposition:
its current formulation is refuted, so it cannot responsibly remain an admitted theorem.
These are obligations to prove and, if counterexamples arise, refine; the
prototype and stated theorems are not advertised as a verified full system.

`GroundInstantiates` fixes every identifier outside the quantified domain, including
ones absent from a scheme's body and bounds. This preserves the interpretation of
ambient identifiers used only by capture metadata. Sharing and locking now require
scheme binders fresh for ambient bounds, and locking additionally requires them
fresh for its symbolic modality. The checked counterexample uses the ambient
bound `aliased ≤ μ₀` with the separately quantified scheme `∀μ₀. credit@μ₀`:
the former sharing premise holds but both components own the same credit at a
unique instance. `ContextScoping.renamed_fresh` verifies that alpha-renaming makes
the scope valid while retaining polymorphism. These scoping repairs do not resolve
the distinct variable-instantiation metadata defect below.

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
assignment. This is a checked repair witness, not a proof of the full system.

A second capture witness tests nested polymorphism. Substituting into a closure
that captures `∀μ₀. unit → credit@μ₀` renames that capture scheme's binder to `μ₁`.
Uniform annotation mapping leaves the nested captured value's credit annotated
with `μ₀`. `substCapturedTypes` transports that value using the scheme's exposed
`substitutionAction`, so its annotation becomes `μ₁` too. The example proves both
the difference in annotations and equality of runtime structure after erasure.
These mechanisms remain prerequisites for integrating polymorphic instantiation
into elaboration and proving the corrected fundamental theorem.

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
| `Soundness` | Semantic soundness, termination/no-stuck, live results, ownership bound | Structural lemmas, fresh supply partitioning, region liveness, closure interpretation and closed-definition generalization; semantic subtyping and support monotonicity are proved |
| `Algorithms` | Local rewrite equivalence, solution preservation, scheduled termination, worklist correspondence, solve soundness/consistency/completeness, principal factorization, generation correspondence/soundness/completeness, closed-definition generalization, elaborated inference soundness and completeness, backend reduction, scheme-subsumption soundness/completeness | Guarded residual adjunctions, substitution invariants, freshness, representative-search completeness, rigid entailment, Boolean projection/CNF correctness, modal witness reconstruction, established `Equation.decide_correct` |

Completeness statements require a sufficiently large fuel budget. Rewrite
expansion requires distinct flexible variables fresh for the complete original
constraint, pending/residual constraints and accumulated substitution. Subsumption
statements require distinct scheme parameters and residual declared bounds.
Rewrite termination is a separate obligation from the already-proved generic solver
stabilization theorem. The paper's operation-count discussion is not a Lean cost
model, and the finite search/CNF prototype may take exponential time or space.

Borrowing, references as language constructs, concurrency, local let-polymorphism,
a parser/CLI and compiler integration remain future work.
