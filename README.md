# First-class modalities: Lean specification and prototype

This library covers the corrected core calculus in Sections 3–5 of *First-Class
Modalities in OxCaml*, including the POPL response's **closed-RHS restriction on
polymorphic `def`**. It contains independent declarative judgments, concrete
semantic definitions, executable algorithms, and constructor-based examples.

**Proof status:** the original generic modality solver and the evaluator's
soundness, completeness, determinism, and fuel stability are proved. The semantic
interpretation's global-reference and empty shared-support properties are also
proved, including nested fields and polymorphic closure captures. Annotation
erasure preserves evaluation and the runtime structure of results. Full-system
metatheory is deferred: its theorem statements use isolated `sorry`s under
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
| §5 future/past projection and `Fin n` normalization | `ModeBackend` | Executable bridge to established solver |
| §5 generic concrete modality solver | `Subsumption` | **Existing proved correctness and stabilization, unchanged** |
| Core programs and regressions | `Examples`, `Regression` | Executed during validation/CI |
| Evaluator metatheory | `Proofs/Evaluation` | Proved soundness, completeness, determinism and fuel stability; no admissions |
| Interpretation properties | `Proofs/Interpretation` | Proved global references and empty shared ownership; no admissions |
| Annotation erasure | `Proofs/Erasure` | Proved for all evaluation rules and capture trimming; no admissions |
| Recursive annotation transport | `Annotations`, `Proofs/Annotations` | Executable value substitution; proved evaluation, erasure, reference and freshness preservation |
| Simultaneous substitution | `Proofs/Substitution` | Proved composition for types and modality expressions, including overlapping substitution tables; no admissions |
| Term scope | `Proofs/Scoping` | Proved capture-avoiding substitution and renaming preserve scope for every term constructor; no admissions |
| Context routing and lookup | `Proofs/Generation` | Proved usage splitting and both directions of symbolic lookup correspondence; no admissions |
| Declarative weakening | `Proofs/Declarative` | Proved context weakening for annotated and raw typing; no admissions |
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
| Cycles and occurs checks | Benign mode cycle succeeds; direct and indirect recursive type bounds reject |
| All target quantifiers skolemized; assumptions retained | `polyId` versus a monomorphic identity; `bounded` with/without its declared assumption |
| Allocation source, exclusive upper index and future-frame partition | Tail slices start at 1 and 2; distinct branches enter distinct fresh frames |
| Typed ownership and separate reference validity | `aliasedField` inside a unique pair and a dead stack frame |
| Fuel is not rejection | Small-budget inference/evaluation exhaust; larger budgets succeed |

The 89 regression checks also compare small two-mode queries and all concrete mode
comparisons against exhaustive valuation checking before accepting backend results.
They exercise every term constructor and both sum branches.

## Deferred proof work and prerequisites

Each of the 25 remaining deferred theorems has a prerequisite comment immediately above it.
The fundamental semantic soundness claim is separately recorded as a proposition:
its current formulation is refuted, so it cannot responsibly remain an admitted theorem.
These are obligations to prove and, if counterexamples arise, refine; the
prototype and stated theorems are not advertised as a verified full system.

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

| Proof module | Obligations | Prerequisites/dependencies |
| --- | --- | --- |
| `Structural` | Subtyping substitution, closed term substitution, semantic context joins/locks | Freshening and alpha-renaming, scheme instantiation, type-indexed support and semantic subtyping; substitution composition, term scope, weakening, usage splitting and symbolic lookup are proved |
| `Soundness` | Semantic subtyping/support monotonicity, semantic soundness, termination/no-stuck, live results, ownership bound | Structural lemmas, fresh supply partitioning, region liveness, closure interpretation and closed-definition generalization |
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
