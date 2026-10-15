# First-class modalities in Lean

This library defines and implements the core calculus of *First-Class Modalities
in OxCaml*: functions, products, sums, closed polymorphic definitions, heap and
stack allocation, space-credit reuse, and regions. It provides independent typing
and evaluation judgments, executable inference and evaluation, and checked proofs
of source soundness, closed inference completeness, and ground principality.

The executable syntax is `RawTerm`; inference returns the input term unchanged.
`Runtime.Value.closure` stores a trimmed environment and a raw body. `SourceTyping`
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
| `checkSubsumption fuel inferred declared` | Internal comparison substitution and residual validity evidence; soundness and termination proved, general completeness unfinished |

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
body/image guards to source obligations before calling `ComparisonChecker.run`;
the declared assumptions and fresh skolem indices remain unchanged. Exact
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
Shared type and modality choices still require the joint assembly described
under remaining work below.

## Constraint solving

`solve` first runs the deterministic structural worklist in `Constraints`.
It normalizes types and modalities, checks finite constructor shapes, expands
forced type shapes with fresh variables, eliminates type equalities, and orients
residual and closure transformations by variable order. It retains symbolic
bounds and every required partial-expression definedness guard. Proved cache and
substitution invariants justify duplicate discharge and updates to saved images.

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
| Successful inference gives a `SourceTyping` derivation under returned residual bounds and the substituted context, with sound raw execution under the semantic premises | `Proofs/SourceInference` |
| Every declaratively typable closed source term is accepted with sufficiently large fuel; every successful result covers all its valid ground result instances up to subtyping | `Proofs/InferenceCompleteness`, `Proofs/SourceInference` |
| Solver output entails the original constraints after substitution and preserves acyclicity and definedness; flexible inputs have a ground model using the returned witness | `Proofs/SolverSoundness`, `Proofs/SolverImages`, `Proofs/ResidualModels` |
| Initialized solving terminates on every input; on flexible inputs it eventually accepts every satisfiable input and factors every original ground solution through every successful result | `Proofs/SolverTermination`, `Proofs/SolverCompleteness` |
| Actual generation and rewriting preserve the direct Horn domain; both consistency paths are sound, complete, terminating, and preserve successful results at larger budgets | `Proofs/PolarizedConstraints`, `Proofs/HornPropagation`, `Proofs/CNFPropagation`, `Proofs/ModeConsistency` |
| Symbolic Horn elimination has an exact accepted grammar, a uniform expression witness, an equivalent residual query, and no selected flexible atoms; supported modality images reify and assemble with the specified domain and definedness | `Proofs/SymbolicModes`, `Proofs/SymbolicSchemeModes` |
| Scheme preparation preserves scope and provides fresh source and target ranges; a solution of its prepared goals reconstructs an instantiation with exactly the source quantifier domain | `Proofs/SchemePreparation`, `Proofs/SchemePreparedScope` |

`SourceTyping.resource_semantic` retains the full interpreted open environment
and every admissible polymorphic instance. `inference_source_semantic` connects
the actual inferred term to that theorem under modeled residual bounds and an
interpreted substituted context. Ground principality concerns ground solutions;
it does not establish symbolic factorization under arbitrary residual assumptions.

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

`inference_source_defined` proves body and returned-substitution definedness
under the actual residual bounds. `SourceTyping.var` requires defined instances
including unused quantified parameters. Auxiliary context weakening transports
every admissible instance under those residual bounds. Converting its steps to
the paper's guarded scheme replacements remains a separate correspondence task.

`Obligations.SchemeSubsumptionComplete` remains unproved. Its premise is
`AlgebraSubsumesUnder`, retaining duplicate-free binders and residual target
bounds, without closedness, consistency, global totality, or a residual syntax
restriction. Preparation, shape solving, and structural normalization preserve
defined witnesses. Selector-parametric propagation and coordinate tuple
reification are proved components. Their assembly into uniform shared type and
modality reconstruction, and its connection to actual checker success, remain
unfinished. Pointwise coordinate feasibility does not establish one common type
witness. Non-residual declared bounds also lack a complete general procedure.
See [TODO.md](../TODO.md) and [LEAN_PROOF_HANDOFF.md](../LEAN_PROOF_HANDOFF.md).

`Obligations.RunSolverCorrespondence`, relating the complete structural worklist
to the abstract rewrite relation, and `Obligations.PrincipalFactorization`, the
stronger symbolic factorization theorem under residual ambient assumptions,
remain unproved. Local rewriting preservation and the executable solver results
above do not supply these missing statements. Optional closed-term syntactic
substitution also remains an unproved contract; semantic soundness uses environments.

The development does not prove an operation-count bound for the whole pipeline
or that its complete schedule is the paper's schedule. Borrowing, references as
language constructs, concurrency, local let-polymorphism, a parser, and compiler
integration are outside this core. Current proof tasks and interfaces are tracked
in [TODO.md](../TODO.md) and [LEAN_PROOF_HANDOFF.md](../LEAN_PROOF_HANDOFF.md).
