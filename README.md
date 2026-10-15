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
| `checkSubsumption fuel inferred declared` | Executable scheme-comparison evidence; the checker has known mismatches with `Subsumes` and no soundness or completeness theorem |

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

Additional symbolic components support the structural checker replacement.
`SymbolicModes.eliminate flexibleAtoms formula` returns an optional symbolic
witness and residual obligation for its exact accepted Horn grammar;
`SymbolicModes.Elimination.mode` optionally reifies a witness as a defined
`ModExpr`, and `SymbolicSchemeModes.assemble` collects the images into a finite
substitution. `SchemePreparation.prepare ambient source target` returns fresh
source obligations, a separate body comparison, and expanded target assumptions.
Preparation and internal interpolation do not return a subsumption decision
and have not replaced the checker's type search. Modality-image assembly is
used with the general uniform synthesis procedure.

`CompareTy` is a separate finite witness language with binary joins and meets.
`ShapedSubsumes` restricts its instantiations and intermediate subtype derivations
to compatible shapes under the declared assumptions; public `Ty` and `Scheme`
remain join-free. The original subtype and scheme relations embed into it.
`ComparisonInterpolation.witness` reconstructs an isolated variable
from its lower or upper endpoints, with an exact crossed-bound criterion and
preservation of written guards in the unrestricted comparison relation. Its
shape-restricted lift and structural/modalized occurrences remain separate work.
The source typing and semantic theorems still use the original scheme relation.

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

The executable scheme checker still uses `checkCandidates` for type
representatives. Its Boolean assignment expansion is replaced by verified
uniform symbolic synthesis. Replacing type search is [TODO item 1](../TODO.md).
Integration must preserve fixed identifiers, retain original rigid type
obligations, and construct admissible internal type images satisfying the
original scheme goals. Correct modality synthesis alone does not prove the
rigid graph or complete checker correct.

`SchemePreparation.reconstruct_sound` proves the final bridge once supplied an
action that fixes the original identifiers and solves the prepared guarded bounds
and unguarded body comparison. It does not supply the action itself.
The comparison witness for crossed rigid bounds can use an internal join;
`ComparisonInterpolation.exists_interval_iff` proves exact reconstruction for
isolated lower/upper bounds. Global reduction must also handle structural cycles
and modalized occurrences without assuming constructor or modality distribution
laws absent from `CompareSubtype`. Returning unresolved constraints is a reduction
API, not a successful comparison decision. `ShapedSubtype` and `ShapedSubsumes`
require joins/meets to have compatible shapes under the declared assumptions,
including all intermediate comparison types. Ordinary derivations embed, shape
preservation is proved, and mixed-constructor witnesses are excluded. The ground
semantic bridge and complete structural reduction remain separate obligations.

The current checker can also instantiate unquantified flexible identifiers,
omits expansion of target assumptions, and requires body definedness beyond
declarative `Subsumes`. It accepts a fixed free type variable against `unit` and
rejects reflexivity for an undefined body, contrary to the corresponding proved
declarative results in `Proofs/SchemeReconstruction`. Both examples satisfy the
soundness and completeness contracts' duplicate-free-quantifier and residual-target
premises. Those contracts require implementation repairs, not additional scope
restrictions. Correctness of the Boolean validity solver alone does not establish
correctness of the scheme checker.

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
