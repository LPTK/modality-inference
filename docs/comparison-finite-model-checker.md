# Finite mixed-comparison certificates

The finite diagram construction now serializes separating models into an
executable `ComparisonFiniteCertificate.Candidate` accepted by its Boolean
validator. Accepted separation refutes the original comparison under arbitrary
raw type bounds. Conversely, for a **fixed** comparison with raw or defined
internal endpoints, absence of a finite shape model makes non-subtyping
equivalent to existence of an accepted separating certificate within computable
input-derived carrier and control-name bounds. The lookup keys, machine name
tables, and constructor row lists also admit bounded representations preserving
the selected queries. A symbolic finite-certificate query, terminating
certificate search, and public integration remain unfinished.

This documents the reference encoding and its integration boundary. The
production intent in
[`TODO.md`](../../TODO.md) remains symbolic elimination and propagation, with no
exhaustive Boolean valuation expansion or rigid-representative search. Reference
finite enumeration establishes effective presentation; it is not a replacement
for the intended production solver.

## Executable scalar decisions and finite controls

`ScalarDecision` supplies total `defined` and `submode` Boolean decisions using
the existing symbolic backend. A structural budget bounds CNF normalization;
the proof guarantees a successful validity report, including negative answers.
No valuation enumeration or proof-valued search supplies these decisions.

`ComparisonControlForms` exposes the existing finite total-control syntax
family without importing proof modules. Its bridge is exact syntax equality,
so the established totality, support, completeness, and size theorems transfer.
`ComparisonFiniteControlEncoding` removes semantically equivalent labels using
the symbolic decisions. A control is a finite list index; equality, order,
identity, composition, top, and lookup are executable. The decode proofs give
an order and monoid equivalence with `ComparisonFiniteControls.Control`.
Lookup's fallback is unreachable for a total supported label. Projected lookup
replaces names outside the boundary by identity before normalization, matching
`ComparisonFiniteControlProjection`; it does not assert that an unsupported
label is globally equivalent to its projection.

The representative family can be very large. Its role here is a finite
reference control presentation, while scalar order/equivalence already use
symbolic elimination.

## Checked machines and finite range values

`ComparisonObserverRangeDescriptions.finite_rows` chooses finite machine data
through `MachineSerialization.bounded_descriptions_on`. It retains the complete
query pattern at one shared state per source observer, checks the description
for the shadow-row context, and checks the same data for `shapeShadow Δ`.
Mode transport supplies `ModalValid`, `RangeClosed`, and `Coherent` for the
original scalar assumptions.

`ComparisonObserverShadowQueryDescriptions.exists_realization` rebuilds the
optional cuts from these checked descriptions. It returns the same bounded
realization and query-coverage interface, plus the actual description and the
machine equality needed by serialization. No converse from arbitrary
`Certified` to `Coordinates` is assumed.

`ComparisonObserverRangeEncoding` represents range values by Boolean vectors
on the finite state indices. It enumerates exactly the vectors admitted by the
range flags and proves an order equivalence with `FiniteRange.Value`.
Executable unit, credit, atom, modal, constructor, join, meet, and term
operations agree with the semantic operations. Modal admittedness requires a
total label and range closure. The `values`/`all_values` adapter enumerates the
semantic range values directly using proof-erased admittedness witnesses, so
finite embedding checks need no noncomputable `Fintype` instance.

## Row tables, coordinates, and syntax

`ComparisonExecutableTables` stores indexed constructor rows and checks every
row pair for compatibility with the Boolean index order and argument variance.
Full observation coverage makes the finite vector order exact. A successful
check constructs a semantic `IndexedTable`; the executable extension agrees
with its semantic extension at every input. `TableSerialization` proves that
every finite semantic table has such a row-list presentation.

`TableTransport` renames controls, tags, and observations through equivalences
without dropping rows. `ExecutableCoordinates` gives the corresponding
order-reflecting lattice map and proves compatibility with shifts and pair and
function operations. The function proof requires the control renaming to
preserve identity, since function inputs are read at that coordinate.
`ExecutableCoordinateOperations` evaluates the finite row extension directly
while preserving monotone-coordinate invariants; its proof fields erase.
`ExecutableModelTransport` transports the whole model through a control order
equivalence preserving multiplication and identity. `ExecutableObservationTransport`
renames tags and observations. Both preserve denotation and reflect `Related`,
including exact first-matching-key frozen lookup.

`ComparisonExecutableSuffix` uses a supplied Boolean totality test and
preserves the exact literal partial prefix. `ExecutableSyntax.Data` supplies
executable operations and finite frozen lookup. Agreement with the semantic
interpreter requires totality and control correctness only on the finite lists
`totalTests` and `controlLabels`. `ExecutableScalarSyntax` discharges the
totality side with `ScalarDecision.defined`.

`ComparisonExecutableFamilies` serializes the literal-prefix family as a
finite list with empty-table default. For the constructed model this family is
exactly the original one, including all unlisted prefixes. Frozen values use
the same first-matching-key lookup; mapping stored values preserves that
behavior, including duplicate keys. No reassociation through a partial label
is introduced.

## Defined embedding checks

`ComparisonExecutableAgreement` checks a supplied finite table
`j : D → M → O → Bool`. Its finite loops exactly characterize:

- monotonicity in controls;
- preservation of defined joins and meets;
- reflection of the defined order;
- commutation with control shifts;
- product, sum, and function agreement on every pair of defined values.

The proofs construct a lattice homomorphism into monotone coordinates and
`RelativeSyntax.DefinedAgreement` when the supplied operations match the
checked machine and the outer model. The assembled `Candidate` constructs
control, atom, unit, and credit ties by definition. Its `CodeDefinedAgreement`
transfers through the control order equivalence to the semantic agreement used
by the all-rule soundness theorem. `ExecutableAgreementEncoding` also transfers
agreement in the reverse direction and through tag/observation renaming for
serialization. All enumeration lists have proved coverage of their respective
finite types.

## Validator, serialization, and endpoint completeness

`ComparisonFiniteCertificate.Candidate` contains machine descriptions,
finite state/tag/observation counts, an embedding matrix, ordinary and
literal-prefix row lists, frozen arrays, and a defined embedding table keyed by
raw state vectors. Controls use `FiniteControlEncoding.Code`. The executable
validator combines these checks:

- `structureCheck` checks support of context modality names, the machine on
  `shapeShadow Δ`, all ordinary and literal row tables, the defined embedding,
  and monotonicity of every frozen array.
- `boundsCheck` checks every **original whole raw subtype bound** in the outer
  interpreter. The inner machine need not satisfy the original partial bounds.
- `check` combines both checks; `separates a b` additionally checks that the
  interpreted endpoints fail the coordinate inequality.

The embedding is checked on exactly the admitted vectors of the machine and
then interpreted on `FiniteRange.Value`. Atoms, unit, and credit come from this
embedding, so no infinite atom check is needed. Projected control lookup and
finite code multiplication supply the actions. Ordinary and literal-prefix
tables retain their exact defaults, and functions use the future-control
relation and contravariant domain rows.

`ComparisonFiniteCertificateInterpretation` proves that the actual executable
syntax evaluator agrees with the semantic code model for every syntax term and
prefix. `ComparisonFiniteCertificateSoundness` proves `Candidate.algebra_sound`
for every original algebra rule and `Candidate.separates_sound`: an accepted
separating certificate implies `¬ AlgebraSubtype Δ a b`. These results allow
arbitrary raw subtype assumptions in `Δ` and arbitrary `CompareTy` endpoints;
they require neither endpoint `DefinedUnder` guards nor the no-finite-shape-model
hypothesis.

`Serialization.Source` in `ComparisonFiniteCertificateSerialization` packages
a described machine, finite model, finite literal-prefix support, exact table
relations, and the defined agreement needed to serialize it. `Source.candidate` passes
`structureCheck`; `Source.eval_eq` preserves every endpoint denotation at every
prefix, including frozen lookup. `Source.checked_of_bounds` supplies acceptance
from the original outer bounds, and `Source.separates_of_not_related` transfers
semantic separation to the Boolean checker.

`SourceConstruction.exists_source` in `ComparisonFiniteCertificateSource`
presents the constructed finite model on code controls and finite
tag/observation indices while preserving `Related` for every pair of terms.
`ComparisonFiniteCertificateQueries` chooses a query-preserving realization
with its checked machine description and proves all four reflection forms.
Together these give the following theorems in
`ComparisonFiniteCertificate.Completeness`, each equating non-subtyping with
`∃ names, ∃ C : Candidate Δ names, C.separates a b = true`.
The same-named theorems in `ComparisonFiniteCertificate.BoundedCompleteness`
strengthen the certificate side with `WithinDimensions raw queries C`, using
the input lists shown below:

| Theorem | Endpoints `a` / `b` | Endpoint hypotheses | Bound inputs `(raw, queries)` |
| --- | --- | --- | --- |
| `raw_non_subtype_iff` | `Ty` / `Ty`, embedded by `ofTy` | None | `([a,b], [])` |
| `defined_raw_non_subtype_iff` | `CompareTy` / `Ty` | Left endpoint `DefinedUnder Δ` | `([b], [a])` |
| `raw_defined_non_subtype_iff` | `Ty` / `CompareTy` | Right endpoint `DefinedUnder Δ` | `([a], [b])` |
| `defined_non_subtype_iff` | `CompareTy` / `CompareTy` | Both endpoints `DefinedUnder Δ` | `([], [a,b])` |

All four equivalences assume `¬ ∃ ρ, ComparisonShape.Models Δ ρ`: the original
context has no finite shape model. Raw endpoints may be partial. The guards on
internal endpoints are essential to the proved reflection interface; these
theorems do not cover arbitrary partial internal lattice terms.

## Computable bounds and canonical representations

`ComparisonFiniteCertificateBounds` defines the bounds from the original
context, raw endpoints, and internal queries. Its definitions use finite syntax
and arithmetic, independently of the choices used in the existence proofs.
`inputModes` contains only modality names occurring in those inputs.
`inputNodes` bounds the retained heads, including the query-support markers.
The control-name list has length at most
`nameBound = (1 + 2 * inputNodes) * inputModes.card` and contains only names in
`inputModes`. A list of length `n` has at most
`controlBound n = 2^(2^n + 2 * 2^(2*n))` representative controls;
`controlsBound` applies this estimate to `nameBound`.

`Proofs/ComparisonFiniteCertificateBounds` bounds the actual query-preserving
realization by `stateBound`, which accounts for the scalar names and the entire
finite diagram. For a realization with `s` states and `h` heads, the defined
range has at most `2^s` values and the head/control point carrier has
`h * (labels Δ names).length` elements. `ComparisonFiniteCertificateDimensions`
therefore bounds the tag count by their sum and the observation count by the
number of subsets of those tags. The input-only estimates are
`tagsBound = 2^stateBound + inputNodes * controlsBound` and
`observationsBound = 2^tagsBound`. `WithinDimensions` records the name support
and the name, state, tag, and observation bounds used by the four bounded
completeness theorems.

The remaining certificate fields have separate representation theorems:

- `ComparisonExecutableSyntaxSupport` computes the exact interpreter accesses,
  including normalized literal prefixes and frozen keys.
  `Candidate.restrictQueries` retains the keys needed by every original raw
  subtype bound and the supplied query family. It preserves those evaluations,
  bound checks, acceptance, and separation at selected endpoints. The literal
  and frozen table lengths are bounded by the corresponding input-derived key
  lists; first-matching-key behavior is preserved.
- `ComparisonObserverMachineRestriction` reindexes a description by copying
  atom and mode lookups into chosen name lists. Applied with
  `inputTypes Δ queries`, `Candidate.restrictMachine` uses these fixed type
  names and `names` for mode names, with exactly one table entry per listed
  name. It preserves the range and
  constructor data, all supported actions and atom lookups, the checked shadow
  machine, and the original bounds and selected queries. No arbitrary fresh
  machine names or excess table entries are needed.
- `Candidate.canonicalizeRows` enumerates the finite row universe and retains
  exactly the rows present in each original table. Every ordinary and literal
  table then has length at most `(labels Δ names).length * tags^3`.
  All evaluations and Boolean checks are unchanged, including functions and
  literal-prefix lookup.

`Candidate.canonicalize` composes machine restriction, query-key restriction,
and row canonicalization. `canonicalize_canonicalFor` proves all fields of
`CanonicalFor`; `canonicalize_check` and `canonicalize_separates` preserve
acceptance and selected separation, and `canonicalize_withinDimensions`
preserves the original dimension bounds. Combining these facts into canonical
versions of the four completeness equivalences remains an interface task.

These are bounds on reference certificate dimensions and representations.
They do not give a practical complexity estimate or implement the symbolic
solver that must consume those representations.

## Remaining algorithmic obligations

The input-derived dimension bounds and representation reductions are proved.
The fixed-endpoint mixed-context finite-certificate query still needs a symbolic
encoding, a terminating decision or search procedure with proved correctness,
connection to the public backend, and integration with the finite-shape branch.
Neither bounded certificate completeness nor fixed-endpoint separation bounds
the structural rank of an unknown substitution. The independent input-only
stopping argument and the public comparison contract remain unfinished; see
[`comparison-stopping-bound.md`](comparison-stopping-bound.md).
