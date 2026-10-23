# Finite mixed-comparison certificates

The finite diagram construction supplies a separating model for a failed
**fixed** comparison under mixed raw type bounds, assuming there is no finite
shape model. Executable encodings and local validators are now proved. The
remaining implementation target is to assemble them into one finite certificate,
prove extraction and validation together, and connect the fixed-endpoint query
to the symbolic backend.

This is a reference encoding and integration plan. The production intent in
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
checked machine and the outer model. Control, atom, unit, and credit ties are
explicit premises; the assembled certificate must construct them, not assume
them without validation or definition. All enumeration lists require proved
coverage of their respective finite types.

## Remaining assembly and public integration

A certificate should contain checked machine descriptions, finite control/tag/
observation indices, the embedding matrix, ordinary and literal-prefix row
lists, frozen arrays, and the defined embedding table. Assemble the existing
local checks into a single executable validator and a syntax evaluator. Validate
every **original whole raw subtype bound** in the outer interpreter. The inner
machine only checks `shapeShadow Δ`; it need not satisfy the original partial
bounds. Primitive agreement and these outer checks then give all-rule soundness.

For the next assembly step, keep `D` literally `FiniteRange.Value` of the
checked description and enumerate it with `RangeEncoding.values`. Store `j`
using raw bit-vector keys composed with `pack`. Validate on finite control
codes, construct `Valid.embedding`, and compose with the inverse control
`orderIso` coordinate map to obtain the semantic-control embedding. Transfer
shift and constructor laws using `coordinates_shift`, `coordinates_pair`, and
`coordinates_fn`. Define atoms, unit, and credit from this embedding, avoiding
an infinite atom check. Frozen arrays also need a finite control-monotonicity
check before they can inhabit `Coordinates`.

Two small assembly adapters can keep this step local. First construct a
`ControlMap` on finite codes using projected lookup, with Boolean function
order `order m (n * top)`; transport its laws through `decode_project` and the
order/monoid equivalences. Second transport a whole `RelativeSyntax.Model`
through a control order equivalence preserving multiplication and identity.
Its tables use `TableTransport`, its base/frozen coordinates use `coordinates`,
and its control lookup uses the inverse equivalence. Prove denotation
commutation once, including exact frozen lookup. The existing finite embedding
checks then transfer into the semantic-control `DefinedAgreement` without
re-proving the algebra rules.

Prove that the query-preserving constructed model serializes to an accepted
certificate and that serialization preserves both selected endpoint values.
The ingredients are proved separately; a theorem combining them with the
single certificate format is still required. The raw/raw, defined/defined,
and both mixed reflection theorems remain the completeness source. Arbitrary
partial lattice query terms are outside that reflection interface.

Then implement the fixed-endpoint decision/refutation query and connect it to
the symbolic backend and the finite-shape branch. Neither these encodings nor
fixed-endpoint separation bound the structural rank of an unknown substitution.
The independent input-only stopping argument and the public comparison
contract remain unfinished; see
[`comparison-stopping-bound.md`](comparison-stopping-bound.md).
