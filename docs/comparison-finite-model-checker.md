# Finite mixed-comparison certificates

The next implementation target is a finite certificate for a failed **fixed**
comparison in an ambient context that may contain partial raw type bounds.
The finite diagram construction supplies the existence argument. A certificate
checker must inspect finite data, without deciding the original head order or
trusting the source diagram's cut predicates.

This is a reference encoding and proof plan. The production intent in
[`TODO.md`](../../TODO.md) remains symbolic elimination and propagation, with no
exhaustive Boolean valuation expansion or rigid-representative search. Finite
valuation and representative enumeration below establishes an effective finite
presentation; the production query should compile its obligations to the
existing Boolean backend rather than implement that enumeration as its solver.

## First API: executable finite controls

Add a reference `ComparisonFiniteControlEncoding` with a finite control type
and an order/monoid equivalence to `ComparisonFiniteControls.Control Δ names`.
Assume the retained names contain `Δ.modVars`.

1. Enumerate assignments of the retained names to the eight concrete modes,
   extending unlisted names by identity; retain the assignments satisfying the
   original scalar assumptions.
2. Evaluate each member of `ComparisonRawHeadModeOrbits.representatives names`
   on those assignments and deduplicate the resulting finite lists of modes.
3. Use distinct-list indices as controls. Order is pointwise `Mode.le`;
   multiplication is pointwise `Mode.compose`, followed by lookup. Identity and
   top have constant lists. `representatives_complete` proves lookup closure
   and coverage of every supported total label.
4. Export executable control lookup and proofs for identity, composition,
   submode, and the function relation `m ≤ n * top`. Restrict names absent from
   the input before encoding an arbitrary total annotation, as in the existing
   `ComparisonFiniteControlProjection`.

This finite presentation avoids putting functions on infinitely many scalar
worlds in a serialized certificate. Its symbolic replacement should reuse
`modeFormula`, `boundsModeFormula`, `ConcreteBackend.decideFormula`, and their
soundness/completeness theorems. The reference and symbolic representations
must agree before the latter is used by the public checker.

## Certificate data and finite checks

The certificate needs no source preorder, optional cuts, or subtyping proofs.
It contains:

- A finite `ComparisonObserverMachineCheck.Description` array, with retained
  type and mode names. Validate it using `MachineCheck.check` on
  `ComparisonBalancedProjection.shapeShadow Δ`: this preserves the original
  scalar assumptions and has no raw subtype edges. Mode transport supplies
  `ModalValid`, `RangeClosed`, and `Coherent` for the original `Δ`.
- Finite tag and observation indices `A` and `O`, and a Boolean matrix
  `embed : A → O → Bool`.
- Finite constructor row lists indexed by finite controls: ordinary product
  and sum, function, and product/sum lists for each explicitly listed literal
  prefix. An absent literal prefix denotes the empty table. Check the table
  order conditions on all finite row pairs: control order for product/sum,
  `FutureLe` for function, and the correct argument variance.
- A finite frozen lookup list of exact comparison syntax and coordinate
  arrays. Check that each array is monotone in the control. Missing keys denote
  bottom; duplicate keys retain the interpreter's first-match behavior.
- A finite table `j : D → (M → O → Bool)`, where `D` is the range product of the
  checked machine. Check that `j` preserves join and meet, reflects order, and
  commutes with control shifts. Check the three primitive constructor
  agreement equations on every pair of values in `D`. Atoms, unit, and credit
  are derived as `j` of the corresponding machine values.

These checks instantiate `RelativeTables.IndexedTable`,
`RelativeSyntax.Model`, and `RelativeSyntax.DefinedAgreement`. They are finite:
`D` consists of the Boolean vectors admitted by the machine's range flags.
There is no requirement that every tag denote a defined type, or that partial
constructor rows satisfy the defined constructor equations.

Finally evaluate each **original whole raw subtype bound** of `Δ` in this
outer interpreter and check its inequality. Together with the finite agreement
checks, `DefinedAgreement.algebra_sound` gives soundness for every original
algebra rule. The inner machine is not required to satisfy the original partial
raw bounds, and no `Δ.TypeBoundsDefined` premise is introduced.

## Supported evaluation and finite prefixes

The current semantic suffix normalizer uses classical totality. Supply a
reference supported evaluator whose totality tests use the finite scalar
presentation, and prove agreement with `normalize` and `Model.denote` on the
checked inputs. The production evaluator should obtain the same completed
scalar decisions through the verified backend. Literal composition and the
prefix tree must stay exact; do not reassociate through a partial outer label.

Unlisted type atoms already default to unit in `MachineSerialization`.
Unlisted mode names use the fixed identity projection. Query support markers
in `ComparisonObserverShadowQuerySupport` ensure that every checked endpoint's
names are retained and its fresh shadow names are disjoint.

For the constructed model, the active literal-prefix set is bounded by
`ComparisonRawHeadPrefixRows.prefixes B`, the root labels of its finite head
list. `extend_eq_bot_of_not_mem` proves that every other prefix table is empty.
Thus the apparently infinite `Option ModExpr` table family has an exact finite
serialization, including its default behavior.

## Completeness bridge and remaining scope

Choose the extraction machine through
`MachineSerialization.bounded_descriptions_on`, then rebuild the same diagram
from its finite range algebra. Apply the theorem's observer coverage to the
source machine's certified observer, preserving the joint query/shadow pattern.
This is an additional extraction adapter: `serialize_checked` requires an
explicit `Coordinates` witness, which has not been inferred from an arbitrary
`Certified` machine. Do not assume the latter implication.

Serialize the resulting model with `A = D ⊕ P`, its Boolean embedding, `j`, all
finite table entries, and frozen entries. The construction proves each finite
validation condition. Serialization preserves branches, ranges, unit/credit,
retained atoms, and all total actions on admitted range values; these are the
defined operations used by `j` and the tables. A small adapter checks the
description on `shapeShadow Δ`, with vacuous subtype-bound checks. Retain all
declared raw names, selected query names, and shadow names during this step.

`ComparisonObserverShadowQueries.exists_realization_queries` retains each
selected defined `CompareTy` and all shadow names at one common finite state
per source observer. Its `compare_reflect`, `defined_boundary_reflect`, and
`boundary_defined_reflect` cover the selected defined/defined and both mixed
comparison directions. Raw trace reflection covers raw/raw endpoints. This
provides the route from a failed selected comparison to an accepted separating
certificate; the executable serialization and validator bridge are still to
be implemented.

After this bridge, finite certificate search is an effective refutation method
for fixed endpoints. It does **not** bound the structural rank of an unknown
substitution, prove that no higher-rank witness exists, or complete the public
comparison stopping contract. That independent obligation is recorded in
[`comparison-stopping-bound.md`](comparison-stopping-bound.md).
