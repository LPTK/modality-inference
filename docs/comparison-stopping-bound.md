# Comparison completeness and the stopping bound

This note distinguishes the remaining contract from related unification results.
It does not establish a rank bound, a decision procedure, or an undecidability
reduction for the comparison calculus.

## Which completeness statement needs stopping?

The paper's `thm:comparison-reconstruction` in
[`sec/subs.tex`](../../sec/subs.tex) asserts success exactly when there is a
compatible finite internal instantiation, with the bounds, body comparison, and
definedness guards valid under the ambient and declared assumptions. The
preceding finite propagation schedule fixes a basis from the comparison and
claims stabilization after at most `n * 2^d` strict additions. Its missing basis
coverage argument therefore cannot be replaced silently by unbounded rank
enumeration.

The existing Lean contracts have different scopes:

| Contract | Established scope and quantifiers |
| --- | --- |
| `Obligations.SchemeSubsumptionComplete` | Duplicate-free source and target parameters, empty ambient, **residual target bounds**: an admissible witness implies eventual public success. Proved by `scheme_subsumption_complete`. |
| `checkSubsumption_finite_shape_complete` | Empty ambient and a finite model of the prepared declared shape equations: an admissible witness implies eventual public success. |
| `ComparisonRankedJoint.synthesize_complete` and `compare_complete` | No finite prepared shape model and `assumptions.TypeBoundsDefined`: an admissible prepared witness implies `∃ rank threshold result, ∀ fuel ≥ threshold, ... = success result`. |
| `ComparisonRankedJoint.synthesize_success_iff` | Under the same two assumptions, success at **some** rank and fuel is equivalent to existence of an admissible finite prepared witness. |
| `ComparisonRankedJointTermination` | Each **fixed rank** settles; this does not bound the ranks to search. |
| `checkSubsumption_terminates` and `checkSubsumption_stable` | Every input eventually returns a non-exhausted result, and every completed result is unchanged at all larger fuels. Stability preserves the exact evidence or rejection reason. |

The declarations are in
[`Obligations.lean`](../ModalityInference/Proofs/Obligations.lean),
[`ComparisonSubsumptionCompleteness.lean`](../ModalityInference/Proofs/ComparisonSubsumptionCompleteness.lean),
[`ComparisonSubsumptionFiniteShapes.lean`](../ModalityInference/Proofs/ComparisonSubsumptionFiniteShapes.lean),
[`ComparisonRankedJoint.lean`](../ModalityInference/Proofs/ComparisonRankedJoint.lean),
[`ComparisonRankedJointTermination.lean`](../ModalityInference/Proofs/ComparisonRankedJointTermination.lean),
and [`ComparisonSubsumptionTermination.lean`](../ModalityInference/Proofs/ComparisonSubsumptionTermination.lean).
Prepared type bounds are defined automatically for empty ambient by
`SchemePreparation.prepared_typeBoundsDefined`; arbitrary partial ambient
bounds require further treatment. The residual-target obligation is already
proved and must not be reported as the missing unrestricted theorem.

Positive eventual completeness alone needs no input-only stopping bound:
dovetailing complete fixed-rank searches can eventually find each finite
witness. But, together with soundness, extending that completeness to all inputs
while preserving the public checker's unconditional termination and completed
result stability gives a decision procedure. An eventually successful input
cannot have an earlier stable rejection. Thus the full contract needs an
effective negative stopping argument; an input-only witness-rank bound is one
possible means, not the only logically possible one.

Current rejection correctness and the public decision equivalence are proved
for residual targets in
[`ComparisonSubsumptionDecision.lean`](../ModalityInference/Proofs/ComparisonSubsumptionDecision.lean).
There are accepted finite witnesses outside the present public fallback:
[`ComparisonRelationalDeclaredWitness.lean`](../ModalityInference/Proofs/ComparisonRelationalDeclaredWitness.lean)
uses source `forall X. [X ≤ X → unit]. unit`, target
`[B ≤ B → unit]. unit`, and image `X = B`. The declared bounds are defined,
but the shape equations have no finite model. The ranked procedure covers the
witness while the public checker rejects it. Preserving all existing rejections
would therefore conflict with unrestricted completeness; preserving certified
negatives is the relevant requirement.

A separate explicit-rank interface, or an unbounded positive search, can preserve
the current public API and expose the existing positive coverage. Neither
completes its intended all-input contract. A rank-zero acceptance patch also
does not discharge the general stopping obligation.

## What the primary unification literature actually supplies

**Cycle-restricted EL.** Franz Baader, Stefan Borgwardt, and Barbara Morawska,
*Extending Unification in EL towards General TBoxes*, KR 2012, pp. 568–572
([primary PDF](https://cdn.aaai.org/ocs/4491/4491-21845-1-PB.pdf)).
Theorem 5 obtains an input-atom local unifier from any unifier for a flat,
cycle-restricted ground TBox; Corollary 6 gives NP membership. Lemma 7 uses the
cycle restriction to make the substitution dependency relation acyclic.
Example 9 shows that their local-unifier theorem fails without that restriction,
even though its example has a finite unifier. This is a failure of that locality
construction, not an undecidability theorem. Arbitrary declared bounds here
permit constructor cycles, so the restriction is unavailable without a new
reduction. EL also has conjunction and existential roles, not the full
distributive and variance-sensitive signature used here.

**Flat-TBox FL0.** Barbara Morawska, *Unification in FL0 modulo a flat TBox*,
DL 2020, CEUR volume 2663, paper 15
([primary PDF](https://ceur-ws.org/Vol-2663/paper-15.pdf)).
This proves ExpTime completeness when background axioms are flat subsumptions
between concept names. FL0 uses conjunction, top, and unary value restrictions.
The introduction explicitly reports general-TBox unification as unsolved in
2020. Naming a structured bound with fresh constants does not meet the theorem's
hypothesis: equations connecting those constants to role expressions restore
nonflat background axioms. The theorem therefore supplies no depth bound for
our arbitrary declared constructor bounds.

**General-TBox status in the ACUI extension paper.** Franz Baader, Pavlos
Marantidis, Antoine Mottet, and Alexander Okhotin, *Extensions of unification
modulo ACUI*, Mathematical Structures in Computer Science 30 (2020), 597–626,
[doi:10.1017/S0960129519000185](https://doi.org/10.1017/S0960129519000185).
The introduction (p. 598) and conclusion (p. 625) describe unification for EL and
FL0 with general TBoxes as open at that time. The paper proves positive results
for ACUI plus finite ground identities and explains that its methods do not
extend to those two richer theories. This is a dated statement about those
problems, not a claim about their current status or about this calculus.

**Undecidability with additional modal structure.** Frank Wolter and Michael
Zakharyaschev, *Undecidability of the unification and admissibility problems for
modal and description logics*, [arXiv:cs/0609052](https://arxiv.org/abs/cs/0609052)
(2006 version). The results concern K/K4 with a universal modality, multimodal
K/K4 with nominals, and corresponding Boolean description logics. The relative
role-box result uses transitive roles, inverse roles, and role hierarchies.
These are not an undecidability theorem for positive EL/FL0 under arbitrary
ground TBoxes, nor for the present calculus. No encoding of the required
universal, nominal, or role-box mechanisms into our exact constraints has been
established.

## Exact remaining transfer gap

The comparison problem requires one finite positive image for each unknown,
shared across all occurrences, independent constructor routes, modes, guards,
and constant boundaries. Product and sum act jointly on two lattice operands;
function reverses the domain order. A Boolean modal encoding of an observer's
branch selector can introduce disjunction and negation, outside EL/FL0, and an
arbitrary Boolean unifier need not reify to a permitted positive type image.
Neither direction of the needed finite-term correspondence follows from the
papers above.

Likewise, a finite semantic algebra or finite-state uniformizer does not itself
give a finite-depth syntactic image. A usable stopping theorem must preserve the
constrained input observations, shared overlapping windows, positivity, boundary
values, and eventual independence from the frontier. The existing one-route
de Bruijn approach does not establish this for independent branching routes.
There is presently no justified decidability or undecidability transfer from
these references to the exact missing comparison contract.
