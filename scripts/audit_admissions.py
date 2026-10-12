#!/usr/bin/env python3
"""Check the admission boundary, including transitive Lean axiom dependencies."""
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def code_only(source):
    out, i, depth = [], 0, 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif source.startswith('--', i):
            j = source.find('\n', i)
            i = len(source) if j == -1 else j
        elif source[i] == '"':
            i += 1
            while i < len(source) and source[i] != '"':
                i += 2 if source[i] == '\\' else 1
            i += 1
        else:
            out.append(source[i])
            i += 1
    return ''.join(out)


admissions = 0
for path in [ROOT / 'ModalityInference.lean', *sorted((ROOT / 'ModalityInference').rglob('*.lean'))]:
    code = code_only(path.read_text())
    proof = 'Proofs' in path.relative_to(ROOT).parts
    bad = re.findall(r'\b(?:sorry|admit|axiom|unsafe)\b', code)
    if proof:
        assert all(token == 'sorry' for token in bad), f'Unexpected escape hatch: {path}'
        admissions += len(bad)
    else:
        assert not bad, f'Admission outside designated proof directory: {path}: {bad}'
        if path.name != 'Proofs.lean':
            assert not re.search(r'^import\s+ModalityInference\.Proofs', code, re.M), path

constants = [
    'Equation.decide_correct', 'RightExpr.iterate_stabilizes',
    'ModalityInference.infer', 'ModalityInference.solve',
    'ModalityInference.checkSubsumption', 'ModalityInference.evalFuel',
    'ModalityInference.Typing', 'ModalityInference.ValueInterpretation',
    'ModalityInference.evalFuel_sound', 'ModalityInference.Eval.fuel_complete',
    'ModalityInference.Eval.deterministic', 'ModalityInference.evalFuel_stable',
    'ModalityInference.evalFuel_monotone', 'ModalityInference.Eval.no_rejection',
    'ModalityInference.ValueInterpretation.global_references',
    'ModalityInference.ValueInterpretation.shared_support',
    'ModalityInference.Eval.annotation_erasure',
    'ModalityInference.PolymorphicCapture.no_unrestricted_soundness',
    'ModalityInference.Value.substTypes', 'ModalityInference.Eval.substTypes',
    'ModalityInference.Value.mapAnnotation_erasure', 'ModalityInference.ValueErasure.references',
    'ModalityInference.World.compatible_mapAnnotation',
    'ModalityInference.PolymorphicCapture.transported_interpreted',
    'ModalityInference.Substitution.ty_compose',
    'ModalityInference.ModExpr.subst_compose',
    'ModalityInference.Term.subst_scoped', 'ModalityInference.Term.rename_scoped',
    'ModalityInference.splitContext_spec', 'ModalityInference.lookupScheme_sound',
    'ModalityInference.Lookup.lookupScheme',
    'ModalityInference.RawTyping.weakening',
    'ModalityInference.Subtype.semantic', 'ModalityInference.Subtype.realize_defined',
    'ModalityInference.Owns.mode_mono', 'ModalityInference.ValueInterpretation.mode_mono',
    'ModalityInference.Subtype.substitute', 'ModalityInference.Subtype.substitute_ordinary',
    'ModalityInference.ModExpr.eval_subst',
    'ModalityInference.PartialSubstitution.no_unrestricted_subtyping_substitution',
    'ModalityInference.Substitution.constraint_compose',
    'ModalityInference.Substitution.bounds_compose',
    'ModalityInference.Scheme.subst_body_action', 'ModalityInference.Scheme.subst_bounds_action',
    'ModalityInference.Value.substCapturedTypes', 'ModalityInference.SchemeValue.subst',
    'ModalityInference.Value.substCapturedTypes_erasure',
    'ModalityInference.Eval.substCapturedTypes_erasure',
    'ModalityInference.ScopedCaptures.nested_transport',
    'ModalityInference.ScopedCaptures.uniform_and_scoped_differ',
    'ModalityInference.SchemeValue.instantiate',
    'ModalityInference.TypeExpr.wellFormedBounds_spec',
    'ModalityInference.instantiationGuards_spec',
    'ModalityInference.SchemeValue.instantiate_spec',
    'ModalityInference.SchemeValue.instantiate_erasure',
    'ModalityInference.ScopedCaptures.unique_instantiation_contract',
    'ModalityInference.toCNF_correct',
    'ModalityInference.ConcreteBackend.atomFin_lookup',
    'ModalityInference.ConcreteBackend.equation_correct',
    'ModalityInference.ConcreteBackend.decideFormula_correct',
    'ModalityInference.projectedModes_encodeModes',
    'ModalityInference.ModExpr.project_correct',
    'ModalityInference.modeFormula_correct',
    'ModalityInference.boundsModeFormula_correct',
    'ModalityInference.ConcreteBackend.entails_correct',
    'ModalityInference.ConcreteBackend.entails_submode',
    'ModalityInference.GroundInstantiates.mono_iff',
    'ModalityInference.GroundInstantiates.modal_iff',
    'ModalityInference.SchemeInterpretation.mono_iff',
    'ModalityInference.BindingOwns.mono_iff',
    'ModalityInference.EnvironmentInterpretation.singleton',
    'ModalityInference.AmbientCaptureScope.unquantified_change_rejected',
    'ModalityInference.ContextScoping.old_sharing_premise_insufficient',
    'ModalityInference.ContextScoping.renamed_fresh',
    'ModalityInference.Scheme.subsumptionIndices_type_fresh',
    'ModalityInference.Scheme.subsumptionIndices_mode_fresh',
    'ModalityInference.Scheme.subsumption_type_skolem_fresh',
    'ModalityInference.Scheme.subsumption_mode_skolem_fresh',
    'ModalityInference.Scheme.subsumptionIndices_empty',
    'ModalityInference.SubsumptionScope.former_weakening_unsound',
    'ModalityInference.SubsumptionScope.corrected_comparison_rejects',
    'ModalityInference.ResourceInterpretation',
    'ModalityInference.ResourceSchemeInterpretation',
    'ModalityInference.ResourceEnvironmentInterpretation',
    'ModalityInference.ResourceSemanticEvaluation',
    'ModalityInference.ResourceInterpretation.erasure',
    'ModalityInference.ResourceInterpretation.global_references',
    'ModalityInference.ResourceInterpretation.shared_resources',
    'ModalityInference.ResourceEnvironmentInterpretation.lookup',
    'ModalityInference.ResourceCapture.scheme_interpreted',
    'ModalityInference.ResourceCapture.variable_semantic',
    'ModalityInference.Typing.realize_defined',
    'ModalityInference.TypeExpr.source_wellFormedBounds',
    'ModalityInference.UndefinedDomain.former_typed',
    'ModalityInference.UndefinedDomain.interpreted',
    'ModalityInference.UndefinedDomain.rejected',
    'ModalityInference.UndefinedDomain.not_semantic',
    'ModalityInference.UndefinedDomain.corrected_function_rejected',
    'ModalityInference.ResourceInterpretation.mode_mono',
    'ModalityInference.ResourceLe.fn',
    'ModalityInference.ResourceLe.prod',
    'ModalityInference.Subtype.resourceLe',
    'ModalityInference.Subtype.resource_semantic',
    'ModalityInference.ModExpr.eval_congr',
    'ModalityInference.TypeExpr.realize_congr',
    'ModalityInference.GroundModels.congr',
    'ModalityInference.GroundInstantiates.models_fresh',
    'ModalityInference.GroundInstantiates.eval_fresh',
    'ModalityInference.ResourceSchemeInterpretation.shared',
    'ModalityInference.ContextJoin.resource_semantics',
    'ModalityInference.Deferred.context_join_semantics',
    'ModalityInference.ResourceSchemeInterpretation.capture',
    'ModalityInference.Lock.resource_semantics',
    'ModalityInference.Deferred.locking_semantics',
    'ModalityInference.TypeExpr.DefinedUnder.realize_defined',
    'ModalityInference.Entails.source_sub_iff',
    'ModalityInference.Entails.source_equal_iff',
    'ModalityInference.Entails.source_equiv_iff',
    'ModalityInference.UndefinedBounds.former_typed',
    'ModalityInference.UndefinedBounds.no_ground_instance',
    'ModalityInference.UndefinedBounds.interpreted',
    'ModalityInference.UndefinedBounds.rejected',
    'ModalityInference.UndefinedBounds.not_semantic',
    'ModalityInference.UndefinedBounds.corrected_instantiation_rejected',
    'ModalityInference.UndefinedBounds.corrected_consistency_rejected',
    'ModalityInference.Subtype.ground',
    'ModalityInference.Entails.groundSatisfies',
    'ModalityInference.EntailsAll.groundModels',
    'ModalityInference.ModExpr.eval_refinement',
    'ModalityInference.ModExpr.eval_ground',
    'ModalityInference.TypeExpr.realize_ground',
    'ModalityInference.GroundSatisfies.pullback',
    'ModalityInference.GroundModels.pullback',
    'ModalityInference.Instantiates.ground',
    'ModalityInference.BoundsSatisfiable.ground',
    'ModalityInference.ResourceEnvironmentInterpretation.instantiated_lookup',
    'ModalityInference.GroundInstantiates.rebase',
    'ModalityInference.ResourceSchemeInterpretation.ambient_congr',
    'ModalityInference.ResourceInterpretation.reworld',
    'ModalityInference.ResourceSchemeInterpretation.reworld',
    'ModalityInference.ResourceEnvironmentInterpretation.reworld',
    'ModalityInference.ResourceSchemeInterpretation.capture_many',
    'ModalityInference.Lock.resource_many_semantics',
    'ModalityInference.Typing.freeVars_present',
    'ModalityInference.Typing.scoped',
    'ModalityInference.Typing.closed',
    'ModalityInference.ResourceEnvironmentInterpretation.restrict',
    'ModalityInference.ResourceEnvironmentInterpretation.trim',
    'ModalityInference.ContextResources.restrict_subset',
    'ModalityInference.TypeExpr.realize_subst_congr',
    'ModalityInference.GroundSatisfies.subst_congr',
    'ModalityInference.GroundModels.subst_congr',
    'ModalityInference.GroundInstantiates.skolemize',
    'ModalityInference.Subsumes.resource_semantic',
    'ModalityInference.ContextLe.resource_semantics',
    'ModalityInference.Subsumes.realizable',
    'ModalityInference.Typing.freeVars_realizable',
    'ModalityInference.Lock.restrict',
    'ModalityInference.ContextLe.restrict',
    'ModalityInference.ContextJoin.restrict',
    'ModalityInference.ResourceEnvironmentInterpretation.trim_valid',
    'ModalityInference.ResourceSchemeInterpretation.capture_global',
    'ModalityInference.Lock.trim_global',
    'ModalityInference.ResourceSchemeInterpretation.mono',
    'ModalityInference.ResourceEnvironmentInterpretation.cons',
    'ModalityInference.ResourceEnvironmentInterpretation.cons_used',
    'ModalityInference.ContextResources.cons_used_subset',
    'ModalityInference.ResourceEnvironmentInterpretation.references',
    'ModalityInference.Typing.resource_lam',
    'ModalityInference.Supply.slice_disjoint',
    'ModalityInference.Supplies.fresh_branch_disjoint',
    'ModalityInference.World.Compatible.branch',
    'ModalityInference.Eval.references',
    'ModalityInference.Eval.not_fresh_branch',
    'ModalityInference.Typing.resource_generalize_closed',
    'ModalityInference.Typing.resource_defn',
]
with tempfile.TemporaryDirectory(prefix='modality-audit-') as directory:
    path = Path(directory) / 'Audit.lean'
    path.write_text('import ModalityInference\nimport ModalityInference.Proofs.Evaluation\n'
                    'import ModalityInference.Proofs.Interpretation\n'
                    'import ModalityInference.Proofs.Erasure\n'
                    'import ModalityInference.Proofs.Substitution\n'
                    'import ModalityInference.Proofs.Scoping\n'
                    'import ModalityInference.Proofs.Generation\n'
                    'import ModalityInference.Proofs.Declarative\n'
                    'import ModalityInference.Proofs.Subtyping\n'
                    'import ModalityInference.Proofs.PartialSubstitution\n'
                    'import ModalityInference.Proofs.ScopedCaptures\n'
                    'import ModalityInference.Proofs.Backend\n'
                    'import ModalityInference.Proofs.Projection\n'
                    'import ModalityInference.Proofs.ContextScoping\n'
                    'import ModalityInference.Proofs.SubsumptionScope\n'
                    'import ModalityInference.Proofs.ResourceCapture\n'
                    'import ModalityInference.Proofs.UndefinedDomain\n'
                    'import ModalityInference.Proofs.UndefinedBounds\n'
                    'import ModalityInference.Proofs.GroundInstantiation\n'
                    'import ModalityInference.Proofs.GroundSchemes\n'
                    'import ModalityInference.Proofs.ResourceWorlds\n'
                    'import ModalityInference.Proofs.ResourceRestriction\n'
                    'import ModalityInference.Proofs.ResourceSubsumption\n'
                    'import ModalityInference.Proofs.ResourceCaptures\n'
                    'import ModalityInference.Proofs.ResourceClosure\n'
                    'import ModalityInference.Proofs.ResourceDefinitions\n'
                    'import ModalityInference.Proofs.ResourceSubtyping\n'
                    'import ModalityInference.Proofs.Structural\n'
                    'import ModalityInference.Proofs.PolymorphicCapture\n' + '\n'.join(
        f'#print axioms {name}' for name in constants) + '\n')
    result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT,
                            text=True, capture_output=True, check=True)
    assert 'sorryAx' not in result.stdout + result.stderr, result.stdout + result.stderr
print(f'Admission boundary OK: {admissions} isolated deferred proofs; '
      f'{len(constants)} public/established declarations checked transitively.')
