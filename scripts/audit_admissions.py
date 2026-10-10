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
]
with tempfile.TemporaryDirectory(prefix='modality-audit-') as directory:
    path = Path(directory) / 'Audit.lean'
    path.write_text('import ModalityInference\nimport ModalityInference.Proofs.Evaluation\n'
                    'import ModalityInference.Proofs.Interpretation\n'
                    'import ModalityInference.Proofs.Erasure\n'
                    'import ModalityInference.Proofs.Substitution\n'
                    'import ModalityInference.Proofs.PolymorphicCapture\n' + '\n'.join(
        f'#print axioms {name}' for name in constants) + '\n')
    result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT,
                            text=True, capture_output=True, check=True)
    assert 'sorryAx' not in result.stdout + result.stderr, result.stdout + result.stderr
print(f'Admission boundary OK: {admissions} isolated deferred proofs; '
      f'{len(constants)} public/established declarations checked transitively.')
