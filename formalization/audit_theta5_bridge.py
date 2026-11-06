"""Independently rebuild and audit the explicitly requested Theta5 bridge.

The output tree is separate from the complete default build, so this check
does not overwrite its source/OLean hashes or build receipt.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
AUDIT_ROOT = ROOT.parent / 'tmp/theta5_bridge_independent_build'
LEAN = ROOT.parent / 'jsp423-repro/_toolchain/bin/lean.exe'
LIBRARIES = Path('C:/Users/Administrator/Documents/ChatGPT/jsp423_fast_runtime_20261101/libraries')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
MODULES = [
    'Theta5Probe', 'Theta5SparseMonomial', 'Theta5EvaluationStagesProbe',
    'Theta5SparseBridgeProbe', 'Theta5LastCoordinateExpansionProbe',
    'Theta5SparseSupportListsProbe', 'Theta5PositiveSupportListsProbe',
    'Theta5LastZeroCoefficientProbe', 'Theta5RecurrenceWordCertificateProbe',
    'Theta5PositiveRecurrenceWordProbe', 'Theta5SpecializationBridgeProbe',
    'Theta5RankFourSpanBridgeProbe',
]
REQUIRED = {'Carlet.theta5Span4_polynomial',
            'Carlet.theta5_specialization_eq_span_polynomial',
            'Carlet.hasZeroSumSubspace_five_of_theta5_independent_zero'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    full = json.loads((ROOT / 'build_receipt.json').read_text(encoding='utf-8'))
    final = json.loads((ROOT / 'final_theorem_audit.json').read_text(encoding='utf-8'))
    if final.get('status') != 'passed' or final.get('full_build_time_utc') != full['time_utc']:
        raise RuntimeError('The current complete build and final theorem audit must pass first')
    (AUDIT_ROOT / 'Carlet').mkdir(parents=True, exist_ok=True)
    # Lean resolves a whole module namespace from the first search root that
    # contains it, rather than falling back file by file. Seed the isolated
    # tree with every verified default-build artifact before replacing the
    # twelve audited bridge artifacts with independently rebuilt versions.
    for entry in full['modules']:
        source = ROOT / entry['module']
        artifact = source.with_suffix('.olean')
        if digest(source) != entry['source_sha256'] or digest(artifact) != entry['olean_sha256']:
            raise RuntimeError(f'Full-build source or artifact changed: {source}')
        target = AUDIT_ROOT / artifact.relative_to(ROOT)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(artifact, target)
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join([str(AUDIT_ROOT), str(ROOT), str(ROOT / 'vendor/aintlib/olean'),
                                       *[str(p) for p in LIBRARIES.iterdir() if p.is_dir()]])
    env['LEAN_SYSROOT'] = str(LEAN.parent.parent)
    env['LEAN_NUM_THREADS'] = '1'
    results = []
    seen_axioms = {}
    for name in MODULES:
        source = ROOT / 'Carlet' / (name + '.lean')
        output = AUDIT_ROOT / 'Carlet' / (name + '.olean')
        run = subprocess.run([str(LEAN), '-j1', '-o', str(output), str(source)],
                             cwd=ROOT, env=env, text=True, capture_output=True,
                             encoding='utf-8', errors='replace')
        combined = run.stdout + run.stderr
        print(f'{name}: exit={run.returncode}', flush=True)
        print(combined, end='', flush=True)
        if run.returncode or 'warning' in combined.lower() or 'sorryAx' in combined:
            raise RuntimeError(f'Independent bridge rebuild failed: {name}')
        axioms = {key: {a.strip() for a in values.split(',') if a.strip()}
                  for key, values in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", combined)}
        axioms.update({key: set() for key in
                       re.findall(r"'([^']+)' does not depend on any axioms", combined)})
        if any(not used <= ALLOWED for used in axioms.values()):
            raise RuntimeError(f'Unexpected axiom while rebuilding {name}')
        seen_axioms.update(axioms)
        results.append({'module': name, 'source_sha256': digest(source),
                        'olean_sha256': digest(output), 'exit_code': run.returncode})
    if not REQUIRED <= seen_axioms.keys():
        raise RuntimeError('The requested span/independent-zero bridge audits are missing')
    result = {'status': 'passed', 'full_build_time_utc': full['time_utc'],
              'modules': results, 'required_axioms':
              {name: sorted(seen_axioms[name]) for name in sorted(REQUIRED)}}
    (ROOT / 'theta5_bridge_audit.json').write_text(
        json.dumps(result, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
