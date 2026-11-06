"""Re-elaborate the exact main statement after a complete verified build."""
from pathlib import Path
import ast
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
LEAN = ROOT.parent / 'jsp423-repro/_toolchain/bin/lean.exe'
LIBRARIES = Path('C:/Users/Administrator/Documents/ChatGPT/jsp423_fast_runtime_20261101/libraries')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
REQUIRED = {'Carlet.oddCarletConjecture_main',
            'Carlet.oddCarletConjecture_original_statement',
            'Carlet.independently_checked_original_statement',
            'Carlet.evenDegreeCarlet_unconditional',
            'Carlet.independently_checked_even_degree_statement'}


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def expected_modules():
    tree = ast.parse((ROOT / 'build.py').read_text(encoding='utf-8'))
    for node in tree.body:
        if isinstance(node, ast.Assign) and any(
                isinstance(t, ast.Name) and t.id == 'modules' for t in node.targets):
            return ast.literal_eval(node.value.values[-1])
    raise RuntimeError('Cannot locate the default build module list')


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    receipt = json.loads((ROOT / 'build_receipt.json').read_text(encoding='utf-8'))
    if [m['module'] for m in receipt['modules']] != expected_modules():
        raise RuntimeError('A complete default build receipt is required')
    summary = json.loads((ROOT / 'verified_build_summary.json').read_text(encoding='utf-8'))
    if summary.get('main_conjecture_proved') is not True:
        raise RuntimeError('The independent full-build verifier has not passed')
    main_entry = next(m for m in receipt['modules'] if m['module'] == 'Carlet/MainTheorem.lean')
    source = ROOT / 'Carlet/MainTheorem.lean'
    olean = source.with_suffix('.olean')
    if sha256(source) != main_entry['source_sha256'] or sha256(olean) != main_entry['olean_sha256']:
        raise RuntimeError('Final theorem source or compiled artifact does not match the full build')
    even_entry = next(m for m in receipt['modules'] if m['module'] == 'Carlet/EvenDegree.lean')
    even_source = ROOT / 'Carlet/EvenDegree.lean'
    even_olean = even_source.with_suffix('.olean')
    if sha256(even_source) != even_entry['source_sha256'] or sha256(even_olean) != even_entry['olean_sha256']:
        raise RuntimeError('Even-degree theorem source or compiled artifact does not match the full build')

    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join([str(ROOT), str(ROOT / 'vendor/aintlib/olean'),
                                       *[str(p) for p in LIBRARIES.iterdir() if p.is_dir()]])
    env['LEAN_SYSROOT'] = str(LEAN.parent.parent)
    env['LEAN_NUM_THREADS'] = '1'
    version = subprocess.run([str(LEAN), '--version'], env=env, text=True,
                             capture_output=True, check=True).stdout.strip()
    if 'version 4.33.0,' not in version:
        raise RuntimeError('Unexpected Lean version: ' + version)
    with tempfile.TemporaryDirectory(prefix='carlet-audit-') as directory:
        run = subprocess.run([str(LEAN), '-j1', '-o', str(Path(directory) / 'FinalAudit.olean'),
                              str(ROOT / 'Carlet/FinalTheoremAudit.lean')],
                             cwd=ROOT, env=env, text=True, capture_output=True,
                             encoding='utf-8', errors='replace')
    output = run.stdout + run.stderr
    if run.returncode or 'warning' in output.lower() or 'sorryAx' in output:
        raise RuntimeError('Independent Lean audit failed:\n' + output)
    audits = {name: {item.strip() for item in names.split(',') if item.strip()}
              for name, names in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output)}
    audits.update({name: set() for name in
                   re.findall(r"'([^']+)' does not depend on any axioms", output)})
    if not REQUIRED <= audits.keys() or any(not axioms <= ALLOWED for axioms in audits.values()):
        raise RuntimeError('Missing final theorem audit or unapproved axiom:\n' + output)
    result = {'status': 'passed', 'lean_version': version,
              'full_build_time_utc': receipt['time_utc'],
              'main_source_sha256': sha256(source), 'main_olean_sha256': sha256(olean),
              'even_degree_source_sha256': sha256(even_source),
              'even_degree_olean_sha256': sha256(even_olean),
              'audit_source_sha256': sha256(ROOT / 'Carlet/FinalTheoremAudit.lean'),
              'axioms': {name: sorted(audits[name]) for name in sorted(REQUIRED)},
              'output': output}
    (ROOT / 'final_theorem_audit.json').write_text(
        json.dumps(result, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
