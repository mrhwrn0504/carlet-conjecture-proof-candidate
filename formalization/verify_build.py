"""Independently verify a full build receipt against the current files.

The final theorem is counted only when the complete default build contains
the explicitly printed original-statement theorem and its axiom audit.
A targeted build receipt is deliberately rejected.
"""
import ast
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def expected_modules():
    tree = ast.parse((ROOT / 'build.py').read_text(encoding='utf-8'))
    for node in tree.body:
        if isinstance(node, ast.Assign) and any(
                isinstance(t, ast.Name) and t.id == 'modules' for t in node.targets):
            return ast.literal_eval(node.value.values[-1])
    raise RuntimeError('Cannot locate the default module list')


def verify():
    expected = expected_modules()
    positions = {Path(path).with_suffix('').as_posix().replace('/', '.'): index
                 for index, path in enumerate(expected)}
    if len(positions) != len(expected):
        raise RuntimeError('Duplicate modules in the default build manifest')
    for index, name in enumerate(expected):
        for line in (ROOT / name).read_text(encoding='utf-8-sig').splitlines():
            match = re.match(r'^\s*import\s+(.+)$', line)
            if not match:
                continue
            for dependency in match.group(1).split('--', 1)[0].split():
                if dependency.startswith('Carlet.') and (
                        dependency not in positions or positions[dependency] >= index):
                    raise RuntimeError(f'Missing or out-of-order local import: {name}: {dependency}')
    # Audit the pinned Hasse dependency's actual source and compiled artifacts.
    # AINTLIB contains unrelated admitted declarations; the printed axioms of
    # the imported Hasse theorem and the final Carlet theorems are checked below.
    vendor = ROOT / 'vendor/aintlib'
    entries = {}
    lines = (vendor / 'olean/probe-receipt.jsonl').read_text(encoding='utf-8').splitlines()
    for line in lines:
        item = json.loads(line)
        entries[item['module']] = item
    if len(entries) != 188 or len(lines) != len(entries) or 'HasseWeil.HasseBound' not in entries:
        raise RuntimeError('Incomplete Hasse dependency build receipt')
    hasse_positions = {name: index for index, name in enumerate(entries)}
    for index, (name, item) in enumerate(entries.items()):
        parts = name.split('.')
        source = ((vendor / 'src' / 'Common').joinpath(*parts[1:]) if parts[0] == 'Common'
                  else (vendor / 'src/projects/HasseWeil').joinpath(*parts))
        source = source.with_suffix('.lean')
        olean = (vendor / 'olean').joinpath(*parts).with_suffix('.olean')
        for line in source.read_text(encoding='utf-8-sig').splitlines():
            match = re.match(r'^\s*import\s+(.+)$', line)
            if not match:
                continue
            for dependency in match.group(1).split('--', 1)[0].split():
                if (dependency == 'HasseWeil' or dependency.startswith('HasseWeil.') or
                        dependency == 'Common' or dependency.startswith('Common.')) and (
                        dependency not in hasse_positions or hasse_positions[dependency] >= index):
                    raise RuntimeError(f'Missing or out-of-order Hasse import: {name}: {dependency}')
        if item['exit_code'] or 'warning' in item['output'].lower():
            raise RuntimeError(f'Unsuccessful Hasse dependency: {name}')
        for path, key in ((source, 'source_sha256'), (olean, 'olean_sha256')):
            if hashlib.sha256(path.read_bytes()).hexdigest() != item[key]:
                raise RuntimeError(f'Stale or changed Hasse dependency: {path}')
    receipt = json.loads((ROOT / 'build_receipt.json').read_text(encoding='utf-8'))
    modules = receipt['modules']
    if [m['module'] for m in modules] != expected:
        raise RuntimeError('Receipt is not for the complete default build')
    declarations = 0
    axioms = set()
    for m in modules:
        source = ROOT / m['module']
        olean = source.with_suffix('.olean')
        if m['exit_code'] or not m['hole_free_output'] or not m['printed_axiom_audit']:
            raise RuntimeError(f"Unsuccessful module: {m['module']}")
        for path, key in ((source, 'source_sha256'), (olean, 'olean_sha256')):
            if hashlib.sha256(path.read_bytes()).hexdigest() != m[key]:
                raise RuntimeError(f'Stale or changed artifact: {path}')
        output = m['stdout'] + m['stderr']
        if 'warning' in output.lower() or 'sorryAx' in output:
            raise RuntimeError(f"Warning or proof hole: {m['module']}")
        declarations += len(m['theorem_axioms'])
        for names in m['theorem_axioms'].values():
            axioms.update(names)
    if not axioms <= ALLOWED_AXIOMS:
        raise RuntimeError(f'Unexpected axioms: {axioms - ALLOWED_AXIOMS}')
    even_entries = [m for m in modules if m['module'] == 'Carlet/EvenDegree.lean']
    if len(even_entries) != 1:
        raise RuntimeError('Missing or duplicated even-degree theorem module')
    even = even_entries[0]
    even_theorem = 'Carlet.evenDegreeCarlet_unconditional'
    if even_theorem not in even['theorem_axioms']:
        raise RuntimeError('Unconditional even-degree theorem axiom audit missing')
    if f'theorem {even_theorem} :' not in even['stdout']:
        raise RuntimeError('Unconditional even-degree theorem statement was not printed')
    even_axioms = set(even['theorem_axioms'][even_theorem])
    if not even_axioms <= ALLOWED_AXIOMS:
        raise RuntimeError(f'Unexpected axioms in the even-degree theorem: {even_axioms - ALLOWED_AXIOMS}')
    main_entries = [m for m in modules if m['module'] == 'Carlet/MainTheorem.lean']
    if len(main_entries) != 1:
        raise RuntimeError('Missing or duplicated final main theorem module')
    main = main_entries[0]
    required = {'Carlet.oddCarletConjecture_main',
                'Carlet.oddCarletConjecture_original_statement'}
    if not required <= main['theorem_axioms'].keys():
        raise RuntimeError('Final original-statement theorem axiom audit missing')
    if 'theorem Carlet.oddCarletConjecture_original_statement :' not in main['stdout']:
        raise RuntimeError('Final expanded theorem statement was not printed')
    final_axioms = set(main['theorem_axioms']['Carlet.oddCarletConjecture_main'])
    expanded_axioms = set(main['theorem_axioms']['Carlet.oddCarletConjecture_original_statement'])
    if not final_axioms <= ALLOWED_AXIOMS or not expanded_axioms <= ALLOWED_AXIOMS:
        raise RuntimeError('Unexpected axioms in the final theorem')
    summary = dict(modules=len(modules), hasse_dependency_modules=len(entries), printed_declarations_checked=declarations,
                   source_and_olean_hashes_match=True, compiler_warnings=0,
                   main_conjecture_proved=True,
                   main_theorem_axioms=sorted(final_axioms), even_degree_theorem_proved=True,
                   even_degree_theorem_axioms=sorted(even_axioms))
    (ROOT / 'verified_build_summary.json').write_text(
        json.dumps(summary, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(dict(summary, audited_axioms=sorted(axioms)), indent=2))


if __name__ == '__main__':
    verify()
