"""Compile a bounded prefix of the pinned, patched AINTLIB Hasse dependency graph.

All output is isolated under tmp; this does not edit the Carlet project or its
build receipt. A successful prefix is not a proof audit of the final theorem.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys

sys.stdout.reconfigure(encoding='utf-8')
sys.stderr.reconfigure(encoding='utf-8')
PROJECT = Path(__file__).resolve().parents[2]
WORKSPACE = PROJECT.parent.parent.parent
SOURCE = PROJECT / 'vendor/aintlib/src'
OUT = PROJECT / 'vendor/aintlib/olean'
OUT = Path(os.environ.get('CARLET_AINTLIB_OLEAN') or OUT)
RUNTIME = Path(os.environ.get('CARLET_MATHLIB_LIBRARIES') or
               'C:/Users/Administrator/Documents/ChatGPT/jsp423_fast_runtime_20261101/libraries')
LEAN = Path(os.environ.get('CARLET_LEAN_BIN') or
            WORKSPACE / 'jsp423-repro/_toolchain/bin/lean.exe')
LIMIT = int(sys.argv[1]) if len(sys.argv) > 1 else 188
if not LEAN.is_file():
    raise FileNotFoundError('Lean not found; set CARLET_LEAN_BIN to the Lean 4.33.0 executable')
if not RUNTIME.is_dir():
    raise FileNotFoundError('Mathlib libraries not found; set CARLET_MATHLIB_LIBRARIES to the directory containing the compiled libraries')
OUT.mkdir(parents=True, exist_ok=True)

module_paths = {}
for subdir, prefix in [('projects/HasseWeil', ''), ('Common', 'Common.')]:
    srcdir = SOURCE / subdir
    for path in srcdir.rglob('*.lean'):
        name = prefix + '.'.join(path.relative_to(srcdir).with_suffix('').parts)
        module_paths[name] = path

pattern = re.compile(r'^\s*(?:(?:public|meta)\s+)?import\s+([\w.]+)', re.M)
imports = {name: {m for m in pattern.findall(path.read_text(encoding='utf-8'))
                  if m in module_paths} for name, path in module_paths.items()}
ordered, active, seen = [], set(), set()
def visit(mod):
    if mod in seen:
        return
    if mod in active:
        raise RuntimeError('cycle in parsed imports: ' + mod)
    active.add(mod)
    for dep in sorted(imports[mod]):
        visit(dep)
    active.remove(mod)
    seen.add(mod)
    ordered.append(mod)

visit('HasseWeil.HasseBound')
print('dependency_modules', len(ordered), 'probe_limit', LIMIT, flush=True)
env = os.environ.copy()
env['LEAN_PATH'] = os.pathsep.join([str(OUT), *[str(p) for p in RUNTIME.iterdir() if p.is_dir()]])
env['LEAN_SYSROOT'] = str(LEAN.parent.parent)
env['LEAN_NUM_THREADS'] = '1'
receipt = OUT / 'probe-receipt.jsonl'
previous = {}
if receipt.exists():
    for line in receipt.read_text(encoding='utf-8').splitlines():
        entry = json.loads(line)
        previous[entry['module']] = entry
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

for i, mod in enumerate(ordered[:LIMIT], 1):
    path = module_paths[mod]
    output = OUT.joinpath(*mod.split('.')).with_suffix('.olean')
    sourcehash = digest(path)
    old = previous.get(mod, {})
    print(f'[{i}/{min(LIMIT,len(ordered))}] {mod}', flush=True)
    if (output.exists() and old.get('exit_code') == 0 and
        old.get('source_sha256') == sourcehash and old.get('olean_sha256') == digest(output)):
        previous[mod] = old
        print('matching prior probe output', flush=True)
        continue
    output.parent.mkdir(parents=True, exist_ok=True)
    options = ['-DrelaxedAutoImplicit=false', '-DmaxSynthPendingDepth=3', '-Dpp.unicode.fun=true']
    run = subprocess.run([str(LEAN), '-j1', *options, '-o', str(output), str(path)],
        cwd=SOURCE, env=env, text=True, capture_output=True, encoding='utf-8', errors='replace')
    combined = run.stdout + run.stderr
    entry = {'module': mod, 'exit_code': run.returncode, 'source_sha256': sourcehash,
             'olean_sha256': digest(output) if run.returncode == 0 and output.exists() else None,
             'output': combined}
    previous[mod] = entry
    receipt.write_text(''.join(json.dumps(previous[name], ensure_ascii=False) + '\n'
                                   for name in ordered if name in previous), encoding='utf-8')
    print('exit', run.returncode, flush=True)
    if combined:
        print(combined[-4000:], flush=True)
    if run.returncode:
        sys.exit(run.returncode)
