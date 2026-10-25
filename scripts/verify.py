#!/usr/bin/env python3
"""Build every proof module and allow only standard Lean foundational axioms.

This verifies the delivered statements. It does not certify the mathematical
coverage of the source paper; see ASSUMPTIONS.md for that separate obligation.
"""
from datetime import datetime, timezone
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
from build_order import module_build_order

parser = argparse.ArgumentParser(description=__doc__)
build_mode = parser.add_mutually_exclusive_group()
build_mode.add_argument('--serial', action='store_true',
                       help='Build project modules one at a time before the umbrella.')
build_mode.add_argument('--require-current-modules', action='store_true',
                       help='Require Lake to confirm all module exports are current before building the umbrella.')
args = parser.parse_args()

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'verification'
OUT.mkdir(exist_ok=True)


def run(args, output=None):
    result = subprocess.run(args, cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if output:
        (OUT / output).write_text(result.stdout)
    if result.returncode:
        print(result.stdout, file=sys.stderr)
        raise SystemExit(result.returncode)
    return result.stdout


def proof_sources():
    directory = ROOT / 'DepthAspect'
    paths = sorted(directory.rglob('*.lean'))
    if any(path.parent != directory for path in paths):
        raise SystemExit('Nested proof sources are unsupported; no file may be omitted from the audit.')
    return paths


modules = proof_sources()
imports = set(re.findall(r'^import (\S+)\s*$',
                        (ROOT / 'DepthAspect.lean').read_text(), re.M))
expected_imports = {'DepthAspect.' + p.stem for p in modules}
if imports != expected_imports:
    raise SystemExit(f'Umbrella imports differ from modules: {imports ^ expected_imports}')

print(run([sys.executable, 'scripts/make_axiom_audit.py']).strip(), flush=True)
audit_source = (ROOT / 'CheckAxioms.lean').read_text()
expected_names = re.findall(r'^#print axioms (\S+)$', audit_source, re.M)
def source_hashes():
    source_files = (proof_sources() +
                    [ROOT / 'DepthAspect.lean', ROOT / 'CheckAxioms.lean',
                     ROOT / 'lakefile.toml', ROOT / 'lake-manifest.json', ROOT / 'lean-toolchain'] +
                    sorted((ROOT / 'scripts').glob('*.py')) +
                    sorted(p for p in (ROOT / 'correspondence').glob('*') if p.is_file()))
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in source_files}


before_hashes = source_hashes()
manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
mathlib = next(p for p in manifest['packages'] if p['name'] == 'mathlib')['rev']


def completed_paper_review():
    """A build cannot create or refresh the separate mathematical coverage review."""
    path = ROOT / 'correspondence/completed-review.json'
    if not path.is_file():
        return None
    review = json.loads(path.read_text())
    if review.get('status') != 'all paper claims reviewed':
        raise SystemExit('The recorded paper review is not marked complete.')
    proofs = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in modules}
    if review.get('proof_source_sha256') != proofs:
        raise SystemExit('Proof sources differ from the completed paper review; '
                         'review the changed mathematics before certifying it again.')
    maps = ['named-results.json', 'numbered-equations.json', 'prose-assertions.json',
            'paper-text.txt']
    expected = {'correspondence/' + name: hashlib.sha256(
        (ROOT / 'correspondence' / name).read_bytes()).hexdigest() for name in maps}
    if review.get('correspondence_sha256') != expected:
        raise SystemExit('The correspondence indices differ from the completed paper review.')
    return review


paper_review = completed_paper_review()


def check_dependencies():
    """Require the exact pristine Git sources recorded for every dependency."""
    revisions = {}
    for package in manifest['packages']:
        if package['type'] != 'git':
            raise SystemExit('Unpinned non-Git dependency: ' + package['name'])
        path = str(ROOT / manifest['packagesDir'] / package['name'])
        revision = run(['git', '-C', path, 'rev-parse', 'HEAD']).strip()
        if revision != package['rev']:
            raise SystemExit('Dependency checkout differs from the pinned revision: '
                             + package['name'])
        if run(['git', '-C', path, 'status', '--porcelain',
                '--untracked-files=no']).strip():
            raise SystemExit('Dependency has tracked local modifications: '
                             + package['name'])
        for ignored in [False, True]:
            command = ['git', '-C', path, 'ls-files', '-z', '--others']
            if ignored:
                command.append('--ignored')
            command += ['--exclude-standard', '--', '*.lean']
            for name in filter(None, run(command).split('\0')):
                parts = Path(name).parts
                cache = any(parts[i] == '.lake' and parts[i + 1] in ['build', 'packages']
                            for i in range(len(parts) - 1))
                if not cache:
                    raise SystemExit('Untracked Lean dependency source outside build caches: '
                                     + package['name'] + '/' + name)
        revisions[package['name']] = revision
    return revisions


dependency_revisions = check_dependencies()
if args.require_current_modules:
    run(['lake', '--no-build', 'build'] + sorted(expected_imports),
        'module-cache-check.log')
    print('Every module export is current according to Lake.', flush=True)
if args.serial:
    for module in module_build_order(modules):
        print(f'Checking {module}', flush=True)
        run(['lake', 'build', module], module + '.build.log')
run(['lake', 'build'], 'build.log')
print('Full build passed.', flush=True)
audit = run(['lake', 'env', 'lean', 'CheckAxioms.lean'], 'axioms.txt')
entries = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit, re.S)
empty_entries = re.findall(r"'([^']+)' does not depend on any axioms", audit)
seen = [name for name, _ in entries] + empty_entries
if len(seen) != len(expected_names) or set(seen) != set(expected_names):
    raise SystemExit('Axiom report does not cover exactly the requested theorem names.')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
used = set()
for name, dependencies in entries:
    axioms = {v.strip() for v in dependencies.split(',') if v.strip()}
    if axioms - allowed:
        raise SystemExit(f'Unexpected axiom dependency in {name}: {axioms - allowed}')
    used.update(axioms)

lean_version = run(['lake', 'env', 'lean', '--version']).strip()
hashes = source_hashes()
if hashes != before_hashes or modules != proof_sources():
    raise SystemExit('Project sources changed during verification; no certificate was written.')
if check_dependencies() != dependency_revisions:
    raise SystemExit('Dependencies changed during verification; no certificate was written.')
summary = {
    'status': ('checked relative formalization; all paper claims reviewed' if paper_review else
               'checked partial formalization; paper not fully certified'),
    'checked_at_utc': datetime.now(timezone.utc).isoformat(),
    'lean_version': lean_version,
    'mathlib_revision': mathlib,
    'dependency_revisions': dependency_revisions,
    'proof_modules': len(modules),
    'public_theorems_audited': len(expected_names),
    'full_build_passed': True,
    'axiom_audit_passed': True,
    'paper_correspondence_review_passed': paper_review is not None,
    'axioms_used': sorted(used),
    'source_sha256': hashes,
}
(OUT / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
coverage_note = (
    '**Checked relative formalization. All paper claims have a recorded source review.**\n\n'
    if paper_review else
    '**Partial formalization. The main theorems of the paper are not yet certified.**\n\n')
coverage_limit = (
    'The paper-to-source review is recorded in `correspondence/completed-review.json`; '
    'its proof and correspondence hashes must match before this status is issued. '
    'The results remain conditional on the cited general background identities '
    'listed in [ASSUMPTIONS.md](../ASSUMPTIONS.md). '
    'Those inputs are explicit theorem parameters, not new Lean axioms.\n'
    if paper_review else
    'These checks establish the statements in the Lean sources. '
    'They do not establish missing hypotheses or the unformalized correspondence '
    'with modular forms, L-functions, and the paper’s principal conclusions. '
    'See [the proof-coverage ledger](../ASSUMPTIONS.md).\n')
(OUT / 'SUMMARY.md').write_text(
    '# Verification record\n\n'
    + coverage_note + f"Checked: {summary['checked_at_utc']}\n\n"
    f'- Toolchain: {lean_version}\n'
    f'- Mathlib revision: `{mathlib}`\n'
    f'- Proof modules: {len(modules)}; every module imported by `DepthAspect.lean`.\n'
    f'- Public theorems checked for axiom dependencies: {len(expected_names)}.\n'
    '- Full project build: passed.\n'
    '- Only foundational axioms used: ' + ', '.join(f'`{a}`' for a in sorted(used)) + '.\n'
    '- No `sorry`, `admit`, paper-specific `axiom`, `native_decide`, or `unsafe` '
    'declarations in the proof modules.\n\n'
    'Run `python3 scripts/verify.py` from the project directory to repeat these checks. '
    'The source hashes in `summary.json` identify the precise checked files. '
    'The complete outputs are in `build.log` and `axioms.txt`.\n\n'
    + coverage_limit)
print(f'Passed: {len(modules)} modules, {len(expected_names)} theorem dependency audits.', flush=True)
