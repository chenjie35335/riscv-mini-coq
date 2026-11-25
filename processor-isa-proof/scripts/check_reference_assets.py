#!/usr/bin/env python3
"""Source-only build of the shared-semantics and same-reference proof bundles.

Copies shared FIRRTL library .v sources, never existing .vo files. Compiles the
needed local closure in a fresh external directory, audits bundled theorem
assumptions, and recursively checks all bundle modules. This is not a DUT proof.
"""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import hashlib
import json
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import tempfile


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--library-root', type=Path, required=True, help='firrtl2coq source checkout')
    ap.add_argument('--tool-bin', type=Path, help='Directory containing coqc, coqdep and coqchk')
    ap.add_argument('--build-dir', type=Path, help='New or empty directory outside skill/library')
    ap.add_argument('--jobs', type=int, default=4, help='Maximum concurrent compilers')
    ap.add_argument('--timeout', type=int, default=600, help='Seconds per tool invocation')
    args = ap.parse_args()
    if args.jobs < 1 or args.timeout < 1:
        ap.error('jobs and timeout must be positive')
    skill = Path(__file__).resolve().parents[1]
    library = args.library_root.resolve()
    build = (args.build_dir or Path(tempfile.mkdtemp(prefix='shared-reference-proof-'))).resolve()
    for source in (skill, library):
        if build == source or source in build.parents:
            ap.error('Build directory must be outside skill and library source trees')
    build.mkdir(parents=True, exist_ok=True)
    if any(build.iterdir()):
        ap.error('Build directory must be empty')
    tools = {}
    for name in ('coqc', 'coqdep', 'coqchk'):
        tool = str(args.tool_bin / name) if args.tool_bin else shutil.which(name)
        if not tool or not Path(tool).is_file():
            ap.error('Tool not found: ' + name)
        tools[name] = str(Path(tool).resolve())
    print('Build directory: ' + str(build), flush=True)
    copied = {}

    def copy_source(source, relative):
        target = build / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        copied[str(relative)] = digest(target)

    for directory in ('src', 'lib/nbits', 'lib/simplssrlib'):
        files = sorted((library / directory).rglob('*.v'))
        if not files:
            ap.error('Missing library sources: ' + directory)
        for source in files:
            copy_source(source, Path('firrtl2coq') / source.relative_to(library))
    bundles = ['shared-semantics', 'same-reference']
    modules = {}
    for bundle in bundles:
        files = sorted((skill / 'assets' / bundle / 'coq').glob('*.v'))
        if not files:
            ap.error('Missing bundle: ' + bundle)
        for source in files:
            if source.stem in modules:
                ap.error('Duplicate logical module: ' + source.stem)
            relative = Path(bundle) / source.name
            modules[source.stem] = relative
            copy_source(source, relative)
    flags = ['-Q', 'firrtl2coq/lib/simplssrlib', 'simplssrlib',
             '-Q', 'firrtl2coq/lib/nbits', 'nbits', '-R', 'firrtl2coq/src', 'firrtl',
             '-Q', 'shared-semantics', '', '-Q', 'same-reference', '']
    report = {'scope': 'Extracted shared/reference proofs only, not target DUT correctness',
              'status': 'running', 'source_sha256': copied, 'commands': [],
              'tool_sha256': {k: digest(Path(v)) for k, v in tools.items()}}

    def save():
        (build / 'report.json').write_text(json.dumps(report, indent=2) + '\n')

    def run(command, log):
        with (build / log).open('w') as stream:
            result = subprocess.run(command, cwd=build, stdout=stream,
                                    stderr=subprocess.STDOUT, timeout=args.timeout)
        if result.returncode:
            raise RuntimeError('Command failed: ' + shlex.join(command) + '\n' +
                               (build / log).read_text()[-5000:])
        return (build / log).read_text()

    try:
        report['compiler'] = run([tools['coqc'], '--version'], 'version.log').strip()
        project = build / 'sources.project'
        project.write_text('\n'.join(shlex.quote(p) for p in sorted(copied)) + '\n')
        dep_command = [tools['coqdep'], *flags, '-f', project.name]
        report['commands'].append(dep_command)
        dep_log = run(dep_command, 'dependencies.log')
        if 'has not been found' in dep_log or 'module-not-found' in dep_log:
            raise RuntimeError('Unresolved dependency: inspect dependencies.log')
        graph = {}
        for line in dep_log.replace('\\\n', ' ').splitlines():
            if ':' not in line:
                continue
            lhs, rhs = line.split(':', 1)
            for target in shlex.split(lhs):
                if target.endswith('.vo'):
                    graph[target] = [x for x in shlex.split(rhs) if x.endswith('.vo')]
        closure = set()
        todo = [str(path.with_suffix('.vo')) for path in modules.values()]
        while todo:
            target = todo.pop()
            if target in closure:
                continue
            if target not in graph or str(Path(target).with_suffix('.v')) not in copied:
                raise RuntimeError('Dependency outside source inventory: ' + target)
            closure.add(target)
            todo.extend(graph[target])
        report['dependency_graph'] = {p: graph[p] for p in sorted(closure)}
        save()
        done, pending, running = set(), set(closure), {}

        def compile_one(target):
            log = target.replace('/', '__') + '.log'
            run([tools['coqc'], *flags, str(Path(target).with_suffix('.v'))], log)
            return target

        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            while pending or running:
                ready = sorted(p for p in pending if set(graph[p]) <= done)
                for target in ready[:args.jobs - len(running)]:
                    pending.remove(target)
                    running[pool.submit(compile_one, target)] = target
                if not running:
                    raise RuntimeError('Dependency cycle in remaining source closure')
                completed, _ = wait(running, return_when=FIRST_COMPLETED)
                for future in completed:
                    target = running.pop(future)
                    future.result()
                    done.add(target)
                    print(f'[{len(done)}/{len(closure)}] {target}', flush=True)
        # Audit all top-level checked theorem declarations, not only selected examples.
        theorem_names = []
        decl_pattern = r'(?m)^[ \t]*(?:Local\s+|Global\s+)?(?:Lemma|Theorem|Corollary|Proposition|Fact|Remark)\s+([A-Za-z_][A-Za-z0-9_\x27]*)\b'
        for module, path in sorted(modules.items()):
            text = (build / path).read_text()
            theorem_names.extend(module + '.' + name for name in re.findall(decl_pattern, text))
        audit_file = build / 'same-reference' / 'SharedReferenceAudit.v'
        audit_file.write_text('Require Import ' + ' '.join(sorted(modules)) + '.\n' +
                              '\n'.join('Print Assumptions ' + name + '.' for name in theorem_names) + '\n')
        run([tools['coqc'], *flags, str(audit_file.relative_to(build))], 'assumptions.log')
        audit = (build / 'assumptions.log').read_text()
        if 'Axioms:' in audit or audit.count('Closed under the global context') != len(theorem_names):
            raise RuntimeError('Non-closed or incomplete assumption audit: inspect assumptions.log')
        kernel_command = [tools['coqchk'], '-silent', *flags, *sorted(modules), 'SharedReferenceAudit']
        report['commands'].append(kernel_command)
        save()
        run(kernel_command, 'coqchk.log')
        report.update(status='passed', modules=sorted(modules), assumptions_audited=theorem_names,
                      all_audited_theorems_closed=True, coqchk_passed=True,
                      compiled_source_count=len(closure),
                      artifact_sha256={p: digest(build / p) for p in sorted(closure)})
        save()
        print(f'PASS: {len(modules)} bundle modules, {len(theorem_names)} theorem audits, '
              f'{len(closure)} source-only compiled modules, recursive coqchk.', flush=True)
        print('Report: ' + str(build / 'report.json'), flush=True)
    except Exception as error:
        report.update(status='failed', error=str(error))
        save()
        raise SystemExit(str(error)) from error


if __name__ == '__main__':
    main()
