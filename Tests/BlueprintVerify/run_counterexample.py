#!/usr/bin/env python3
"""Generate a source-level Auction ScriptContext counterexample and replay it.

The original correct source and compiled validator are preserved. A copied
first_bid_exact annotation changes the minimum bid from 100 to 101.
"""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

repo = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(repo.parent / 'PlutusCoreBlaster/Tests/BlueprintVerify'))
from runtime import lean_command
from counterexample_source import context_replay_source, haskell

HEADER = '''import PlutusCore.UPLC.BlueprintEncoding.Assurance
import CardanoLedgerApi.Counterexample.V3
open PlutusCore.ByteString
open PlutusCore.Integer
open PlutusCore.Data (Data)
open CardanoLedgerApi.IsData.Class
open CardanoLedgerApi.V3
open CardanoLedgerApi.V3.Contexts
open CardanoLedgerApi.V3.Tx
'''


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


def run(command, cwd, log, expected=0, env=None):
    result = subprocess.run(list(map(str, command)), cwd=cwd, text=True,
                            capture_output=True, timeout=300, env=env)
    log.write_text(result.stdout + result.stderr)
    if result.returncode != expected:
        raise RuntimeError(f'{log}: expected {expected}, got {result.returncode}\n'
                           + result.stdout + result.stderr)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--generator', type=Path, required=True)
    parser.add_argument('--plutus', type=Path, required=True)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--z3', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--ghc', default='ghc')
    args = parser.parse_args()
    args.output = args.output.resolve()
    args.output.mkdir(parents=True, exist_ok=True)
    args.generator = args.generator.resolve(strict=True)
    args.plutus = args.plutus.resolve(strict=True)
    args.source = args.source.resolve(strict=True)
    if (args.output / 'FormalSpec.hs').resolve() == args.source:
        parser.error('Use a separate output directory')
    for name in ['counterexample.json', 'property-result.json', 'ScriptContext.hs']:
        (args.output / name).unlink(missing_ok=True)
    source_hash = digest(args.source)
    os.environ['PATH'] = str(args.z3.resolve(strict=True).parent) + os.pathsep + os.environ['PATH']
    lean = lean_command()
    driver = args.output / 'Environment.lean'
    environment = args.output / 'environment.json'
    driver.write_text(HEADER + '#write_checking_environment ' + json.dumps(str(environment)) + '\n')
    run(lean + [driver], repo, args.output / 'environment.log')
    run([args.generator, environment.name], args.output, args.output / 'generator.log')
    doc = json.loads((args.output / 'assurance.json').read_text())
    doc['properties'] = [p for p in doc['properties'] if p['id'] == 'first_bid_exact']
    if len(doc['properties']) != 1:
        raise RuntimeError('Expected first_bid_exact')
    original = args.source.read_text()
    block = re.search(r'\{-@\s*PROPERTY\s+\[scope:\s*auction\]\s+first_bid_exact\b[\s\S]*?@-\}', original)
    if not block or block.group().count('100 ≤ proposed') != 1:
        raise RuntimeError('Unexpected source property')
    source_copy = args.output / 'FormalSpec.hs'
    source_copy.write_text(original[:block.start()] + block.group().replace('100 ≤ proposed', '101 ≤ proposed')
                           + original[block.end():])
    for label in ['correct', 'false']:
        claim = copy.deepcopy(doc)
        if label == 'false':
            formal = claim['properties'][0]['statement']['formal']
            if formal['source'].count('100 ≤ proposed') != 1:
                raise RuntimeError('Unexpected generated property')
            formal['source'] = formal['source'].replace('100 ≤ proposed', '101 ≤ proposed')
        claim_file = args.output / f'{label}.json'
        report_file = args.output / f'{label}-report.json'
        report_file.unlink(missing_ok=True)
        write(claim_file, claim)
        driver = args.output / f'{label.capitalize()}.lean'
        driver.write_text(HEADER + '#verify_blueprint Cex ' + json.dumps(str(claim_file))
                          + ' cex_report ' + json.dumps(str(report_file)) + '\n')
        run(lean + [driver], repo, args.output / f'{label}.log', 0 if label == 'correct' else 1)
        report = json.loads(report_file.read_text())
        if report['assuranceSha256'] != digest(claim_file) or report['blueprintSha256'] != digest(args.output / 'plutus.json'):
            raise RuntimeError('Report input digest mismatch')
        result = report['results'][0]
        if result['outcome'] != ('verified' if label == 'correct' else 'falsified'):
            raise RuntimeError(f'Unexpected outcome: {result}')
        if label == 'correct':
            continue
        cex = result['counterexample']
        replay = cex['replay']
        if replay.get('status') != 'confirmed' or replay['propertyHolds']:
            raise RuntimeError(f'Replay did not confirm the counterexample: {replay}')
        calls = replay.get('calls', [])
        if len(calls) != 1 or calls[0]['outcome'] != 'halted':
            raise RuntimeError(f'Expected one successful compiled Auction call: {calls}')
        call = calls[0]
        if len(call['arguments']) != 1 or call['arguments'][0]['error']:
            raise RuntimeError('Missing exact wire argument')
        wire = call['arguments'][0]['value']
        contexts = [s['argument']['value'] for s in call['sourceArguments']
                    if not s['argument']['error'] and s['argument']['value'].get('kind') == 'encoded'
                    and s['argument']['value'].get('type') == 'PlutusLedgerApi.V3.ScriptContext']
        contexts = list({json.dumps(c, sort_keys=True): c for c in contexts}.values())
        if len(contexts) != 1:
            raise RuntimeError('Expected one source ScriptContext before Data encoding')
        haskell_source = context_replay_source(contexts[0], wire)
        context_file = args.output / 'ScriptContext.hs'
        context_file.write_text(haskell_source)
        binary = args.output / 'check-haskell-context'
        build_dir = args.output / 'haskell-build'
        build_dir.mkdir(exist_ok=True)
        # Lake's native-library search path contains Lean's LLVM. Do not let
        # that override the independent GHC/clang toolchain's own libraries.
        haskell_env = os.environ.copy()
        for name in ['DYLD_LIBRARY_PATH', 'LD_LIBRARY_PATH']:
            haskell_env.pop(name, None)
        run(['cabal', 'exec', '--project-file=cabal.assurance.project', '--with-compiler=' + args.ghc, '--',
             args.ghc, '-XImportQualifiedPost', '-package', 'plutus-ledger-api', '-package', 'bytestring',
             '-outputdir', build_dir, '-o', binary, context_file],
            args.plutus, args.output / 'haskell-build.log', env=haskell_env)
        run([binary], args.output, args.output / 'haskell-roundtrip.log', env=haskell_env)
        values = {b['name']: haskell(b['value']) for b in cex['model']['bindings'] if not b['error']}
        if set(values) != {'proposed', 'locked', 'tokens', 'hi'}:
            raise RuntimeError('Incomplete source inputs')
        if digest(args.source) != source_hash:
            raise RuntimeError('Original Haskell source changed during the run')
        result.update({'source': str(source_copy), 'sourceSha256': digest(source_copy),
                       'originalSource': str(args.source), 'originalSourceSha256': source_hash,
                       'generatorSha256': digest(args.generator),
                       'contextSource': str(context_file), 'contextSourceSha256': digest(context_file),
                       'haskellRoundtrip': 'passed', 'report': str(report_file),
                       'reportSha256': digest(report_file)})
        write(args.output / 'counterexample.json', result)
        write(args.output / 'property-result.json', {
            'property': 'first_bid_exact', 'outcome': 'falsified',
            'source': str(source_copy), 'sourceSha256': digest(source_copy),
            'method': 'Blaster SMT, typed context capture, CEK replay and Haskell round trip',
            'counterexample': values, 'structuredCounterexample': cex,
            'haskell': haskell_source, 'log': str(args.output / 'false.log'),
        })
        print('Source inputs:', values)
        print('PASS original claim; false mutation; exact compiled-validator input; confirmed CEK replay')
        print('PASS Haskell ScriptContext decode and exact Data round trip')
        print('Artifact:', context_file)


if __name__ == '__main__':
    main()
