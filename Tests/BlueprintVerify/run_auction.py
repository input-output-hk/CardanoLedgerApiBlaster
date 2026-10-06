#!/usr/bin/env python3
"""Recompile/generate and check the detached Plutus Auction bundle.
Run from CardanoLedgerApiBlaster: lake env python3 Tests/BlueprintVerify/run_auction.py GENERATOR OUTPUT
The generator is Plutus's example-ual-auction executable. Build the checker and
CardanoLedgerApi.Examples.Auction before running. No stored evidence is trusted.
"""
import copy
import os
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

repo = Path(__file__).resolve().parents[2]
generator = Path(sys.argv[1]).resolve()
out = Path(sys.argv[2]).resolve()
out.mkdir(parents=True, exist_ok=True)
for name in ['run-report.json', 'verified-assurance.json', 'Check.log']:
    (out / name).unlink(missing_ok=True)
sys.path.insert(0, str(repo.parent / 'PlutusCoreBlaster/Tests/BlueprintVerify'))
from runtime import lean_command
lean_args = lean_command()
native = os.environ.get('ASSURANCE_NATIVE_LIBRARY')
child_env = os.environ.copy()

header = 'import PlutusCore.UPLC.BlueprintEncoding.Assurance\nimport CardanoLedgerApi.Examples.Auction\n'

def run(name, source, timeout=1200):
    path = out / (name + '.lean')
    path.write_text(header + source)
    p = subprocess.run(lean_args + [str(path)], cwd=repo, env=child_env, text=True, capture_output=True, timeout=timeout)
    log = p.stdout + p.stderr
    (out / (name + '.log')).write_text(log)
    return p.returncode, log

def digest(path):
    return {'alg': 'sha256', 'digest': hashlib.sha256(path.read_bytes()).hexdigest()}

def write(path, obj):
    path.write_text(json.dumps(obj, indent=2) + '\n')

code, log = run('Environment', f'#write_checking_environment {json.dumps(str(out / "environment.json"))}\n')
if code: raise RuntimeError(log)
subprocess.run([str(generator), 'environment.json'], cwd=out, check=True, timeout=120)
doc = json.loads((out / 'assurance.json').read_text())
bp = json.loads((out / 'plutus.json').read_text())
assert set(doc['functions']) == {'outbids'}
assert [v['id'] for v in bp['validators']] == ['auction']
assert 'functions' not in bp
evaluation = (repo / 'Tests/BlueprintVerify/EvaluateAuction.lean').read_text().replace('"plutus.json"', json.dumps(str(out / 'plutus.json')))
code, log = run('Evaluate', evaluation)
print(log, end='', flush=True)
if code: raise RuntimeError('Concrete Auction execution failed')

expected = {'outbids_exact', 'first_bid_exact', 'existing_bid_exact', 'payout_exact', 'malformed_context'}
expected.update({'audit_newBid_success_requires_output_locks_bid', 'audit_valid_newBid_succeeds', 'audit_demo_valid_bid_accepted', 'audit_newBid_accepts_dust_tokens', 'audit_payout_success_pays_seller_highest_bid', 'audit_newBid_success_requires_before_deadline', 'audit_nb_wrong_policy_rejected', 'audit_payout_staked_outputs_accepted', 'audit_newBid_success_requires_sufficient_bid', 'audit_payout_success_requires_after_deadline', 'audit_newBid_accepts_minimal_increment', 'audit_valid_payout_with_bid_succeeds', 'audit_payout_double_satisfaction', 'audit_newBid_success_requires_bigger_bid', 'audit_nb_datum_wrong_bid_rejected', 'audit_nb_other_redeemer_rejected', 'audit_nb_datum_hash_rejected', 'audit_valid_payout_no_bid_succeeds', 'audit_payout_success_positive_seller_payment', 'audit_nb_wrong_token_name_rejected', 'audit_newBid_success_requires_single_nft', 'audit_newBid_ignores_minting', 'audit_nb_datum_missing_rejected', 'audit_newBid_success_positive_bid', 'audit_payout_success_transfers_asset', 'audit_payout_success_positive_asset'})
def check_property(prop):
    claim = copy.deepcopy(doc)
    claim['properties'] = [prop]
    claim_path = out / ('claim-' + prop['id'] + '.json')
    write(claim_path, claim)
    print('Checking', prop['id'], flush=True)
    code, log = run('Check-' + prop['id'], f'#verify_blueprint Auction {json.dumps(str(claim_path))}\n')
    print(log, end='', flush=True)
    if code or set(re.findall(r"Property '([^']+)': verified", log)) != {prop['id']}:
        raise RuntimeError('Auction claim failed: ' + prop['id'])
    return log

with ThreadPoolExecutor(max_workers=3) as workers:
    logs = list(workers.map(check_property, doc['properties']))
if {p['id'] for p in doc['properties']} != expected:
    raise RuntimeError('Unexpected Auction claim set')
(out / 'Check.log').write_text(''.join(logs))

# Isolate the helper claim and mutate actual inputs to the checker.
helper = copy.deepcopy(doc)
helper['properties'] = [p for p in helper['properties'] if p['id'] == 'outbids_exact']
helper['formalFragments'] = []
helper['properties'][0]['statement']['formal'].pop('uses', None)
checks = []
def reject(name, change, expected):
    d = copy.deepcopy(helper)
    change(d)
    path = out / (name + '.json')
    write(path, d)
    code, log = run(name, f'#verify_blueprint Negative {json.dumps(str(path))}\n')
    if code == 0 or expected.lower() not in log.lower():
        raise AssertionError(f'{name}: expected {expected!r}\n{log}')
    checks.append(name)
    print('PASS', name, flush=True)

reject('tampered-code', lambda d: d['functions']['outbids'].update(compiledCode='00'), 'function compiledCode hash mismatch')
reject('missing-result', lambda d: d['functions']['outbids'].pop('result'), "missing 'result'")
reject('unknown-function', lambda d: d['properties'][0]['scope'].update(functions=['missing']), 'unknown scoped function')
reject('disconnected-claim', lambda d: d['properties'][0]['statement']['formal'].update(source='True'), 'does not depend on scoped function')
reject('false-helper-claim', lambda d: d['properties'][0]['statement']['formal'].update(source='∀ (old proposed : Integer), outbids_returns old proposed true'), 'falsified')
def bind_interface(d, filename):
    key = d['properties'][0]['checkingContext']
    ctx = json.loads((out / d['checkingContexts'][key]['uri']).read_text())
    ctx['targets'][0]['functionInterface'] = {k:v for k,v in d['functions']['outbids'].items() if k not in ['compiledCode','hash']}
    ctx['targets'][0]['functionInterface']['definitions'] = d.get('definitions', {})
    path = out / filename
    write(path, ctx)
    d['checkingContexts'][key] = {'uri':path.name, 'hash':digest(path)}

reject('stale-function-interface', lambda d: d['functions']['outbids']['arguments'].__setitem__(0, {'dataType':'integer'}), 'checking function interface mismatch')

def wrong_argument(d):
    d['functions']['outbids']['arguments'][0] = {'dataType':'integer'}
    bind_interface(d, 'data-argument-context.json')
    d['properties'][0]['statement']['formal']['source'] = '∀ (old proposed : Integer), outbids_returns (Data.I old) proposed (decide (old < proposed))'
reject('wrong-argument-wire', wrong_argument, 'falsified')
# Same bytes, result representation changed: this must falsify, not relabel, the return.
def wrong_result(d):
    d['functions']['outbids']['result'] = {}
    bind_interface(d, 'data-result-context.json')
    d['properties'][0]['statement']['formal']['source'] = '∀ (old proposed : Integer), outbids_returns old proposed (Data.Constr (if old < proposed then 1 else 0) [])'
reject('wrong-result-wire', wrong_result, 'falsified')
# Exact result checking must reject fuel exhaustion.
def exhausted(d):
    key = d['properties'][0]['checkingContext']
    ctx = json.loads((out / d['checkingContexts'][key]['uri']).read_text())
    ctx['execution']['budget']['steps'] = 0
    path = out / 'exhausted-context.json'
    write(path, ctx)
    d['checkingContexts'][key] = {'uri': path.name, 'hash': digest(path)}
reject('exhausted-function', exhausted, 'falsified')

def bad_context(d):
    key = d['properties'][0]['checkingContext']
    ctx = json.loads((out / d['checkingContexts'][key]['uri']).read_text())
    ctx['targets'][0]['functionHash']['digest'] = '00' * 32
    path = out / 'wrong-function-context.json'; write(path, ctx)
    d['checkingContexts'][key] = {'uri': path.name, 'hash': digest(path)}
reject('wrong-context-function-hash', bad_context, 'checking function hash mismatch')

def empty_evidence_hashes(d):
    key = d['properties'][0]['checkingContext']
    d['tools'] = {'blaster': {'name':'Blaster','version':'test'}}
    d['properties'][0]['evidence'] = [{'method':'smt-check','verifier':'test','tool':'blaster',
        'outcome':'verified','date':'2026-10-06','functionHashes':{},
        'checkingContextHash':d['checkingContexts'][key]['hash'],
        'artifact':{'uri':'environment.json','hash':digest(out / 'environment.json')}}]
reject('empty-function-evidence-hashes', empty_evidence_hashes, 'too few properties')

# Upstream's two expected counterexamples: successful executions disprove
# these universally failing scripts. Keep the real context and fragment closure.
for name, source in [
    ('newBid-always-fails', '∀ (old proposed locked refund tokens hi : Integer), ¬ auditBid auction old proposed locked refund tokens hi'),
    ('payout-always-fails', '∀ (bid paid tokens lo : Integer), ¬ auditPayout auction bid paid tokens lo')]:
    claim = copy.deepcopy(doc)
    claim['properties'] = [copy.deepcopy(next(p for p in doc['properties'] if p['id'] == 'first_bid_exact'))]
    claim['properties'][0]['statement']['formal']['source'] = source
    path = out / (name + '.json')
    write(path, claim)
    code, log = run(name, f'#verify_blueprint Counterexample {json.dumps(str(path))}\n')
    if code == 0 or 'falsified' not in log.lower():
        raise AssertionError(f'{name}: expected a counterexample\n{log}')
    checks.append(name)
    print('PASS', name, flush=True)

def revision(path):
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=path, text=True).strip()
    branch = subprocess.check_output(['git', 'branch', '--show-current'], cwd=path, text=True).strip()
    patch = subprocess.check_output(['git', '-c', 'core.fsmonitor=false', 'diff', 'HEAD', '--binary'], cwd=path)
    return {'commit':commit, 'branch':branch, 'trackedDiffSha256':hashlib.sha256(patch).hexdigest()}

plutus = next((p for p in generator.parents if (p / 'plutus-tx').is_dir()), None)
checker = next((Path(p).resolve().parents[3] for p in os.environ.get('LEAN_PATH','').split(os.pathsep)
                if (Path(p) / 'PlutusCore/UPLC/BlueprintEncoding/Assurance.olean').is_file()), None)
source_inputs = [Path(__file__), repo / 'Tests/BlueprintVerify/EvaluateAuction.lean', repo / 'CardanoLedgerApi/Examples/Auction.lean']
if plutus:
    source_inputs += list((plutus / 'doc/docusaurus/static/code/Example/Ual/Auction').glob('*.hs'))
    source_inputs += [plutus / 'doc/docusaurus/static/code/AuctionValidator.hs', plutus / 'plutus-tx/src/PlutusTx/Assurance/Interface.hs']
if checker:
    source_inputs += list((checker / 'PlutusCore/UPLC/BlueprintEncoding').glob('*.lean'))
    source_inputs += list((checker / 'PlutusCore/UPLC/BlueprintEncoding').glob('*.schema.json'))
    source_inputs += [checker / 'PlutusCore/UPLC/CekMachine.lean']
repos = {'ledger':repo}
if plutus: repos['plutus'] = plutus
if checker: repos['checker'] = checker
if native: repos['blaster'] = Path(native).resolve().parents[3]
provenance = {'repositories':{name:revision(path) for name,path in repos.items()},
              'sources':{str(path):digest(path) for path in source_inputs},
              'leanVersion':subprocess.check_output(['lean','--version'], text=True).strip(),
              'solverVersion':subprocess.check_output(['z3','--version'], text=True).strip()}

report = {'status':'verified', 'provenance':provenance, 'properties':sorted(expected), 'negativeChecks':checks,
          'generator':str(generator), 'generatorHash':digest(generator),
          'nativeBlaster':({'path':native, 'hash':digest(Path(native))} if native else None),
          'blueprintHash':digest(out / 'plutus.json'), 'assuranceHash':digest(out / 'assurance.json'),
          'upstreamAuctionCommit':'9938562fd452351655fe2f6b63e583c62422687c',
          'scope':'Current Plinth compilation; bounded upstream bid/payout context shapes and standalone helper. No compiler-linking proof or ledger-validity claim.',
          'trust':'Blaster SMT, no reconstructed Lean kernel proof.'}
write(out / 'run-report.json', report)
# Keep evidence separate from the generated, unverified input document.
verified = copy.deepcopy(doc)
verified.setdefault('tools', {})['blaster'] = {'name':'Blaster', 'version':'loaded-environment',
    'description':'Exact Lean modules and solver are pinned by each checking context.'}
for prop in verified['properties']:
    key = prop['checkingContext']
    evidence = {'method':'smt-check', 'verifier':'Blaster', 'tool':'blaster',
        'outcome':'verified', 'date':datetime.now(timezone.utc).date().isoformat(),
        'checkingContextHash':doc['checkingContexts'][key]['hash'],
        'artifact':{'uri':'run-report.json', 'hash':digest(out / 'run-report.json')},
        'notes':report['scope'] + ' ' + report['trust']}
    if prop['scope'].get('validators'):
        evidence['scriptHash'] = bp['validators'][0]['hash']
    if prop['scope'].get('functions'):
        evidence['functionHashes'] = {fid:doc['functions'][fid]['hash'] for fid in prop['scope']['functions']}
    prop['evidence'] = [evidence]
write(out / 'verified-assurance.json', verified)
print('PASS',len(expected),'Auction claims and', len(checks), 'negative checks', flush=True)
