"""Mapped function checks through the CLI, including replay and Lean exports."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
CLI = ROOT / '.lake/build/bin/uplc_equiv'
EXAMPLES = ROOT / 'equivalence/examples/mappings'


class MappingProcess(unittest.TestCase):
    def test_playground_entry_point(self):
        result = subprocess.run(['lake', 'env', 'lean', str(EXAMPLES / 'Playground.lean')],
                                cwd=ROOT, capture_output=True, text=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('"verdict": "equivalent"', result.stdout)

    def check_mapping(self, mapping, *, old=None, new=None, flags=()):
        result = subprocess.run([
            str(CLI), str(old or EXAMPLES / 'old.uplc'), str(new or EXAMPLES / 'new.uplc'),
            '--mode', 'function', '--mapping', str(mapping), '--steps', '200',
            '--timeout', '20', '--wall-timeout', '60', '--json', *flags,
        ], cwd=ROOT, capture_output=True, text=True, timeout=70)
        return result, json.loads(result.stdout)

    def check_export(self, path):
        checked = subprocess.run(['lake', 'env', 'lean', '--memory=8192', str(path)],
                                 cwd=ROOT, capture_output=True, text=True, timeout=70)
        self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

    def test_mapping_and_export(self):
        with tempfile.TemporaryDirectory() as directory:
            exported = Path(directory) / 'mapping.lean'
            result, report = self.check_mapping(EXAMPLES / 'mapping.json',
                                               flags=('--emit-lean', str(exported)))
            self.assertEqual((result.returncode, report['verdict']), (0, 'equivalent'), report)
            self.assertEqual(report['mapping_plan']['sourceCount'], 2)
            self.assertEqual(report['mapping_plan']['extraCount'], 1)
            self.assertIn('outside', report['mapping_scope'])
            self.assertNotIn('counterexample', report)
            self.assertIn('Mapping.same', exported.read_text())
            self.assertIn('extra0', exported.read_text())
            self.check_export(exported)

    def test_wrong_scale_and_enabled_feature_replay(self):
        original = json.loads((EXAMPLES / 'mapping.json').read_text())
        with tempfile.TemporaryDirectory() as directory:
            mapping = Path(directory) / 'mapping.json'
            for factor, bonus in [(1, 0), (100, 5)]:
                with self.subTest(factor=factor, bonus=bonus):
                    spec = copy.deepcopy(original)
                    spec['target'][0]['quantity']['unitsPerWhole'] = factor * 100
                    spec['target'][3]['fixed'] = bonus
                    mapping.write_text(json.dumps(spec))
                    result, report = self.check_mapping(mapping)
                    self.assertEqual((result.returncode, report['verdict']), (1, 'inequivalent'), report)
                    witness = report['counterexample']
                    self.assertTrue(witness['replayed'])
                    amount, rate = (witness['input']['source'][key] for key in ('amount', 'rate'))
                    self.assertEqual(witness['old_arguments'], [{'integer': amount}, {'integer': rate}])
                    args = witness['new_arguments']
                    self.assertEqual([args[i]['integer'] for i in (0, 1, 3)], [rate * factor, amount, bonus])
                    self.assertNotEqual(amount * rate // 100, amount * (rate * factor) // 10000 + bonus)

    def test_identical_programs_do_not_bypass_mapping_or_export(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            script, mapping, exported = (root / name for name in ('identity.uplc', 'mapping.json', 'identity.lean'))
            script.write_text('(program 1.1.0 (lam x x))')
            mapping.write_text(json.dumps({
                'source': [{'name': 'x', 'unitsPerWhole': 1}],
                'target': [{'quantity': {'name': 'x', 'unitsPerWhole': 2}}],
                'oldOutput': 'constant', 'newOutput': 'constant',
            }))
            result, report = self.check_mapping(mapping, old=script, new=script,
                                               flags=('--emit-lean', str(exported)))
            self.assertEqual((result.returncode, report['verdict']), (1, 'inequivalent'), report)
            self.assertTrue(report['counterexample']['replayed'])
            self.assertNotIn('program_identity', report['queries'])
            self.assertIn('Mapping.same', exported.read_text())
            self.check_export(exported)

    def test_invalid_schema_and_unsupported_scope(self):
        with tempfile.TemporaryDirectory() as directory:
            mapping = Path(directory) / 'mapping.json'
            spec = json.loads((EXAMPLES / 'mapping.json').read_text())
            spec['target'] = []
            mapping.write_text(json.dumps(spec))
            result, report = self.check_mapping(mapping)
            self.assertEqual(result.returncode, 3, report)
            self.assertIn('missing', report['explanation'])
        for flags in [('--bounded',), ('--mode', 'validator'), ('--inputs', 'data')]:
            with self.subTest(flags=flags):
                result, report = self.check_mapping(EXAMPLES / 'mapping.json', flags=flags)
                self.assertEqual((result.returncode, report['verdict']), (3, 'error'), report)


if __name__ == '__main__':
    unittest.main()
