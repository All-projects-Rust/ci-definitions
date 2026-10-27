"""Execute the real pre-checkout guard; never execute checked-out caller code."""
import hashlib
import json
import os
from pathlib import Path
import re
import textwrap
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
PATH = '.github/workflows/w10-required-api-compiler-migration.yml'
HOST = 'All-projects-Rust/ci-definitions'
SOURCE_SHA = 'a' * 40
# Synthetic execution-context fixture, not the future published definition pin.
DEFINITION_SHA = 'b' * 40
WORKFLOW_SHA256 = 'b39eb993f6d0f1c6bcc0ffadce547c031489db863db6cd56c269e30824ac6d58'
TAIL_SHA256 = '01320e6059cc5a1cbf20ce89890ace3fde1b6ef2625a465a06d83c25efb71f10'
ENV_SHA256 = '377dfe4bf05d34ca2079527f952e10617c8aa60bf232ad2ff0fc057f4fb9fb78'
KVM_EXPRESSION = "vars.W10_REQUIRED_COMPILER_KVM == '1' && !inputs.force_hosted && github.repository == 'All-projects-Rust/signalo' && github.repository_id == '1201945594' && github.repository_owner_id == '348736467'"


def definition():
    return dict(workflow_repository=HOST, workflow_file_path=PATH,
                workflow_sha=DEFINITION_SHA,
                workflow_ref=HOST + '/' + PATH + '@' + DEFINITION_SHA)


def guard(**changes):
    workflow = (ROOT / PATH).read_text()
    inline = textwrap.dedent(workflow.split("python3 - <<'PY'\n", 1)[1].split('          PY', 1)[0])
    env = dict(REPOSITORY='signalorust/signalo', REPOSITORY_ID='1201945594',
               OWNER_ID='345015266', EVENT='pull_request',
               EXPECTED_SOURCE_SHA=SOURCE_SHA, ACTUAL_SOURCE_SHA=SOURCE_SHA,
               DEFINITION=json.dumps(definition()), KVM='false')
    env.update(changes)
    with patch.dict(os.environ, env, clear=True):
        # The actual workflow launches plain python3. Outer -O must not silently
        # turn this replay into a different execution mode that removes guards.
        exec(compile(inline, '<actual-definition-guard>', 'exec', optimize=0), {})


class DefinitionContracts(unittest.TestCase):
    def test_current_and_target_caller_pairs_and_allowed_events(self):
        for repository, owner in [('signalorust/signalo', '345015266'),
                                  ('All-projects-Rust/signalo', '348736467')]:
            for event in ['pull_request', 'merge_group', 'workflow_dispatch']:
                with self.subTest(repository=repository, event=event):
                    guard(REPOSITORY=repository, OWNER_ID=owner, EVENT=event)

    def test_wrong_crossed_retired_and_forged_identity_refused(self):
        for changes in [dict(OWNER_ID='348736467'),
                        dict(REPOSITORY='All-projects-Rust/signalo'),
                        dict(REPOSITORY='signalo-rust/signalo', OWNER_ID='339811905'),
                        dict(REPOSITORY=HOST, REPOSITORY_ID='1435776151', OWNER_ID='348736467'),
                        dict(REPOSITORY='attacker/signalo'), dict(REPOSITORY_ID='1435776151'),
                        dict(EVENT='pull_request_target'), dict(EVENT='push'),
                        dict(ACTUAL_SOURCE_SHA=DEFINITION_SHA), dict(EXPECTED_SOURCE_SHA='main'),
                        dict(KVM='unknown')]:
            with self.subTest(changes=changes), self.assertRaises(AssertionError):
                guard(**changes)

    def test_definition_identity_requires_host_path_sha_and_exact_ref(self):
        for key, value in [('workflow_repository', 'signalorust/signalo'),
                           ('workflow_repository', 'attacker/ci-definitions'),
                           ('workflow_file_path', '.github/workflows/other.yml'),
                           ('workflow_sha', 'main'),
                           ('workflow_ref', HOST + '/' + PATH + '@main'),
                           ('workflow_ref', HOST + '/' + PATH + '@refs/heads/main'),
                           ('workflow_ref', HOST + '/' + PATH + '@' + SOURCE_SHA)]:
            with self.subTest(key=key, value=value), self.assertRaises(AssertionError):
                bad = definition()
                bad[key] = value
                guard(DEFINITION=json.dumps(bad))
        with self.assertRaises(AssertionError):
            guard(DEFINITION='{}')

    def test_disposable_guest_isolation_is_enforced_before_checkout(self):
        with patch('socket.gethostname', return_value='ordinary-runner'):
            with self.assertRaises(AssertionError):
                guard(KVM='true')
        with patch('socket.gethostname', return_value='signalo-w10-offline1'):
            with patch('pathlib.Path.exists', return_value=True):
                with self.assertRaises(AssertionError):
                    guard(KVM='true')
            with patch('pathlib.Path.exists', return_value=False):
                with patch('subprocess.run') as mount:
                    mount.return_value.stdout = 'share on /mnt type virtiofs (rw)'
                    with self.assertRaises(AssertionError):
                        guard(KVM='true')
                    mount.return_value.stdout = '/dev/vda on / type ext4 (rw)'
                    guard(KVM='true')

    def test_reviewed_definition_bytes_compiler_and_environment_unchanged(self):
        workflow = (ROOT / PATH).read_bytes()
        self.assertEqual(hashlib.sha256(workflow).hexdigest(), WORKFLOW_SHA256)
        source = workflow.decode()
        tail = '      - name: Setup Node.js' + source.split('      - name: Setup Node.js', 1)[1]
        self.assertEqual(hashlib.sha256(tail.encode()).hexdigest(), TAIL_SHA256)
        env = source.split('\nenv:\n', 1)[1].split('\njobs:', 1)[0]
        self.assertEqual(hashlib.sha256(env.encode()).hexdigest(), ENV_SHA256)
        self.assertNotIn('__DEFINITION_', source)
        self.assertIn('permissions:\n  contents: read\n', source)
        self.assertNotIn('secrets:', source)
        self.assertNotIn('secrets.', source)
        checkout = source.index('      - name: Checkout exact caller source')
        self.assertLess(source.index('      - name: Prove canonical definition'), checkout)
        contract = 'python3 -m unittest discover -s scripts/tests -p test_w10_required_compiler_controller.py'
        self.assertEqual(source.count(contract), 1)
        self.assertLess(checkout, source.index(contract))
        self.assertLess(source.index(contract), source.index('      - name: Setup Node.js'))
        self.assertIn('ref: ${{ inputs.expected_source_sha }}', source)
        self.assertIn('persist-credentials: false', source)

    def test_hosted_default_and_exact_target_disposable_scheduling(self):
        source = (ROOT / PATH).read_text()
        self.assertIn('        default: true\n', source)
        self.assertEqual(source.count(KVM_EXPRESSION), 2)
        self.assertIn("runs-on: ${{ " + KVM_EXPRESSION + " && fromJSON(format('[\"signalo-w10-required-compiler-{0}-{1}\"]', github.run_id, github.run_attempt)) || 'ubuntu-latest' }}", source)
        self.assertIn('KVM: ${{ ' + KVM_EXPRESSION + ' }}', source)

    def test_required_validation_runs_on_first_pr_without_paths_or_privilege(self):
        validation = (ROOT / '.github/workflows/definition-validation.yml').read_text()
        self.assertIn('on:\n  pull_request:\n    branches: [main]\n  push:\n    branches: [main]\n', validation)
        self.assertIn('permissions:\n  contents: read\n', validation)
        self.assertIn('    name: Definition validation\n', validation)
        self.assertIn('    runs-on: ubuntu-latest\n', validation)
        self.assertIn('persist-credentials: false', validation)
        self.assertRegex(validation, r'uses: actions/checkout@[0-9a-f]{40} # v7')
        self.assertIn("python3 -I -B -m unittest discover -s tests -p 'test_*.py' -v", validation)
        self.assertIn("python3 -I -O -B -m unittest discover -s tests -p 'test_*.py' -v", validation)
        for forbidden in ['pull_request_target', 'paths:', 'paths-ignore:', 'secrets:', 'secrets.',
                          'continue-on-error', 'always()', 'self-hosted', 'if:']:
            self.assertNotIn(forbidden, validation)


if __name__ == '__main__':
    unittest.main()
