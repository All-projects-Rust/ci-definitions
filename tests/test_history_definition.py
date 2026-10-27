"""Run the real pre-checkout guard with synthetic identities and no network."""
import base64
import hashlib
import json
import os
from pathlib import Path
import tempfile
import textwrap
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
PATH = '.github/workflows/history-redaction-verify.yml'
HOST = 'All-projects-Rust/ci-definitions'
SOURCE = 'a' * 40
BASE = 'b' * 40
DEFINITION = 'c' * 40


def definition():
    return dict(workflow_repository=HOST, workflow_file_path=PATH,
                workflow_sha=DEFINITION, workflow_ref=HOST + '/' + PATH + '@' + DEFINITION)


def guard(**changes):
    workflow = (ROOT / PATH).read_text()
    inline = textwrap.dedent(workflow.split("python3 -I - <<'PY'\n", 1)[1].split('          PY', 1)[0])
    with tempfile.TemporaryDirectory() as directory:
        output = Path(directory) / 'output'
        env = dict(REPOSITORY='signalorust/signalo', REPOSITORY_ID='1201945594',
                   OWNER_ID='345015266', EVENT='pull_request', SOURCE_SHA=SOURCE,
                   EXPECTED_SOURCE_SHA=SOURCE, EVENT_BASE_SHA=BASE, PHASE='legacy',
                   DESCRIPTOR_SHA256='', DESCRIPTOR_B64='',
                   DEFINITION=json.dumps(definition()), GITHUB_OUTPUT=str(output))
        env.update(changes)
        with patch.dict(os.environ, env, clear=True):
            exec(compile(inline, '<history-pre-checkout-guard>', 'exec', optimize=0), {})
        return output.read_text()


class HistoryDefinitionContracts(unittest.TestCase):
    def test_allowed_pairs_and_intrinsic_bases(self):
        for repository, owner in [('signalorust/signalo', '345015266'),
                                  ('All-projects-Rust/signalo', '348736467')]:
            for event in ['pull_request', 'merge_group']:
                self.assertEqual(guard(REPOSITORY=repository, OWNER_ID=owner, EVENT=event),
                                 'definition_sha=' + DEFINITION + '\n')

    def test_namespace_source_event_and_phase_substitutions_refused(self):
        for changes in [dict(OWNER_ID='348736467'), dict(REPOSITORY='All-projects-Rust/signalo'),
                        dict(REPOSITORY_ID='1435776151'), dict(REPOSITORY='other/signalo'),
                        dict(EVENT='push'), dict(EVENT='pull_request_target'),
                        dict(SOURCE_SHA=BASE), dict(EXPECTED_SOURCE_SHA='main'),
                        dict(EVENT_BASE_SHA=''), dict(EVENT_BASE_SHA='main'),
                        dict(PHASE=''), dict(PHASE='legacy', DESCRIPTOR_B64='e30='),
                        dict(PHASE='active', DESCRIPTOR_SHA256=''),
                        dict(EVENT='workflow_dispatch', EVENT_BASE_SHA='')]:
            with self.subTest(changes=changes), self.assertRaises((AssertionError, ValueError, KeyError)):
                guard(**changes)

    def test_exact_intrinsic_definition_is_required(self):
        for key, value in [('workflow_repository', 'signalorust/signalo'),
                           ('workflow_file_path', '.github/workflows/ci.yml'),
                           ('workflow_sha', 'main'),
                           ('workflow_ref', HOST + '/' + PATH + '@main'),
                           ('workflow_ref', HOST + '/' + PATH + '@' + SOURCE)]:
            bad = definition()
            bad[key] = value
            with self.subTest(key=key), self.assertRaises(AssertionError):
                guard(DEFINITION=json.dumps(bad))

    def test_manual_cutover_matches_externally_pinned_descriptor_bytes_and_tip(self):
        raw = json.dumps(dict(finalPublicationTip=SOURCE, trust=dict(cleanAnchor=BASE))).encode()
        profile = dict(PHASE='active', DESCRIPTOR_B64=base64.b64encode(raw).decode(),
                       DESCRIPTOR_SHA256=hashlib.sha256(raw).hexdigest(),
                       EVENT='workflow_dispatch', EVENT_BASE_SHA='')
        guard(**profile)
        for changes in [dict(SOURCE_SHA=BASE, EXPECTED_SOURCE_SHA=BASE),
                        dict(EVENT_BASE_SHA=BASE), dict(DESCRIPTOR_SHA256='d' * 64),
                        dict(DESCRIPTOR_B64=profile['DESCRIPTOR_B64'] + '\n')]:
            with self.subTest(changes=changes), self.assertRaises((AssertionError, ValueError)):
                guard(**(profile | changes))

    def test_workflow_runs_only_pinned_trusted_code_before_source_is_read_as_data(self):
        workflow = (ROOT / PATH).read_text()
        self.assertLess(workflow.index('Bind intrinsic helper'), workflow.index('uses: actions/checkout@'))
        self.assertLess(workflow.index('Install only locked verifier'), workflow.index('Checkout exact caller bytes'))
        self.assertNotIn('secrets: inherit', workflow)
        self.assertNotIn('pull_request_target', workflow)
        self.assertNotIn('cache:', workflow)
        self.assertEqual(workflow.count('persist-credentials: false'), 2)
        self.assertIn('fetch-depth: 0', workflow)
        self.assertIn('filter: ""', workflow)
        self.assertIn('ref: ${{ steps.identity.outputs.definition_sha }}', workflow)
        self.assertIn('env -i PATH=/usr/bin:/bin', workflow)
        self.assertIn('permissions:\n  contents: read', workflow)
        self.assertIn('NPM_CONFIG_USERCONFIG="$config_dir/user.npmrc"', workflow)
        self.assertIn('NPM_CONFIG_GLOBALCONFIG="$config_dir/global.npmrc"', workflow)

    def test_runtime_acceptance_is_separate_after_stage_a_with_no_github_token(self):
        workflow = (ROOT / PATH).read_text()
        self.assertLess(workflow.index('Verify signed history'), workflow.index('Prepare official OS isolation'))
        self.assertLess(workflow.index('Prepare official OS isolation'), workflow.index('Accept current runtime permission bindings'))
        runtime = workflow.split('      - name: Accept current runtime permission bindings', 1)[1]
        self.assertNotIn('GH_TOKEN', runtime)
        self.assertNotIn('GITHUB_TOKEN', runtime)
        self.assertIn('env -i PATH=/usr/bin:/bin', runtime)
        self.assertIn('history-stage-a-receipt.json', workflow)
        self.assertIn('runtime-binding-acceptance.mjs', runtime)
        self.assertIn('sudo -n apt-get install --yes --no-install-recommends bubblewrap', workflow)


if __name__ == '__main__':
    unittest.main()
