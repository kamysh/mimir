"""Exercise release admission with private Git histories and no network calls."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


GUARD = Path(__file__).resolve().parents[1] / 'scripts/check-release-source.sh'
LOGS = Path(tempfile.mkdtemp(prefix='mimir-release-source-logs-'))


class ReleaseSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        print(f'Release source command logs: {LOGS}', flush=True)

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='mimir-release-source-')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.repo = self.root / 'checkout'
        self.repo.mkdir()
        self.origin = self.root / 'origin.git'
        self.logs = LOGS / self._testMethodName
        self.logs.mkdir()
        self.counter = 0
        self.env = {key: value for key, value in os.environ.items() if not key.startswith('GIT_')}
        self.env.update(GIT_CONFIG_NOSYSTEM='1', GIT_CONFIG_GLOBAL=os.devnull,
                        GIT_AUTHOR_NAME='Release fixture', GIT_AUTHOR_EMAIL='release@example.invalid',
                        GIT_COMMITTER_NAME='Release fixture', GIT_COMMITTER_EMAIL='release@example.invalid',
                        GIT_TERMINAL_PROMPT='0')
        self.git('init', '--bare', '--initial-branch=main', str(self.origin))
        self.git('init', '--initial-branch=main')
        self.git('remote', 'add', 'origin', str(self.origin))
        self.initial = self.commit('initial')
        self.git('push', 'origin', 'main')

    def run_logged(self, args, env):
        self.counter += 1
        stem = self.logs / f'{self.counter:03}'
        result = subprocess.run(args, cwd=self.repo, env=env, text=True, capture_output=True)
        stem.with_suffix('.command.json').write_text(json.dumps(args) + '\n')
        stem.with_suffix('.stdout').write_text(result.stdout)
        stem.with_suffix('.stderr').write_text(result.stderr)
        stem.with_suffix('.exit').write_text(str(result.returncode) + '\n')
        return result

    def git(self, *args):
        result = self.run_logged(['git', *args], self.env)
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout.strip()

    def commit(self, text):
        (self.repo / 'source.txt').write_text(text)
        self.git('add', 'source.txt')
        self.git('commit', '-m', text)
        return self.git('rev-parse', 'HEAD')

    def feature(self):
        self.git('checkout', '-b', 'feature')
        return self.commit('unmerged change')

    def guard(self, event, ref, sha=None):
        output = self.root / 'outputs'
        output.write_text('')
        env = dict(self.env, GITHUB_EVENT_NAME=event, GITHUB_REF=ref,
                   GITHUB_SHA=sha or self.git('rev-parse', 'HEAD'), GITHUB_OUTPUT=str(output))
        result = self.run_logged(['bash', str(GUARD)], env)
        return result, dict(line.split('=', 1) for line in output.read_text().splitlines())

    def test_main_tag_builds_the_exact_commit_and_can_publish(self):
        self.git('tag', 'v-test')
        result, output = self.guard('push', 'refs/tags/v-test')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output, dict(commit=self.initial, publish='true'))

    def test_annotated_tag_resolves_to_its_commit(self):
        self.git('tag', '-a', 'v-test', '-m', 'release fixture')
        tag_object = self.git('rev-parse', 'v-test')
        result, output = self.guard('push', 'refs/tags/v-test', tag_object)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output, dict(commit=self.initial, publish='true'))

    def test_main_can_advance_before_the_tag_check(self):
        self.commit('later main change')
        self.git('push', 'origin', 'main')
        self.git('checkout', '--detach', self.initial)
        result, output = self.guard('push', 'refs/tags/v-test')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output['commit'], self.initial)

    def test_unmerged_branch_tag_is_refused_before_build_outputs(self):
        self.feature()
        self.git('tag', 'v-unmerged')
        result, output = self.guard('push', 'refs/tags/v-unmerged')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('has not been included in main', result.stderr)
        self.assertEqual(output, {})

    def test_manual_feature_branch_build_remains_available_without_publication(self):
        selected = self.feature()
        result, output = self.guard('workflow_dispatch', 'refs/heads/feature')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output, dict(commit=selected, publish='false'))

    def test_manual_main_tag_can_publish(self):
        result, output = self.guard('workflow_dispatch', 'refs/tags/v-test')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output['publish'], 'true')

    def test_manual_tag_cannot_publish_unmerged_code(self):
        self.feature()
        result, output = self.guard('workflow_dispatch', 'refs/tags/v-unmerged')
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(output, {})

    def test_branch_push_does_not_start_release_builds(self):
        result, output = self.guard('push', 'refs/heads/main')
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(output, {})

    def test_nonversion_tag_is_refused(self):
        result, output = self.guard('push', 'refs/tags/snapshot')
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(output, {})

    def test_wrong_checkout_is_refused(self):
        self.feature()
        result, output = self.guard('push', 'refs/tags/v-test', self.initial)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('checked-out source differs', result.stderr)
        self.assertEqual(output, {})

    def test_missing_main_is_refused(self):
        self.git('--git-dir=' + str(self.origin), 'update-ref', '-d', 'refs/heads/main')
        result, output = self.guard('push', 'refs/tags/v-test')
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(output, {})


if __name__ == '__main__':
    print(f'Release source command logs: {LOGS}', flush=True)
    unittest.main()
