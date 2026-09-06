import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
process.chdir(root);
fs.mkdirSync('qa', { recursive: true });
const runs = [];
/** @type {Array<[string, string[]]>} */
const commands = [
  ['source-and-guide-consistency', ['scripts/check-guides.mjs']],
  [
    'lint',
    [
      'node_modules/oxlint/bin/oxlint',
      'app',
      'components/companion.tsx',
      'components/publication-links.tsx',
      'components/results-content.tsx',
      'scripts',
    ],
  ],
  ['typescript', ['node_modules/typescript/bin/tsc', '--noEmit']],
  ['production-build', ['node_modules/vinext/dist/cli.js', 'build']],
];
for (const [name, args] of commands) {
  const run = spawnSync(process.execPath, args, {
    cwd: root,
    encoding: 'utf8',
    windowsHide: true,
  });
  fs.writeFileSync(`qa/${name}.log`, (run.stdout || '') + (run.stderr || ''));
  runs.push({ name, exitCode: run.status });
  console.log(`${name}: ${run.status === 0 ? 'PASS' : 'FAIL'}`);
  if (run.status !== 0) {
    console.error(run.stdout, run.stderr);
    fs.writeFileSync(
      'qa/build-status.json',
      JSON.stringify({ pass: false, runs }, null, 2),
    );
    process.exit(1);
  }
}
const manifest = JSON.parse(
  fs.readFileSync('dist/server/vinext-prerender.json', 'utf8'),
);
const routes = ['/', '/definitions', '/paper', '/verification'];
const missing = routes.filter(
  (route) =>
    !manifest.routes.some((r) => r.route === route && r.status === 'rendered'),
);
fs.writeFileSync(
  'qa/build-status.json',
  JSON.stringify(
    {
      checkedUtc: new Date().toISOString(),
      pass: missing.length === 0,
      runs,
      routes: manifest.routes,
      missing,
    },
    null,
    2,
  ),
);
if (missing.length)
  throw new Error('Static routes missing: ' + missing.join(', '));
console.log('All four companion pages exported. Open OPEN_WEBSITE.cmd.');
