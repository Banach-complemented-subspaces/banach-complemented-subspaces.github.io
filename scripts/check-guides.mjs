import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import katex from 'katex';
const read = (p) =>
  JSON.parse(fs.readFileSync(p, 'utf8').replace(/^\uFEFF/, ''));
const normalize = (s) => s.replaceAll('\r\n', '\n');
const definitions = read('content/definitions.json');
const evidence = read('content/evidence.json');
const definitionsGuides = read('content/definition-guides.json');
const theoremGuides = read('content/theorem-guides.json');
const checks = [];
const errors = [];
const hash = (p) =>
  crypto.createHash('sha256').update(fs.readFileSync(p)).digest('hex');
for (const d of [...definitions.definitions, ...evidence.statements]) {
  const id = d.id ?? d.symbol;
  const code = normalize(d.source?.snippet ?? d.literal);
  const steps = (d.id ? definitionsGuides : theoremGuides)[id];
  if (!steps?.length) {
    errors.push('Missing guide ' + id);
    continue;
  }
  let cursor = 0,
    remainder = '';
  for (const s of steps) {
    const at = code.indexOf(s.fragment, cursor);
    if (at < 0) {
      errors.push('Fragment mismatch ' + id + ': ' + s.fragment);
      continue;
    }
    remainder += code.slice(cursor, at);
    cursor = at + s.fragment.length;
    for (const field of ['syntax', 'math', 'role']) {
      if (!s[field]?.trim())
        errors.push('Missing explanation ' + id + ':' + field);
      for (const token of s[field].match(/\\\[[\s\S]*?\\\]|\$[^$]+\$/g) ?? []) {
        try {
          katex.renderToString(
            token.startsWith('$') ? token.slice(1, -1) : token.slice(2, -2),
            { throwOnError: true, strict: 'error', trust: false },
          );
        } catch (e) {
          errors.push(id + ': ' + e.message);
        }
      }
    }
  }
  remainder += code.slice(cursor);
  // Comments and grouping punctuation may surround semantic clause anchors.
  const uncovered = remainder
    .replace(/\/-[\s\S]*?-\//g, '')
    .replace(/--[^\n]*/g, '')
    .replace(/[\s()]/g, '');
  if (uncovered) errors.push('Uncovered source in ' + id + ': ' + uncovered);
  const source = normalize(
    fs.readFileSync(
      (d.source?.absoluteFile ?? d.source_absolute_path).replace(
        /^LEAN_PROJECT[\\/]/,
        'lean/',
      ),
      'utf8',
    ),
  );
  if (!source.includes(code)) errors.push('Not in frozen source: ' + id);
  checks.push({
    id,
    clauses: steps.length,
    exactSourceMatch: source.includes(code),
    uncovered,
  });
}
const preservation = read('public/evidence-public/companion-source-recheck.json').comparison;
const project = path.resolve('lean');
for (const f of preservation.files) {
  if (hash(path.join(project, f.path)) !== f.after_sha256)
    errors.push('Original source changed: ' + f.path);
}
const assets = read('public/asset-manifest.json');
for (const a of assets) {
  if (hash('public' + a.url) !== a.sha256)
    errors.push('Preserved artifact changed: ' + a.url);
}
const publicCopies = read('public/evidence-public/PUBLIC_COPY_SHA256.json');
for (const f of publicCopies) {
  if (hash(path.join('public', f.public_path)) !== f.public_sha256)
    errors.push('Public evidence copy changed: ' + f.public_path);
}
const result = {
  checkedUtc: new Date().toISOString(),
  pass: !errors.length,
  definitions: definitions.definitions.length,
  statements: evidence.statements.length,
  clauses: checks.reduce((n, c) => n + c.clauses, 0),
  originalSourcesChecked: preservation.files.length,
  preservedArtifactsChecked: assets.length,
  checks,
  errors,
};
fs.writeFileSync(
  'qa/consolidated-source-check.json',
  JSON.stringify(result, null, 2),
);
console.log(JSON.stringify(result));
if (errors.length) process.exitCode = 1;
