import { spawn, execFile } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
const site = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const url = 'http://127.0.0.1:4173/';
async function running() {
  try {
    return (
      (
        await (
          await fetch(url + '__companion/status', {
            signal: AbortSignal.timeout(1000),
          })
        ).json()
      ).application === 'complemented-subspace-local-companion'
    );
  } catch {
    return false;
  }
}
if (!(await running())) {
  fs.mkdirSync(path.join(site, 'qa'), { recursive: true });
  const log = fs.openSync(path.join(site, 'qa/local-server.log'), 'a');
  const child = spawn(
    process.execPath,
    [path.join(site, 'scripts/serve.mjs')],
    {
      cwd: site,
      detached: true,
      windowsHide: true,
      stdio: ['ignore', log, log],
    },
  );
  child.unref();
  fs.closeSync(log);
  for (let i = 0; i < 30 && !(await running()); i++)
    await new Promise((r) => setTimeout(r, 200));
}
if (!(await running()))
  throw new Error(
    'Could not start the local companion. See qa/local-server.log; port 4173 may be in use.',
  );
if (process.platform === 'win32' && !process.argv.includes('--no-browser'))
  execFile('explorer.exe', [url]);
else console.log(url);
