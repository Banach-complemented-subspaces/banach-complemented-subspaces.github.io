import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
const root = path.resolve(
  path.dirname(fileURLToPath(import.meta.url)),
  '../dist/client',
);
const port = Number(process.env.COMPANION_PORT || 4173);
const mime = {
  '.html': 'text/html; charset=utf-8',
  '.js': 'text/javascript; charset=utf-8',
  '.css': 'text/css; charset=utf-8',
  '.json': 'application/json; charset=utf-8',
  '.txt': 'text/plain; charset=utf-8',
  '.log': 'text/plain; charset=utf-8',
  '.md': 'text/plain; charset=utf-8',
  '.lean': 'text/plain; charset=utf-8',
  '.toml': 'text/plain; charset=utf-8',
  '.pdf': 'application/pdf',
  '.zip': 'application/zip',
  '.woff': 'font/woff',
  '.woff2': 'font/woff2',
  '.ttf': 'font/ttf',
  '.svg': 'image/svg+xml',
  '.jpg': 'image/jpeg',
  '.png': 'image/png',
  '.ico': 'image/x-icon',
  '.rsc': 'text/x-component',
};
http
  .createServer((req, res) => {
    res.setHeader('X-Robots-Tag', 'noindex, nofollow');
    res.setHeader('Referrer-Policy', 'no-referrer');
    res.setHeader('X-Content-Type-Options', 'nosniff');
    res.setHeader(
      'Content-Security-Policy',
      "default-src 'self'; script-src 'self' 'unsafe-inline'; style-src 'self' 'unsafe-inline'; font-src 'self' data:; img-src 'self' data:; connect-src 'self'; frame-src 'self'; object-src 'self'; base-uri 'self'",
    );
    if (!['GET', 'HEAD'].includes(req.method)) {
      res.writeHead(405).end();
      return;
    }
    let pathname;
    try {
      pathname = decodeURIComponent(
        new URL(req.url, 'http://127.0.0.1').pathname,
      );
    } catch {
      res.writeHead(400).end();
      return;
    }
    if (pathname === '/__companion/status') {
      res.setHeader('Content-Type', 'application/json');
      res.end(
        JSON.stringify({
          application: 'complemented-subspace-local-companion',
          localOnly: true,
        }),
      );
      return;
    }
    if (pathname === '/results' || pathname === '/results/') {
      res.writeHead(308, { Location: '/' }).end();
      return;
    }
    const candidate = path.resolve(root, '.' + pathname);
    if (candidate !== root && !candidate.startsWith(root + path.sep)) {
      res.writeHead(403).end();
      return;
    }
    const base = candidate.replace(/[\\/]$/, '');
    const file = [
      candidate,
      path.join(candidate, 'index.html'),
      base + '.html',
    ].find((p) => fs.existsSync(p) && fs.statSync(p).isFile());
    if (!file) {
      res
        .writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8' })
        .end('Local file not found.');
      return;
    }
    const size = fs.statSync(file).size;
    res.setHeader(
      'Content-Type',
      mime[path.extname(file)] || 'text/plain; charset=utf-8',
    );
    res.setHeader('Accept-Ranges', 'bytes');
    const range = /^bytes=(\d+)-(\d*)$/.exec(req.headers.range || '');
    if (range) {
      const start = Number(range[1]),
        end = Math.min(range[2] ? Number(range[2]) : size - 1, size - 1);
      if (start >= size || start > end) {
        res.writeHead(416, { 'Content-Range': `bytes */${size}` }).end();
        return;
      }
      res.writeHead(206, {
        'Content-Range': `bytes ${start}-${end}/${size}`,
        'Content-Length': end - start + 1,
      });
      if (req.method === 'HEAD') res.end();
      else fs.createReadStream(file, { start, end }).pipe(res);
      return;
    }
    res.setHeader('Content-Length', size);
    if (req.method === 'HEAD') res.end();
    else fs.createReadStream(file).pipe(res);
  })
  .listen(port, '127.0.0.1', () =>
    console.log(`Local companion: http://127.0.0.1:${port}/`),
  );
