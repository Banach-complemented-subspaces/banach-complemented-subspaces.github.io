"""Small offline renderer for the controlled Markdown audit report format."""
import html
import re

def inline(text):
    text=html.escape(text)
    text=re.sub(r'`([^`]+)`',r'<code>\1</code>',text)
    text=re.sub(r'\*\*([^*]+)\*\*',r'<strong>\1</strong>',text)
    return re.sub(r'\[([^\]]+)\]\(([^\s)]+)\)',r'<a href="\2">\1</a>',text)

def render(markdown):
    output=[]; code=[]; paragraph=[]; table=[]; listing=[]; in_code=False
    def flush():
        if paragraph:
            output.append('<p>'+inline(' '.join(paragraph))+'</p>'); paragraph.clear()
        if table:
            rows=[]
            for i,row in enumerate(table):
                if all(re.fullmatch(r':?-{3,}:?',cell.strip()) for cell in row):
                    continue
                tag='th' if i==0 else 'td'
                rows.append('<tr>'+''.join('<'+tag+'>'+inline(cell.strip())+'</'+tag+'>' for cell in row)+'</tr>')
            output.append('<div class="table-scroll"><table>'+''.join(rows)+'</table></div>'); table.clear()
        if listing:
            output.append('<ul>'+''.join('<li>'+inline(item)+'</li>' for item in listing)+'</ul>'); listing.clear()
    for line in markdown.splitlines():
        if line.startswith('```'):
            if in_code:
                output.append('<pre><code>'+html.escape('\n'.join(code))+'</code></pre>'); code.clear()
            else:
                flush()
            in_code=not in_code
        elif in_code:
            code.append(line)
        elif line.startswith('#'):
            flush(); level=min(len(line)-len(line.lstrip('#')),6)
            output.append(f'<h{level}>'+inline(line[level:].strip())+f'</h{level}>')
        elif line.startswith('|') and line.endswith('|'):
            if paragraph or listing: flush()
            table.append(line[1:-1].split('|'))
        elif line.startswith('- '):
            if paragraph or table: flush()
            listing.append(line[2:])
        elif not line.strip():
            flush()
        else:
            if table or listing: flush()
            paragraph.append(line)
    flush()
    if in_code: raise ValueError('Unclosed report code fence')
    return '''<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Extended fresh Lean audit — 6 September 2026</title>
<style>body{margin:0;color:#222;background:#fff;font:17px/1.65 Georgia,serif}main{max-width:1040px;margin:auto;padding:40px 24px 80px}nav{font:15px/1.6 system-ui,sans-serif;margin-bottom:32px}a{color:#154e80;text-underline-offset:3px}h1{font-size:2rem;line-height:1.2}h2{font-size:1.35rem;margin-top:2.2rem}h3{font-size:1.1rem}p,li{overflow-wrap:anywhere}code,pre{font:14px/1.6 ui-monospace,Consolas,monospace}code{overflow-wrap:anywhere}pre{padding:16px;background:#f4f6f7;overflow:auto;border:1px solid #dce1e4}table{border-collapse:collapse;min-width:540px;width:100%;font:15px/1.6 system-ui,sans-serif}th,td{text-align:left;vertical-align:top;border-bottom:1px solid #dce1e4;padding:10px 12px;overflow-wrap:anywhere}.table-scroll{overflow:auto;margin:20px 0}th{background:#f4f6f7}nav a{display:inline-block;margin-right:20px}li{margin:8px 0}@media(max-width:600px){main{padding:24px 18px 60px}h1{font-size:1.7rem}}</style></head><body><main>
<nav><a href="/verification/#extended-fresh-audit">← Verification</a><a href="report.md" download>Download report</a><a href="../full-fresh-audit-evidence.zip" download>Download evidence</a></nav>
'''+ '\n'.join(output) + '</main></body></html>\n'
