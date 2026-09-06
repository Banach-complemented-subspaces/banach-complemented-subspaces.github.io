'use client';
import { useEffect, useRef, useState } from 'react';
import { usePathname } from 'next/navigation';
import katex from 'katex';
import { Button } from '@/components/ui/button';
import {
  Accordion,
  AccordionContent,
  AccordionItem,
  AccordionTrigger,
} from '@/components/ui/accordion';
import definitions from '@/content/definitions.json';
import definitionGuides from '@/content/definition-guides.json';
import evidence from '@/content/evidence.json';
import theoremGuides from '@/content/theorem-guides.json';
export function Navigation() {
  const path = usePathname();
  return (
    <nav aria-label="Main navigation">
      {[
        ['/', 'Results'],
        ['/definitions/', 'Definitions'],
        ['/paper/', 'Paper'],
        ['/verification/', 'Verification'],
      ].map(([href, label]) => (
        <a
          key={href}
          href={href}
          aria-current={
            path?.replace(/\/$/, '') === href.replace(/\/$/, '')
              ? 'page'
              : undefined
          }
        >
          {label}
        </a>
      ))}
    </nav>
  );
}
export function Math({
  tex,
  display = false,
}: {
  tex: string;
  display?: boolean;
}) {
  return (
    <span
      className={display ? 'math-display' : 'math-inline'}
      dangerouslySetInnerHTML={{
        __html: katex.renderToString(tex, {
          displayMode: display,
          throwOnError: true,
          trust: false,
          output: 'htmlAndMathml',
          strict: 'error',
        }),
      }}
    />
  );
}
export function Prose({ text }: { text: string }) {
  return (
    <div className="math-prose">
      {text
        .split(/(\\\[[\s\S]*?\\\]|\$[^$]+\$)/g)
        .map((s, i) =>
          s.startsWith('\\[') ? (
            <Math key={i} tex={s.slice(2, -2)} display />
          ) : s.startsWith('$') ? (
            <Math key={i} tex={s.slice(1, -1)} />
          ) : (
            <span key={i}>{s}</span>
          ),
        )}
    </div>
  );
}
const names = new Map(
  [...definitions.definitions, ...definitions.standardMathlib].map((d) => [
    d.name,
    d.id,
  ]),
);
function Tokens({ text }: { text: string }) {
  return (
    <>
      {text
        .replaceAll('\r\n', '\n')
        .split(/(\b[A-Za-z_][A-Za-z_0-9.]*\b|--[^\n]*)/g)
        .map((t, i) =>
          names.has(t) ? (
            <a
              key={i}
              href={'/definitions/#' + names.get(t)}
              title={'Read the definition of ' + t}
            >
              {t}
            </a>
          ) : (
            <span
              key={i}
              className={
                /^(def|theorem|structure|where|letI|Prop|Type|by|instance|variable|namespace|noncomputable|section|open|scoped|abbrev)$/.test(
                  t,
                )
                  ? 'keyword'
                  : t.startsWith('--')
                    ? 'comment'
                    : undefined
              }
            >
              {t}
            </span>
          ),
        )}
    </>
  );
}
export function Lean({
  code,
  label = 'Exact Lean source excerpt',
}: {
  code: string;
  label?: string;
}) {
  const [copied, setCopied] = useState('Copy');
  return (
    <div className="lean-wrap">
      <div className="code-toolbar">
        <span>{label}</span>
        <Button
          variant="ghost"
          onClick={async () => {
            try {
              await navigator.clipboard.writeText(code);
              setCopied('Copied');
            } catch {
              setCopied('Select code to copy');
            }
            setTimeout(() => setCopied('Copy'), 2200);
          }}
        >
          {copied}
        </Button>
      </div>
      <section className="code-scroll" tabIndex={0} aria-label={label}>
        <pre>
          <code>
            <Tokens text={code} />
          </code>
        </pre>
      </section>
    </div>
  );
}
export function SourceLink({
  file,
  line,
  children = 'View source',
}: {
  file: string;
  line?: number;
  children?: React.ReactNode;
}) {
  return (
    <a href={'/evidence-public/source/' + file + '.html' + (line ? '#L' + line : '')}>
      {children}
    </a>
  );
}
export function Definition({
  id,
  compact = false,
}: {
  id: string;
  compact?: boolean;
}) {
  const d = definitions.definitions.find((d) => d.id === id);
  if (!d) return null;
  return (
    <article
      className={compact ? 'definition compact' : 'definition'}
      id={compact ? undefined : d.id}
    >
      <div className="eyebrow">Project-defined</div>
      <h3>
        <code>{d.name}</code>
      </h3>
      <Math tex={d.mathTex} display />
      <p>{d.explanation}</p>
      {d.notes.map((n, i) => (
        <p key={i} className="note">
          {n}
        </p>
      ))}
      <Lean code={d.source.snippet} />
      <p className="source-line">
        <SourceLink file={d.source.file} line={d.source.startLine} />
        <span>
          {d.source.file.split('/').pop()} · lines {d.source.startLine}–
          {d.source.endLine}
        </span>
      </p>
      <GuideDisclosure
        guideId={'definition-' + d.id}
        code={d.source.snippet}
        steps={(definitionGuides as Record<string, ReadingStep[]>)[d.id] ?? []}
        label="Explain this Lean definition"
        depth={compact ? 1 : 0}
      />
      {!compact && (
        <Accordion className="quiet-disclosure">
          <AccordionItem value="context">
            <AccordionTrigger>
              Surrounding assumptions and notation
            </AccordionTrigger>
            <AccordionContent>
              <p>
                These excerpts show the assumptions and notation used in the
                definition. They should be read with the surrounding declarations
                and imports in the full source.
              </p>
              {d.sourceContext.map((s, i) => (
                <Lean key={i} code={s.snippet} />
              ))}
            </AccordionContent>
          </AccordionItem>
        </Accordion>
      )}
      {!compact && d.dependsOn.length > 0 && (
        <p className="related">
          Related:{' '}
          {d.dependsOn.map((n) => (
            <a key={n} href={'/definitions/#' + (names.get(n) ?? n)}>
              {n}
            </a>
          ))}
        </p>
      )}
    </article>
  );
}

export type ReadingStep = {
  fragment: string;
  syntax: string;
  math: string;
  role: string;
  terms?: string[];
};

const notation: Record<string, string> = {
  UnconditionalCorollaryStatement:
    'The basis proposition shared by the real and complex theorems. Substituting ℂ fixes every scalar, linear map and continuous dual to the complex field.',
  'ContinuousLinearMap.id':
    'ContinuousLinearMap.id 𝕜 X is the identity bounded 𝕜-linear operator on X. Subtracting P gives I_X − P on the same space.',
  'P.range':
    'P.range is the linear subspace {P x | x ∈ X}, with the norm inherited from X. Its continuous dual consists of bounded linear maps from this range to the scalar field.',
  'X.Carrier':
    'X.Carrier denotes the underlying vector space of the chosen Banach space X. All later conditions refer to this same space and its complete norm.',
  NontriviallyNormedField:
    'The bracketed field assumption specifies scalar arithmetic and a nontrivial norm. The verified real and complex theorems use ℝ and ℂ; defining a proposition for a general field does not prove it for every field.',
  WithLp:
    'Mathlib’s WithLp equips finite product coordinates with the indicated ℓᵖ norm. Block uses it on Fin (a.N j) → ℝ.',
  lp: 'Mathlib’s lp is the normed space of families with finite ℓᵖ norm. Here the outer exponent is 2, so membership requires square-summability of the block norms.',
  Antitone:
    'Antitone means nonincreasing: if i ≤ j, then p j ≤ p i. Equality between successive terms is permitted.',
  'Filter.Tendsto':
    'Tendsto expresses convergence between filters. Along atTop on ℕ, tending to 𝓝 2 means the exponents approach 2 as the block index tends to infinity.',
  'ENNReal.ofReal':
    'ENNReal.ofReal embeds a nonnegative real value in the extended nonnegative reals. These values also have a largest element ⊤, interpreted as infinity.',
};

function termInfo(term: string) {
  const project = definitions.definitions.find(
    (d) => d.name === term || d.id === term,
  );
  const library = definitions.standardMathlib.find(
    (d) => d.name === term || d.id === term,
  );
  const statement = evidence.statements.find((s) => s.symbol === term);
  return { project, library, statement, notation: notation[term] };
}

function FragmentTerms({
  text,
  extra = [],
  onSelect,
}: {
  text: string;
  extra?: string[];
  onSelect: (term: string) => void;
}) {
  const terms = [
    ...new Set([...names.keys(), ...Object.keys(notation), ...extra]),
  ]
    .filter((t) => text.includes(t) && Object.values(termInfo(t)).some(Boolean))
    .sort((a, b) => b.length - a.length);
  const pieces: React.ReactNode[] = [];
  let pos = 0;
  while (pos < text.length) {
    const hits = terms
      .map((term) => ({ term, at: text.indexOf(term, pos) }))
      .filter((h) => h.at >= 0)
      .sort((a, b) => a.at - b.at || b.term.length - a.term.length);
    const hit = hits[0];
    if (!hit) {
      pieces.push(text.slice(pos));
      break;
    }
    pieces.push(text.slice(pos, hit.at));
    pieces.push(
      <button
        type="button"
        className="code-term"
        key={hit.at}
        aria-label={'Explain ' + hit.term}
        onClick={() => onSelect(hit.term)}
      >
        {hit.term}
      </button>,
    );
    pos = hit.at + hit.term.length;
  }
  return <>{pieces}</>;
}

export function GuideDisclosure({
  guideId,
  code,
  steps,
  label = 'Read the Lean statement step by step',
  depth = 0,
  children,
}: {
  guideId: string;
  code: string;
  steps: ReadingStep[];
  label?: string;
  depth?: number;
  children?: React.ReactNode;
}) {
  return (
    <Accordion className="quiet-disclosure" data-guide={guideId}>
      <AccordionItem value="explanation">
        <AccordionTrigger>{label}</AccordionTrigger>
        <AccordionContent>
          <CodeReading code={code} steps={steps} depth={depth} />
          {children}
        </AccordionContent>
      </AccordionItem>
    </Accordion>
  );
}

function CodeReading({
  code,
  steps,
  depth,
}: {
  code: string;
  steps: ReadingStep[];
  depth: number;
}) {
  const [current, setCurrent] = useState(0);
  const [term, setTerm] = useState<string | null>(null);
  const contextRef = useRef<HTMLElement>(null);
  const fragmentRef = useRef<HTMLPreElement>(null);
  useEffect(() => {
    const box = contextRef.current;
    const selected = box?.querySelector<HTMLElement>('[aria-pressed="true"]');
    if (!box || !selected) return;
    const y =
      selected.getBoundingClientRect().top - box.getBoundingClientRect().top;
    if (y < 0 || y + selected.offsetHeight > box.clientHeight)
      box.scrollTop += y - 24;
  }, [current]);
  const choose = (index: number) => {
    setCurrent(index);
    setTerm(null);
  };
  const chunks: React.ReactNode[] = [];
  let cursor = 0;
  steps.forEach((s, i) => {
    const at = code.indexOf(s.fragment, cursor);
    if (at < 0)
      throw new Error(
        'Guide fragment missing from exact source: ' + s.fragment,
      );
    chunks.push(code.slice(cursor, at));
    chunks.push(
      <button
        type="button"
        key={i}
        data-clause={i}
        className={
          'selectable-clause' + (current === i ? ' selected-clause' : '')
        }
        aria-label={'Read clause ' + (i + 1) + ': ' + s.fragment}
        aria-pressed={current === i}
        onClick={() => {
          if (!window.getSelection()?.toString()) choose(i);
        }}
        onKeyDown={(e) => {
          if (e.key === 'Enter' || e.key === ' ') {
            e.preventDefault();
            choose(i);
          }
          if (e.key === 'ArrowDown' || e.key === 'ArrowUp') {
            e.preventDefault();
            const next = globalThis.Math.max(
              0,
              globalThis.Math.min(
                steps.length - 1,
                i + (e.key === 'ArrowDown' ? 1 : -1),
              ),
            );
            choose(next);
            contextRef.current
              ?.querySelector<HTMLElement>('[data-clause="' + next + '"]')
              ?.focus({ preventScroll: true });
          }
        }}
      >
        {s.fragment}
      </button>,
    );
    cursor = at + s.fragment.length;
  });
  chunks.push(code.slice(cursor));
  const selected = steps[current];
  if (!selected) return null;
  const info = term ? termInfo(term) : null;
  return (
    <div className="code-reading">
      <p className="guide-hint">
        Select a clause in the code, or use Previous and Next. Underlined terms
        in the selected fragment open their definitions.
      </p>
      <div className="guide-layout">
        <section
          className="guide-code"
          ref={contextRef}
          tabIndex={0}
          aria-label="Complete declaration with selectable clauses"
        >
          <pre>
            <code>{chunks}</code>
          </pre>
        </section>
        <div className="guide-detail">
          <div className="guide-controls">
            <Button
              variant="ghost"
              disabled={current === 0}
              onClick={() => choose(current - 1)}
            >
              ← Previous
            </Button>
            <span className="guide-progress" aria-live="polite">
              {current + 1} / {steps.length}
            </span>
            <Button
              variant="ghost"
              disabled={current === steps.length - 1}
              onClick={() => choose(current + 1)}
            >
              Next →
            </Button>
          </div>
          <div className="selected-fragment-label">Selected Lean fragment</div>
          <pre className="selected-fragment" tabIndex={-1} ref={fragmentRef}>
            <code>
              <FragmentTerms
                text={selected.fragment}
                extra={selected.terms}
                onSelect={setTerm}
              />
            </code>
          </pre>
          <dl className="clause-explanation">
            <dt>How to read it</dt>
            <dd>
              <Prose text={selected.syntax} />
            </dd>
            <dt>In mathematics</dt>
            <dd>
              <Prose text={selected.math} />
            </dd>
            <dt>Place in the statement</dt>
            <dd>
              <Prose text={selected.role} />
            </dd>
          </dl>
          {term && info && (
            <section
              className="local-definition"
              aria-label={'Definition of ' + term}
            >
              <Button
                variant="ghost"
                className="return-to-clause"
                onClick={() => {
                  setTerm(null);
                  fragmentRef.current?.focus({ preventScroll: true });
                }}
              >
                ← Return to selected clause
              </Button>
              {info.project && depth === 0 ? (
                <Definition compact id={info.project.id} />
              ) : (
                <>
                  <div className="eyebrow">
                    {info.project || info.statement
                      ? 'Project-defined'
                      : info.library || term === 'ContinuousLinearMap.id'
                        ? 'Imported from Mathlib'
                        : 'Lean notation'}
                  </div>
                  <h4>
                    <code>{term}</code>
                  </h4>
                  <p>
                    {info.project?.explanation ??
                      info.library?.explanation ??
                      info.notation}
                  </p>
                  {(info.project || info.library) && (
                    <>
                      <Lean
                        code={(info.project ?? info.library)!.source.snippet}
                      />
                      <SourceLink
                        file={(info.project ?? info.library)!.source.file}
                        line={(info.project ?? info.library)!.source.startLine}
                      >
                        Pinned definition source
                      </SourceLink>
                    </>
                  )}
                  {info.statement && (
                    <>
                      <Lean
                        code={info.statement.literal}
                        label="Complete proposition definition"
                      />
                      <SourceLink
                        file={info.statement.source_path}
                        line={info.statement.line_start}
                      >
                        Statement source
                      </SourceLink>
                      {depth === 0 && (
                        <GuideDisclosure
                          guideId={'local-' + info.statement.symbol}
                          code={info.statement.literal}
                          steps={
                            (theoremGuides as Record<string, ReadingStep[]>)[
                              info.statement.symbol
                            ]
                          }
                          depth={1}
                        />
                      )}
                    </>
                  )}
                </>
              )}
            </section>
          )}
        </div>
      </div>
    </div>
  );
}
