'use client';
import { useState } from 'react';
import { Definition, Math, SourceLink, Lean } from '@/components/companion';
import definitions from '@/content/definitions.json';
export default function Definitions() {
  const [query, setQuery] = useState('');
  const selected = definitions.definitions.filter((d) =>
    (d.name + ' ' + d.explanation).toLowerCase().includes(query.toLowerCase()),
  );
  return (
    <div className="page">
      <div className="page-title">
        <div className="eyebrow">The mathematical vocabulary</div>
        <h1>Definitions, made explicit</h1>
        <p className="intro">
          The project’s definitions are shown with their exact source,
          mathematical meaning, and context. Standard Mathlib notions are
          identified separately below.
        </p>
      </div>
      <div className="two-column">
        <aside className="index" aria-label="Definition index">
          <div className="eyebrow">Project definitions</div>
          {definitions.definitions.map((d) => (
            <a key={d.id} href={'#' + d.id} onClick={() => setQuery('')}>
              {d.name}
            </a>
          ))}
          <a href="#mathlib" onClick={() => setQuery('')}>
            Standard Mathlib notions ↓
          </a>
        </aside>
        <div>
          <label htmlFor="definition-search">Find a definition</label>
          <input
            className="search"
            id="definition-search"
            type="search"
            placeholder="Name or mathematical term…"
            value={query}
            onChange={(e) => setQuery(e.target.value)}
          />
          <p className="note" aria-live="polite">
            {selected.length} of {definitions.definitions.length} project
            definitions
          </p>
          {selected.length ? (
            selected.map((d) => <Definition id={d.id} key={d.id} />)
          ) : (
            <p className="empty">
              No matching definition. Try “basis”, “range”, or “lattice”.
            </p>
          )}
          <section id="mathlib" className="definition">
            <div className="eyebrow">Standard library</div>
            <h2>Definitions from Mathlib</h2>
            <p>
              These are established library notions used by the project. The
              local source excerpts record the pinned revision; online
              documentation may describe a newer revision.
            </p>
            {definitions.standardMathlib.map((d) => (
              <article key={d.id} id={d.id} className="definition standard">
                <div className="eyebrow">Standard Mathlib notion</div>
                <h3>
                  <code>{d.name}</code>
                </h3>
                <Math tex={d.mathTex} display />
                <p>{d.explanation}</p>
                <Lean
                  code={d.source.snippet}
                  label="Pinned Mathlib source excerpt"
                />
                <div className="links">
                  <SourceLink file={d.source.file} line={d.source.startLine}>
                    Pinned source
                  </SourceLink>
                  {d.documentationUrl && (
                    <a
                      href={d.documentationUrl}
                      target="_blank"
                      rel="noopener noreferrer"
                      referrerPolicy="no-referrer"
                    >
                      Mathlib documentation ↗
                    </a>
                  )}
                </div>
              </article>
            ))}
          </section>
        </div>
      </div>
    </div>
  );
}
