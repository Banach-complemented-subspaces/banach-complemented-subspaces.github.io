import { Prose } from '@/components/companion';
import { PublicationLinks } from '@/components/publication-links';
import paper from '@/content/paper.json';
export default function Paper() {
  const p = paper.manuscript;
  return (
    <div className="page">
      <div className="page-title">
        <div className="eyebrow">The paper</div>
        <h1>{p.title}</h1>
        <p>
          {p.authors.join(', ')} · {p.date}
        </p>
      </div>
      <div className="paper-layout">
        <section>
          <h2>Abstract</h2>
          <Prose text={p.abstract_tex} />
          <p className="note" style={{ marginTop: 20 }}>
            The abstract describes further results beyond the five Lean
            theorems presented on this site.
          </p>
        </section>
        <aside className="paper-meta">
          <p>
            <strong>Manuscript</strong>
            {p.pdf_pages} pages
            <br />
            {p.date}
          </p>
          <PublicationLinks />
          <p>
            <strong>Start with</strong>
            <a href="/paper/manuscript.pdf#page=2">
              Theorems A, B & Corollary C · pp. 2–3
            </a>
          </p>
        </aside>
      </div>
      <div className="links">
        <a
          className="link-button primary"
          href="/paper/manuscript.pdf"
          target="_blank"
          rel="noopener"
        >
          View PDF ↗
        </a>
        <a
          className="link-button"
          href="/paper/manuscript.pdf"
          download="The_complemented_subspace_problem.pdf"
        >
          Download PDF
        </a>
        <a className="link-button" href="/">
          Explore the formalised results →
        </a>
      </div>
      <iframe
        className="pdf-viewer"
        src="/paper/manuscript.pdf#view=FitH"
        title={`The paper PDF, ${p.pdf_pages} pages`}
      />
      <p className="note" style={{ marginTop: 15 }}>
        If your browser does not display the embedded PDF, use “View PDF” or
        “Download PDF” above.
      </p>
      <p className="hash">PDF SHA256: {p.sha256}</p>
    </div>
  );
}
