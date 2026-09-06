import {
  GuideDisclosure,
  Lean,
  Prose,
  SourceLink,
  type ReadingStep,
} from '@/components/companion';
import evidence from '@/content/evidence.json';
import paper from '@/content/paper.json';
import guides from '@/content/theorem-guides.json';

function Statement({ symbol }: { symbol: string }) {
  const s = evidence.statements.find((s) => s.symbol === symbol)!;
  return (
    <div data-statement={symbol}>
      <Lean
        code={s.literal}
        label="Exact proposition definition · complete body"
      />
      <p className="source-line">
        <SourceLink file={s.source_path} line={s.line_start}>
          Statement source
        </SourceLink>
      </p>
    </div>
  );
}
function Proof({ symbol }: { symbol: string }) {
  const e = evidence.endpoints.find((e) => e.symbol === symbol)!;
  return (
    <div id={symbol} className="proved-reference">
      <Lean
        code={e.literal_signature}
        label="Proved declaration · proof body omitted"
      />
      <p className="verification-line">
        Verified in Lean ·{' '}
        <SourceLink file={e.source_path} line={e.line_start}>
          Source
        </SourceLink>{' '}
        · <a href="/verification/">Verification details</a>
      </p>
    </div>
  );
}
function Guide({
  symbol,
  children,
}: {
  symbol: string;
  children?: React.ReactNode;
}) {
  const s = evidence.statements.find((s) => s.symbol === symbol)!;
  return (
    <GuideDisclosure
      guideId={symbol}
      code={s.literal}
      steps={(guides as Record<string, ReadingStep[]>)[symbol] ?? []}
    >
      {children}
    </GuideDisclosure>
  );
}
export function ResultsContent() {
  const a = paper.results.find((r) => r.id === 'theorem-a')!;
  const b = paper.results.find((r) => r.id === 'theorem-b')!;
  const c = paper.results.find((r) => r.id === 'corollary-c')!;
  return (
    <>
      <section className="result" id="theorem-a">
        <h2>Theorem A</h2>
        <div className="result-grid">
          <div className="result-mathematics">
            <div className="panel-label">
              Mathematical statement · real field
            </div>
            <Prose text={a.statement_tex} />
            <p className="note correspondence-note">
              The Lean statement requires uniform convexity of the displayed norm,
              which implies superreflexivity. The manuscript also establishes
              uniform convexity in Corollary 4.2(ii). The exponents are
              nonincreasing, and Lean starts the block index at 0.
            </p>
          </div>
          <div>
            <Statement symbol="RealMainTheoremStatement" />
            <Proof symbol="realMainTheorem" />
            <p className="note">
              The definition states the result; <code>realMainTheorem</code>{' '}
              proves it.
            </p>
          </div>
        </div>
        <Guide symbol="RealMainTheoremStatement">
          <p className="assembled-reading">
            Taken together: for every positive tolerance, choose one block space
            and one projection. That space has all three geometric properties,
            both complementary projection norms satisfy the strict bounds, and
            both ranges and both continuous duals satisfy the GL/DPR
            conclusions.
          </p>
        </Guide>
      </section>
      <section className="result" id="theorem-b">
        <h2>Theorem B</h2>
        <div className="result-grid">
          <div className="result-mathematics">
            <div className="panel-label">
              Mathematical statement · real and complex fields
            </div>
            <Prose text={b.statement_tex} />
            <p className="note correspondence-note">
              The real declaration on the right includes the two nonisomorphism
              conclusions. The common basis conclusion and its complex
              specialisation follow below.
            </p>
          </div>
          <div>
            <h3 className="scalar-heading">Real case</h3>
            <Statement symbol="RealCorollaryStatement" />
            <Proof symbol="realCorollary" />
          </div>
        </div>
        <Guide symbol="RealCorollaryStatement" />
        <div className="result-grid scalar-pair">
          <div className="result-mathematics">
            <h3>Basis conclusion over each field</h3>
            <Prose
              text={
                'This proposition states the unconditional-basis part of Theorem B. The theorem $\\mathtt{realUnconditionalCorollary}$ proves it for $\\mathbb R$, and $\\mathtt{complexCorollary}$ proves its specialisation to $\\mathbb C$.'
              }
            />
            <p>
              The generic proposition is defined for a normed scalar field. The
              two proved declarations displayed here concern the real and
              complex fields.
            </p>
            <p className="note">
              Over ℂ, the operators and continuous dual are complex-linear. The
              ambient 1-unconditional basis is contractive under complex
              coordinate multipliers of modulus at most one, including all
              phases. The complex theorem proves the basis conclusion.
            </p>
          </div>
          <div>
            <Statement symbol="UnconditionalCorollaryStatement" />
            <Proof symbol="realUnconditionalCorollary" />
          </div>
        </div>
        <Guide symbol="UnconditionalCorollaryStatement" />
        <div className="result-grid scalar-pair">
          <div>
            <h3>Complex specialisation</h3>
            <p>
              Substitute ℂ for the field in the complete proposition just above.
              This definition adds no new hypotheses or conclusions; the
              separate theorem below proves that specialisation.
            </p>
          </div>
          <div>
            <Statement symbol="ComplexCorollaryStatement" />
            <Proof symbol="complexCorollary" />
          </div>
        </div>
        <Guide symbol="ComplexCorollaryStatement" />
      </section>
      <section className="result" id="corollary-c">
        <h2>Corollary C</h2>
        <div className="result-grid">
          <div className="result-mathematics">
            <div className="panel-label">Mathematical statement</div>
            <Prose text={c.statement_tex} />
            <p className="note correspondence-note">
              The restriction to real scalars and the counterexample are given in §4.3
              and Corollary 4.6 of the manuscript.
            </p>
            <h3>The counterexample in Lean</h3>
            <Prose text={c.lean_statement_tex!} />
            <p className="note correspondence-note">
              The Lean statement describes the counterexample: neither
              complementary summand is isomorphic to a Banach lattice.
              It does not introduce a general predicate for a
              primary class. Here superreflexivity means isomorphism to a
              complete uniformly convex space.
            </p>
          </div>
          <div>
            <Statement symbol="SeparableNonprimarityStatement" />
            <Proof symbol="realSeparableNonprimarity" />
          </div>
        </div>
        <Guide symbol="SeparableNonprimarityStatement" />
      </section>
    </>
  );
}
