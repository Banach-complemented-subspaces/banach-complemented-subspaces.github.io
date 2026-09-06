import { Lean, SourceLink } from '@/components/companion';
import evidence from '@/content/evidence.json';
const links = [
  ['verification_report.md', 'Verification certificate · public copy'],
  ['whole_project_axioms.txt', 'Axioms used by the theorems'],
  ['theorem_check.txt', 'Exact theorem checks'],
  ['build.log', 'Clean root-closure build log'],
  ['additional_modules_build.log', 'Supplementary module build log'],
  ['placeholder_audit.txt', 'Placeholder and axiom scan'],
  ['kernel_dependency_summary.json', 'Main theorem dependency traversal'],
  ['dependency_graph_review.json', 'Dependency graph review'],
  ['environment.txt', 'Environment and pinned dependencies'],
  ['source_hashes_after.json', 'Source SHA256 manifest'],
  ['run_status.json', 'Recorded audit exit codes'],
  ['report_guard_results.json', 'Final certificate consistency checks'],
];
export default function Verification() {
  return (
    <div className="page">
      <div className="page-title">
        <div className="eyebrow">Source & verification</div>
        <h1>What Lean checked</h1>
        <p>
          Original independent audit: <strong>PASS</strong> · 5 September 2026,
          23:29 UTC
        </p>
      </div>
      <div className="audit-summary">
        <p>
          The main real theorem and the four further theorems below
          were accepted under the pinned Lean and Mathlib versions. The audit
          rebuilt all 193 project library modules and checked the theorems’ axioms,
          placeholders, source integrity, and the main theorem’s transitive
          dependency graph.
        </p>
        <p className="note">
          This summary records the preserved 5 September audit. All 233
          original source and configuration hashes were
          rechecked when assembling the companion.
        </p>
        <table className="audit-table">
          <tbody>
            <tr>
              <th>Lean / Lake</th>
              <td>
                {evidence.environment.lean_version} /{' '}
                {evidence.environment.lake_version}
              </td>
            </tr>
            <tr>
              <th>Mathlib revision</th>
              <td>
                <code>{evidence.environment.mathlib_revision}</code>
              </td>
            </tr>
            <tr>
              <th>Clean project rebuild</th>
              <td>
                PASS · 177 root-closure + 16 supplementary modules · final build
                exit codes 0
              </td>
            </tr>
            <tr>
              <th>Executable placeholders</th>
              <td>0 sorry · 0 admit · 0 sorryAx in the scanned source scope</td>
            </tr>
            <tr>
              <th>Project mathematical axioms</th>
              <td>0 in the audited dependency chain</td>
            </tr>
            <tr>
              <th>Axioms of each theorem</th>
              <td>
                <code>propext, Classical.choice, Quot.sound</code>
              </td>
            </tr>
            <tr>
              <th>Audit scope</th>
              <td>
                234 local Lean files scanned, including four audit helpers;
                2,573 imported ComplementedSubspace declarations axiom-audited
              </td>
            </tr>
            <tr>
              <th>Main theorem traversal</th>
              <td>
                40,291 declarations · 1,332,580 edges · complete traversal, no
                missing bodies or constants
              </td>
            </tr>
            <tr>
              <th>Source preservation</th>
              <td>233 original Lean/configuration hashes unchanged</td>
            </tr>
            <tr>
              <th>Separate fresh kernel replay</th>
              <td>
                Not part of the original audit. See the extended fresh audit
                below for replay of the imported logical declarations.
              </td>
            </tr>
            <tr>
              <th>Archive reproduction</th>
              <td>
                Source hashes and reproduction instructions are available. A
                separate rebuild from an extracted archive is not recorded here.
              </td>
            </tr>
          </tbody>
        </table>
        <p>
          The certificate establishes that the stored Lean theorem was accepted
          by the stated kernel under pinned dependencies, without a placeholder
          or project-defined mathematical axiom in its audited dependency chain.
          It does not by itself establish that the proposition faithfully
          translates the paper. That correspondence is documented on the Results
          and Definitions pages for human inspection.
        </p>
        <div className="links">
          <a
            className="link-button primary"
            href="/evidence-public/raw/audit/verification_report.md"
          >
            View certificate · public copy
          </a>
          <a
            className="link-button"
            href="/evidence-public/raw/audit/verification_report.md"
            download
          >
            Download certificate · public copy
          </a>
          <a className="link-button" href="/evidence-public/verification_report_portable.md">
            Portable report with local links
          </a>
        </div>
        <p className="hash">
          Public copy SHA256: {evidence.certificate.public_report_sha256}
        </p>
        <p className="hash">
          Original certificate SHA256: {evidence.certificate.report_sha256}
        </p>
      </div>
      <section className="verification-section" id="extended-fresh-audit">
        <p>
          <strong>Extended fresh audit</strong> —{' '}
          <a href="/evidence-public/raw/full-fresh-audit/2026-09-06/evidence/report.html">
            View report
          </a>{' '}
          ·{' '}
          <a
            href="/evidence-public/raw/full-fresh-audit/2026-09-06/full-fresh-audit-evidence.PUBLIC.zip"
            download
          >
            Download evidence · public copy
          </a>
          {' · '}
          <a href="/evidence-public/raw/full-fresh-audit/2026-09-06/full-fresh-audit-evidence.PUBLIC.zip.sha256">
            Public archive SHA256
          </a>
        </p>
        <p className="note">
          PASS · 6 September 2026 · Snapshot{' '}
          <code title="875e2219bcfe9ea3c6a66a21fecbb077fc225b47e4ab39a0720f82735fe8fa3a">
            875e2219bcfe
          </code>
          . Pinned source reproduction, fresh kernel replay including imports,
          and theorem/axiom checks passed. The pinned Lean toolchain was retained.
        </p>
      </section>
      <section className="verification-section" id="declarations">
        <h2>The verified declarations</h2>
        <p>
          Every declaration below is closed: it takes no unproved mathematical
          assumptions as parameters. All names are in the namespace{' '}
          <code>ComplementedSubspace</code>.
        </p>
        {evidence.endpoints.map((e) => (
          <div key={e.symbol}>
            <Lean code={e.literal_signature} label="Lean theorem statement" />
            <p className="source-line">
              <SourceLink file={e.source_path} line={e.line_start}>
                Full proof source
              </SourceLink>
              <a href={'/' + e.axiom_evidence.planned_raw_url}>
                Recorded axiom list
              </a>
              <a href={'/#' + e.symbol}>Mathematical statement ↗</a>
            </p>
          </div>
        ))}
      </section>
      <section className="verification-section" id="evidence">
        <h2>Public evidence copies</h2>
        <p>
          Personal computer paths and account names have been removed from these
          separately labelled copies. The author retains the original evidence
          unchanged. The proofs and recorded audit conclusions are unchanged;
          this preparation is not a new Lean audit.
        </p>
        <p className="note">
          Hashes inside historical reports identify the original files. The
          public-copy manifests below give both original and new hashes,
          including archive members. Paths in audit scripts are placeholders to
          configure before use.
        </p>
        <div className="evidence-list">
          {links.map(([file, title]) => (
            <a key={file} href={'/evidence-public/raw/audit/' + file}>
              {title} ↗
            </a>
          ))}
        </div>
        <p className="links">
          <a href="/evidence-public/README.md">About the public copies</a>
          <a href="/evidence-public/PUBLIC_COPY_SHA256.json">Original and public file hashes</a>
          <a href="/evidence-public/PUBLIC_ARCHIVE_MEMBERS_SHA256.json">Archive member hashes</a>
          <a href="/asset-manifest.json">Current website file hashes</a>
          <a href="/evidence-public/companion-source-recheck.json">
            Companion’s 233-file source recheck
          </a>
          <a href="/evidence-public/raw/audit/build_scope.md">Detailed build scope</a>
          <a href="/evidence-public/raw/audit/dependency_provenance.txt">
            External dependency provenance
          </a>
        </p>
      </section>
      <section className="verification-section" id="downloads">
        <h2>Source & reproducibility</h2>
        {evidence.archives.map((a) => (
          <div key={a.filename} style={{ marginBottom: 25 }}>
            <a className="link-button" href={'/' + a.planned_url} download>
              {a.filename.includes('Independent')
                ? 'Download full independent audit archive'
                : 'Download verified Lean source'}{' '}
              ↓
            </a>
            <p className="note">
              {(a.bytes / 1000000).toFixed(2)} MB · Public copy
            </p>
            <p className="hash">Public copy SHA256: {a.public_sha256}</p>
            <p className="hash">Original archive SHA256: {a.recorded_sha256}</p>
          </div>
        ))}
        <p>
          For the portable 177-module proof build, follow{' '}
          <a href="/evidence-public/source-building.md">
            BUILDING.md from the verified-source ZIP
          </a>
          . To reproduce the full 193-module audit and its dependency graphs,
          follow{' '}
          <a href="/evidence-public/audit-reproduction.md">
            README.md from the independent-audit ZIP
          </a>
          ; the audit scripts need the Lean installation and save locations
          specified for your computer.
        </p>
        <p>
          Use the pinned <a href="/evidence-public/raw/source/lean-toolchain">toolchain</a> and{' '}
          <a href="/evidence-public/raw/source/lake-manifest.json">Lake manifest</a> with the
          source archive. The full audit archive includes the audit scripts,
          source snapshots, reproduction instructions, and full dependency
          graphs. The original certificate records the precise rebuild commands
          and scope.
        </p>
        <p className="note">
          The original 5 September audit rebuilt local project modules while retaining external
          dependency caches. It did not rebuild Lean or Mathlib from scratch.
          The enclosing repository had no project commit; source identity is
          recorded by hashes and archives.
        </p>
        <div id="proof-differences">
          <h3>Proof correspondence</h3>
          <p>
            Parts of the manuscript’s sphere/Gaussian presentation are replaced
            by finite frames and explicit finite-sign moment estimates. The
            formal complex argument uses a real equivalence of the constructed
            ranges to transfer the established DPR obstructions. The{' '}
            <a href="/evidence-public/raw/source/README.md">
              development’s architecture README
            </a>{' '}
            gives the full account.
          </p>
          <p className="note">
            Uses Mathlib and vendored BanLat; upstream credits and licences are
            preserved in the source archive.
          </p>
        </div>
      </section>
      <section className="verification-section">
        <h2>Historical audit-helper failures</h2>
        <p>
          Two intermediate helper failures are preserved: an unsupported
          pretty-printer option, and an incorrectly resolved <code>liftIO</code>{' '}
          in the dependency tracer. The audit helpers were corrected and rerun
          successfully. These were failed helper runs, not missing proofs in the
          main theorem.
        </p>
        <div className="links">
          <a href="/evidence-public/raw/audit/initial_failed_theorem_check.txt">
            Initial theorem-check failure
          </a>
          <a href="/evidence-public/raw/audit/initial_failed_dependency_trace.txt">
            Initial dependency-trace failure
          </a>
          <a href="/evidence-public/raw/audit/run_status.json">Final successful run status</a>
        </div>
      </section>
      <section className="verification-section" id="methodology">
        <h2>Attribution & methodology</h2>
        <p>
          The Lean development was produced entirely by ChatGPT in Codex, with
          minor supervision by the author. At the author’s request, alternative
          proofs were permitted where more efficient to formalise, to reduce
          token usage and formalisation overhead, while retaining the intended
          mathematical statements.
        </p>
      </section>
    </div>
  );
}
