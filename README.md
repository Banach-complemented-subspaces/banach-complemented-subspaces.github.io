# The complemented subspace problem

Mathematical companion to Antonio Acuaviva's *A negative solution to the complemented subspace problem for Banach spaces with unconditional bases*.

This is a private preparation for publication. GitHub Pages must remain disabled until the author authorises public release. There is no automatic deployment workflow. The paper must be publicly available before the companion website is published.

## Read the website locally

On the author's laptop, double-click `OPEN_WEBSITE.cmd`, or visit <http://127.0.0.1:4173/> while its local server is running. To rebuild, use `BUILD_WEBSITE.cmd`.

On another computer, use Node.js 22.13 or later and restore the dependencies with `pnpm install --frozen-lockfile`. Run `node scripts/build.mjs`, then `node scripts/serve.mjs`. The server binds only to the local computer. The static website is written to `dist/client/`.

The author's updated final manuscript has 26 pages. Its PDF is `public/paper/manuscript.pdf`, copied without alteration. The retained LaTeX snapshot, `paper/main.tex`, precedes the two latest PDF corrections: “emphasized” becomes “emphasised”, and the Benyamini–Flinn–Lewis reference begins on page 145 rather than 143. No revised LaTeX file accompanied this PDF update. The main statements and pagination are unchanged. The paper includes the companion address `https://banach-complemented-subspaces.github.io/`. Earlier manuscript snapshots remain in Git history.

## Mathematical scope and architecture

The Results page presents Theorem A, Theorem B and Corollary C alongside five complete Lean proposition definitions and five proved declarations. The Definitions page gives the non-standard definitions and their exact source, with 25 expandable guides containing 136 clause readings across both pages.

The five verified declarations are `realMainTheorem`, `realCorollary`, `realUnconditionalCorollary`, `realSeparableNonprimarity` and `complexCorollary`, in the `ComplementedSubspace` namespace. The site distinguishes the paper's superreflexivity conclusion from the stronger uniform convexity required by the main real Lean statement. It does not claim that every result in the manuscript is formalised.

The `lean/` directory contains all 233 original source and configuration files from the audited snapshot, byte-for-byte unchanged. The original development README is retained at `lean/README.md` and in the source download. It records the proof architecture and the differences from the paper's proof, including finite frames and finite-sign moment estimates, and the real equivalence used in the complex argument. These alternative constructions do not change the five verified statements.

| Location | Purpose |
| --- | --- |
| `app/`, `components/` | Mathematical pages, exact Lean statements, guides and source links |
| `content/paper.json` | Current paper metadata and manuscript-to-Lean correspondence |
| `content/definitions.json`, `content/evidence.json` | Exact definitions, statements, declarations and recorded verification facts |
| `content/theorem-guides.json`, `content/definition-guides.json` | Exact clause excerpts and mathematical explanations |
| `lean/` | Frozen Lean source and pinned toolchain/dependency configuration |
| `public/evidence-public/` | Separately labelled public evidence copies and downloads |
| `public/asset-manifest.json` | Current website download hashes, alongside original hashes |
| `public/evidence-public/PUBLIC_COPY_SHA256.json` | Original and public SHA-256 hashes and sizes for copied files |
| `public/evidence-public/PUBLIC_ARCHIVE_MEMBERS_SHA256.json` | Original and public archive/member hashes, including nested ZIPs |
| `PUBLIC_FILES_SHA256.json` | Complete current public-directory hash manifest |
| `scripts/check-public-evidence.py` | Independent recursive hash and privacy checks for public downloads |
| `scripts/check-guides.mjs`, `scripts/build.mjs` | Exact excerpt coverage, frozen-source and public-file hashes, lint, TypeScript and production build |
| `content/publication.json` | arXiv and journal links; absent links remain unpublished |

The website uses the existing React/Vinext Sites scaffold, Shadcn controls and local KaTeX rendering. No analytics, remote fonts or cloud services are required. `.openai/hosting.json` has no hosting registration or cloud bindings.

## Public evidence preparation

The original website evidence was preserved outside this repository and outside the served directory before any preparation. The author also retains the original Lean project and both original audit collections. Nothing in those original records was edited.

Public copies replace personal computer location prefixes with `LEAN_PROJECT`, `WORKSPACE` and `USER_HOME`. Author attribution, mathematical statements, proof source, recorded audit results, dates and historical hashes are retained. Audit scripts containing those placeholders need their locations configured before use.

The three downloadable archives have `.PUBLIC.zip` names. Each includes `PUBLIC_COPY_README.md` and an original/public member hash manifest. The two nested frozen-source archives in the fresh audit remain byte-for-byte unchanged. Public evidence preparation is not a new Lean audit or a rerun of the historical audit scripts.

Hashes embedded in historical certificates, validation reports and original manifests continue to identify the original files. They must not be interpreted as hashes of the redacted copies. The separately labelled public manifests identify the prepared files and archive members. `PUBLIC_FILES_SHA256.json` also covers the newly written provenance documents.

For an independent check, run `python scripts/check-public-evidence.py`. The normal website build checks exact Lean excerpts, 233 frozen source/configuration hashes and the recorded public file hashes. The original audits' mathematical scope and limitations remain documented on the Verification page.

## Editing and eventual publication

Use British English and direct mathematical prose. Avoid “supplied”, “asserted” and “threshold”, and computing terms such as “data”, “input”, “output” and “endpoint” in mathematical explanations. Keep quoted Lean identifiers, source excerpts and archived mathematical statements verbatim.

Do not alter Lean excerpts to make them match a changed manuscript. A change to a mathematical statement requires corresponding verified source and evidence. The final statements of Theorem A, Theorem B and Corollary C are identical to the preceding LaTeX snapshot. The final abstract removes “complete” before “Lean 4 formalisation”. The website follows that wording and the final paper's numbering for its visible corollary references. Older detailed comparison notes retain both the numbering and page references of the earlier paper identified in `content/paper.json`; they are historical records. Updating the manuscript is not a new Lean audit.

The repository is [Banach-complemented-subspaces/banach-complemented-subspaces.github.io](https://github.com/Banach-complemented-subspaces/banach-complemented-subspaces.github.io). It is private with GitHub Pages disabled. The organisation is owned by the author's `ahacua` account.

The intended website address is [https://banach-complemented-subspaces.github.io/](https://banach-complemented-subspaces.github.io/). This is the organisation's own homepage, separate from the author's personal website. It is not yet published. The site uses paths relative to the domain root, so no project-name prefix is required. The build provides directory indexes for `/paper/`, `/definitions/` and `/verification/`, and a `.nojekyll` file for static hosting.

Before a later public release, confirm the final manuscript and companion address, recheck the published links, add available publication links, and obtain the author's explicit release instruction. Do not turn on Pages or create a public preview as part of private preparation.
