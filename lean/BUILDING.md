# Reproducing the verified Lean build

Extract the archive and run commands from its single
`Complemented_Subspace_Lean_Verified` directory. Install Git and elan first.
The commands below work with the standard elan `lake` command on Windows,
macOS and Linux; they do not need this project's original local toolchain path.

To match the recorded build's resource settings, set `LEAN_NUM_THREADS=2`
before running Lake: `$env:LEAN_NUM_THREADS = '2'` in PowerShell, or
`export LEAN_NUM_THREADS=2` in a POSIX shell. The project configuration already
passes `-j1 -M8192` to each project and BanLat Lean compiler process.

```text
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake --no-cache build +ComplementedSubspace:olean
lake --no-cache env lean WholeProjectAudit.lean
```

`lean-toolchain` selects Lean 4.34.0-rc2 automatically. `lakefile.toml` pins
Mathlib to commit `4cbb42e75a050e830b7cf0f2ae748d7644f59cf7`, and
`lake-manifest.json` pins its dependency revisions. Retain both files; do not
update dependencies when reproducing this result. The cache command fetches
matching dependency artifacts and may require a network connection. No
dependency binaries or cache directories are included in the archive.

The `+ComplementedSubspace:olean` target rebuilds the root module and its
transitive import closure. This matters: the archive also contains standalone
review material which is not a second library root. `WholeProjectAudit.lean`
imports the live root and rejects every project declaration with a transitive
axiom outside `propext`, `Classical.choice`, and `Quot.sound`.

All vendored BanLat sources are included with their upstream license and
`BanLat/PORTING.md`. Mathlib and its own dependencies remain external,
version-pinned Lake dependencies. Source-only packaging follows the actual
root import graph; unused experiments, scratch modules, `.lake`, `.cache`
and binary outputs are excluded.

`manuscript/` preserves the supplied LaTeX sources verbatim for independent
statement and proof comparison. These are mathematical references, not build
instructions or additional formalized claims. Its README records the precise
scope of the Lean endpoints. PDF outputs and unrelated assets are excluded.

## Statement review files

`MainTheoremReview.lean` imports the current project statement and presents
readable aliases and definitional-equality checks. It can be checked with
`lake --no-cache env lean MainTheoremReview.lean` after the library build.

`MainRealTheoremDefinitions.lean` is a standalone review snapshot, retained
at the user's request. It imports Mathlib only and reproduces the definitions
in the project namespace. Check it separately with
`lake --no-cache env lean MainRealTheoremDefinitions.lean`; do not import it
together with the live library, since that would redeclare the same names.
These review files state and explain the target. The actual proofs are in
the imported `RealMainTheorem`, `RealMainConsequences`, and `ComplexCorollary`
modules.

## Logs, hashes and optional Windows helpers

`verification/` contains the recorded text build and axiom-audit logs,
including historical intermediate checks. The final fresh-build log ends
with its success marker. The progress and semantic-review notes explain
proof changes from the manuscript; their historical checkpoints should be
read alongside the final README status.

`SOURCE-MANIFEST.sha256` lists SHA-256 hashes of every packaged file except
the manifest itself. Paths are relative to the extracted directory. It hashes
the exact archived bytes, including source, configuration, notes and logs.
For example, on systems with `sha256sum`, run
`sha256sum -c SOURCE-MANIFEST.sha256` from that directory.

The original `run-lean.ps1`, `check-lean-direct.ps1`,
`check-lattice-dependencies.ps1`, `get-mathlib-cache.ps1` and
`rebuild-verified.ps1` are preserved unchanged as provenance. They expect the
original external portable toolchain under `../../tmp/` and are not portable
build entry points. Use the standard elan/Lake commands above after extraction.
The rebuild helper's `-Resume` option retains the prior root-only clean and
continues a failed build after a source repair; Lake checks dependency hashes
and rebuilds affected modules before rerunning the complete axiom audit.

`package-verified.ps1` needs only PowerShell and .NET. It recreates the
source-only archive in the parent directory, with stable entry ordering and
timestamps. `-ListOnly` prints its selection without creating files;
`-ReplaceExisting` explicitly permits replacement of the same archive.
Packaging requires the completed fresh build/audit log and rejects active
build inputs modified after that verification. It performs no recursive
deletion. Identical file bytes yield identical archives on the same .NET
compression implementation; a new build log naturally changes the archive.
