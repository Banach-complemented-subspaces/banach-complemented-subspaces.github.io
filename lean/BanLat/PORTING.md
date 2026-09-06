# Selectively vendored BanLat

These 21 modules are the dependency closure of `BanLat.Substructures.Band.PPP`
and `BanLat.Dual`, copied from David Muñoz-Lahoz's BanLat repository at commit
`5c9360ccd9cef27b749f3cabda6348fd2529d1a3`.

Source: <https://github.com/davidmunozlahoz/banlat/tree/5c9360ccd9cef27b749f3cabda6348fd2529d1a3>.
The upstream license is retained in `LICENSE` and author headers are unchanged.

The upstream project uses Lean 4.32.1; this project uses Lean 4.34.0-rc2.
Port changes are recorded below. Compilation and an axiom audit, rather than
the presence of source files alone, determine which modules are usable.

- `Basic.lean`: replace the broad `Mathlib.Tactic` import with the tactic
  modules used by this dependency closure. This avoids unrelated tactic and
  category-theory dependencies; mathematical statements and proofs are unchanged.
- `Basic.lean`: use `Mathlib.Basic.Real.Basic`, the new location of the
  deprecated `Mathlib.Data.Real.Basic` module.
- `Basic.lean`: explicitly import real order completeness and the dimension
  theory of division rings, previously obtained indirectly through the umbrella
  tactic import. `Basic.lean` compiles with its original theorem proofs.

`check-lattice-dependencies.ps1` checks the vendored closure serially to avoid
several simultaneous compiler processes. Its timestamp skip is an iteration
aid, not a substitute for the final integrated Lake build and axiom audit.

All 21 vendored modules, including `RieszKantorovich` and `Dual`, compiled
successfully under the pinned Lean 4.34.0-rc2 runtime on 5 September 2026.
No mathematical proof or statement changes were needed in the selected closure.
