# Dependency audit of `ComplementedSubspace.realMainTheorem`

Scope: mechanical Lean/source verification only. This report does not compare the formal definitions or conclusions with any manuscript or natural-language theorem.

## Completed graph check: PASS

The final `TraceDependencies.lean` run exited **0**. Independent parsing of the raw graph agrees with every summary count and anomaly list:

| Checked item | Result |
|---|---|
| Reachable declarations / labelled dependency edges | 40,291 / 1,332,580 |
| Project declarations | 1,946 |
| Project defining modules | 136: 119 `ComplementedSubspace`, 17 `BanLat` |
| Project declarations with private `_private.` names | 150 |
| Direct target references | 224, including 34 project references |
| Principal source-map declarations found in graph | All 85; their source hashes still match |
| Missing constants, expected bodies, or origins | None |
| Reachable project axioms, opaque, unsafe, or partial declarations | None |

The independently traversed axiom set and stock `collectAxioms` both give exactly **`propext`, `Classical.choice`, and `Quot.sound`**. Graph traversal and origin classification are complete. The checked target is a theorem with type `ComplementedSubspace.RealMainTheoremStatement` and no universe parameters; its unfolded type agrees with the source target below.

The direct references confirm both synthesized geometry instances and every immediate helper application listed below. No source-trace correction was required. The 136 defining modules are the declaration-dependency count; the source theorem import closure (148 modules) and project-root build closure (177 modules) are separate scopes.

Evidence: `dependency_trace_run.txt`, `kernel_dependency_summary.json`, and the independent raw-graph/source-map review `dependency_graph_review.json`. The initial audit-helper compilation failure is preserved separately; the successful retry used explicit `IO`-to-`MetaM` lifts in audit machinery only.

## Exact declaration and hypotheses

The declaration is `ComplementedSubspace.realMainTheorem`, in `ComplementedSubspace/RealMainTheorem.lean:15`:

```lean
theorem realMainTheorem : RealMainTheoremStatement := by
```

There is no surrounding `variable`, section parameter, or typeclass hypothesis in that file. The theorem has a proof body, beginning with `intro ρ hρ`. The target is the definition at `ComplementedSubspace/TheoremStatement.lean:55`:

```lean
def RealMainTheoremStatement : Prop :=
  ∀ ρ : ℝ, 0 < ρ →
    ∃ a : BlockParameters,
      TopologicalSpace.SeparableSpace (Ambient a) ∧
      UniformConvexSpace (Ambient a) ∧
      HasRealBanachLatticeOrder (Ambient a) ∧
      ∃ P : Ambient a →L[ℝ] Ambient a,
        P.comp P = P ∧
        ‖P‖ < 1 + ρ ∧
        ‖ContinuousLinearMap.id ℝ (Ambient a) - P‖ < 1 + ρ ∧
        HasSeparatedRange P ∧
        HasSeparatedRange (ContinuousLinearMap.id ℝ (Ambient a) - P)
```

Thus the only universally quantified input after unfolding this target is a real number `ρ` and its positivity proof. In particular, none of the finite obstruction, Hilbert estimate, projection norm, DPR, or GL assertions is an extra hypothesis on `realMainTheorem`.

The definitions used in this type carry ordinary normed-space typeclass arguments. `HasRealBanachLatticeOrder` (`TheoremStatement.lean:34`) requires `NormedAddCommGroup`, `NormedSpace ℝ`, and `CompleteSpace`; `HasSeparatedRange` (`:42`) requires the first two. Those arguments are instantiated at the concrete `Ambient a` using its established instances. They are not independent parameters of the theorem. The separability and uniform-convexity witnesses are conclusions, provided by the proof's two `inferInstance` expressions.

`BlockParameters` is the structure at `Ambient.lean:23`, with positive dimensions and the displayed exponent fields. `Block` (`:39`) abbreviates a finite `PiLp` space, and `Ambient` (`:43`) abbreviates `lp (Block a) 2`. `HasSeparatedRange` is a conjunction of four formulas involving `chiGL`, `chiDPR`, the projection range, and its continuous dual. These are definitions of the target objects/propositions, not assumptions of their asserted properties.

## Immediate source applications

Every filename in the following table is relative to `ComplementedSubspace/`. This is the explicit proof-source map, including the two synthesized proof instances. The generated `dependency_direct.jsonl` gives the exact elaborated direct constant references, including elaborator-generated and library references; all entries below were confirmed in that completed graph.

| Declaration | File:line | Role in the target proof |
|---|---|---|
| `exists_recursive_alternatingProjection_near_one` | `RecursiveProjection.lean:146` | Supplies `η`, its positivity proof, `P`, idempotence, both strict norm bounds, and the coordinate formula. |
| `recursiveFrameSelection` | `RecursiveParameters.lean:293` | Definition choosing the recursive parameter data, locally named `s`. |
| `RecursiveFrameSelection.toBlockParameters` | `RecursiveParameters.lean:234` | Definition extracting the ambient block parameters. |
| `ambientSeparableSpace` | `AmbientSeparable.lean:16` | Synthesized proof instance for the separability conclusion. |
| `ambientUniformConvexSpace` | `AmbientUniformConvex.lean:17` | Synthesized proof instance for the uniform-convexity conclusion. |
| `ambient_hasRealBanachLatticeOrder` | `AmbientLattice.lean:121` | Supplies the compatible lattice-order conclusion. |
| `hasSeparatedRange_of_DPR_obstructions` | `ProjectionCorollaries.lean:27` | Applied twice to assemble the four range/dual assertions. |
| `ambient_chiGL_le_one` | `AmbientFiniteApproximation.lean:91` | Supplies the ambient GL bound in both applications. |
| `ambientDual_chiGL_le_one` | `AmbientFiniteApproximation.lean:110` | Supplies the ambient-dual GL bound in both applications. |
| `actualProjection_range_chiDPR_eq_top` | `ActualProjectionDPR.lean:18` | Supplies the range DPR obstruction. |
| `actualProjection_range_dual_chiDPR_eq_top` | `ActualProjectionDualDPR.lean:19` | Supplies the range-dual DPR obstruction. |
| `actualProjection_complement_range_chiDPR_eq_top` | `ActualProjectionDPR.lean:27` | Supplies the complementary range DPR obstruction. |
| `actualProjection_complement_range_dual_chiDPR_eq_top` | `ActualProjectionDualDPR.lean:28` | Supplies the complementary range-dual DPR obstruction. |
| `complement_idempotent` | `RecursiveProjection.lean:12` | Proves idempotence of `id - P` from the supplied idempotence of `P`. |

The local destructuring also receives lower bounds `hP1` and `hPc1`; the final target uses the supplied strict upper bounds. The proof does not invoke `corollary_negations_of_DPR_obstructions`, `realMainConsequences`, or the bidual DPR theorem explicitly.

## Principal proof branches

### Recursive projection and parameter construction

`exists_recursive_alternatingProjection_near_one` calls `exists_recursive_alternatingProjection_tolerance` (`RecursiveProjection.lean:122`). The latter calls `exists_recursive_complement_tolerance` (`ReindexedFrameProjection.lean:138`) and constructs the diagonal map `RecursiveFrameSelection.alternatingProjection` (`RecursiveProjection.lean:60`). Its idempotence and norm estimates are proved through the `lpDiagonal` lemmas in `AmbientProjection.lean`.

The complementary finite-block estimate calls `exists_finTensorProjection_complement_threshold` (`ReindexedFrameProjection.lean:82`). That proof explicitly combines `exists_localHilbert_subspace_threshold` (`LocalHilbert.lean:204`), `finitePiLp_parallelogram_le` (`FiniteLpGeometry.lean:93`), and `norm_complement_le_of_localHilbert` (`LocalHilbertProjection.lean:71`) with the finite tensor projection's identity/nonzero/norm lemmas. The primary projection norm reaches `tensorFrameProjection_norm_le_exp` (`TensorProjection.lean:159`) through `finTensorProjection_norm_le_exp` (`ReindexedFrameProjection.lean:76`).

The selected data are obtained by the definition `recursiveFrameSelection`, using the proved `exists_recursiveFrameSelection` (`RecursiveParameters.lean:180`). Its finite recursion uses the private theorem `exists_nextFrameChoice` (`:108`), which is part of the relevant source branch despite having a private generated kernel name. The structure fields such as `quadratic_error`, `overlap_separation`, and the head bounds are then supplied by that constructed data; they are not unproved top-level axioms.

### Primal DPR obstruction

The two `actualProjection_*_chiDPR_eq_top` proofs first recover bounded block maps and identify the actual operator with `lpDiagonal` using the coordinate formula. Both then call `recursiveDiagonalRange_chiDPR_eq_top` (`RecursiveDiagonalDPR.lean:16`). The range application uses the even-index frame isometry; the complementary range uses the odd-index complementary isometry. The definitions are `frameCoefficientEvenRangeEquiv` and `frameCoefficientOddComplementRangeEquiv` in `FrameCoefficientReindexedRange.lean:40,46`.

`recursiveDiagonalRange_chiDPR_eq_top` directly calls `frame_block_le_chiDPR` (`FiniteBlockDPRLower.lean:17`), supplying the actual diagonal summand maps from `DiagonalFrameSummand.lean`, the recursive overlap separation, and `recursiveDiagonalRange_kernel_locallyHilbert` (`RecursiveKernelHilbert.lean:45`). It turns arbitrary finite lower bounds into `chiDPR = ⊤` through `chiDPR_eq_top_of_nnreal_lower_bounds`.

`frame_block_le_chiDPR` applies `le_chiDPR_of_basis_obstruction` from `DPRObstruction.lean`, constructs finite superspace splitting maps from `FiniteSuperspaceSplitting.lean`, and invokes `finite_basis_obstruction_with_frame_summand_of_scale` (`FiniteBlockObstruction.lean:70`). That proof calls the finite scalar bounds and then `finite_basis_obstruction_with_frame_summand` (`:22`). The latter uses the proved `exists_frame_selectedHilbertFactorization` (`FiniteSelectedHilbertModel.lean:78`) and `finite_selected_trace_obstruction` (`FiniteOverlapObstruction.lean:126`). The trace obstruction is proved from `finite_selected_trace_scale_le` and `finite_selected_projection_overlap_le` in the same file, reaching `finite_basis_overlap_scaled_bound` (`FiniteOverlapConclusion.lean:17`) and `frame_trace_forces_projection_overlap` (`ProjectionOverlapLower.lean:34`).

Although `RecursiveDiagonalDPR.lean` imports `InfiniteFrameObstruction.lean`, its proof directly applies `frame_block_le_chiDPR`; it does not simply cite that imported file's `chiDPR_eq_top_of_frame_summands` theorem. This distinction is why the source applications, rather than just the import list, are recorded here.

### Dual DPR obstruction

The two dual actual-projection proofs call `recursiveDiagonalRange_dual_chiDPR_eq_top` (`RecursiveDiagonalDualDPR.lean:16`) with the same even/odd finite range isometries and coordinate identifications. This recursive dual proof directly applies `frame_product_le_chiDPR_dual` (`FiniteDualDPRLower.lean:20`), using the constructed `diagonalFrameProductEquiv` (`DiagonalFrameProduct.lean:19`) and `recursiveDiagonalRange_kernel_dual_subspaces` (`LocalHilbertRecursiveKernelDual.lean:59`).

`frame_product_le_chiDPR_dual` constructs the actual dual product equivalence from `realDualIsometryEquiv` and `prodL2DualEquiv`; then, for a finite superspace, it uses `finiteSuperspaceDualProductEquiv`, `continuousDualBasis`, and `continuousDualBasis_constant_le`. Its contradiction is `finite_basis_obstruction_of_frame_product` (`FiniteProductObstruction.lean:15`), which calls the shared `finite_basis_obstruction_with_frame_summand`. Thus the dual branch contains a separate finite dual/superspace argument and is not supplied as a hypothesis to the final theorem.

### Kernel geometry used by the obstructions

The primal kernel theorem combines `lpDiagonalRangeKernelHeadTailIsometry` with `recursiveProfile_finiteHead_hasHilbertNormWithin` (`RecursiveHeadHilbert.lean:41`) and `recursiveProfileTail_locallyHilbert` (`RecursiveTailHilbert.lean:40`) through `locallyHilbert_of_isometricEmbedding_prodL2` (`RecursiveKernelHilbert.lean:13`).

The dual kernel theorem calls `recursiveProfile_embedding_dual_subspaces` (`LocalHilbertRecursiveKernelDual.lean:20`). That proof uses `recursiveProfile_finiteHead_hilbertModel` (`RecursiveHeadHilbert.lean:63`), `recursiveProfileTail_approxParallelogram` (`RecursiveTailHilbert.lean:27`), the head/tail renorm equivalence, and `embedded_renorm_dual_subspace_dual_localHilbert` from `LocalHilbertEmbeddedRenorm.lean`. The local Hilbert thresholds ultimately come from the proved local Hilbert results in `LocalHilbert.lean` and their supporting coordinate/compactness development. The helper theorems have explicit finite-dimension and norm-bound premises; the recursive proofs supply those premises before the target theorem is assembled.

### GL estimates and ambient approximation

`hasSeparatedRange_of_DPR_obstructions` assembles two supplied DPR equalities with `chiGL_range_le_projection_norm_all` (`ProjectionCorollaries.lean:18`) and `chiGL_dual_range_le_projection_norm` (`GLDualRetraction.lean:81`).

The primal GL inequality reaches `chiGL_range_le_projection_norm` (`GLRetraction.lean:196`), `chiGL_le_norm_product_of_retraction`, and `chiGL_le_of_retraction` (`:143`). These use the explicit factorization construction `GLFactorization.throughRetraction` (`:39`) and its norm/cost bounds. The dual proof constructs the adjoint retraction with `dualPullback` (`GLDualRetraction.lean:21`), proves its norm bounds and retraction identity, and applies the GL retraction inequality. The zero-range case is handled by a proof that the GL constant of a subsingleton space is zero.

`ambient_chiGL_le_one` combines `chiGL_le_chiDPR` (`DPRtoGL.lean:199`) with an ambient DPR upper bound from finite unconditional approximations. Those approximations come from the dense disjoint scalar coordinates in `AmbientBasis.lean` and `AmbientFiniteApproximation.lean`, via `chiDPR_le_constant_of_finite_approximations` (`FiniteApproximation.lean:131`).

`ambientDual_chiGL_le_one` combines the same DPR-to-GL comparison with `ambientDual_chiDPR_le_one` (`AmbientFiniteApproximation.lean:103`), whose proof applies `chiDPR_dual_lattice_le_one` (`LatticeApproximation.lean:41`). The latter reaches finite disjoint approximation and basis proofs in `LatticeSpectral.lean`/`LatticeBasis.lean`, and the dual-lattice instances imported from `BanLat.Dual`. This is an actual proof dependency on the local BanLat development, rather than merely a broad root import.

### Ambient geometry

The inferred `ambientSeparableSpace` instance uses the density of the span of block inclusions, proved from `hasSum_blockProjection` (`Ambient.lean:90`).

The inferred `ambientUniformConvexSpace` instance applies `lp_two_uniformConvexSpace_of_cubicModulus` (`LpTwoUniformConvex.lean:137`) to `block_hasCubicSumModulus` (`AmbientUniformConvex.lean:11`). The latter calls `finitePiLp_uniform_modulus` (`FiniteLpGeometry.lean:182`), whose source branch includes the finite Clarkson estimate. These are proof declarations producing the requested instance.

`ambient_hasRealBanachLatticeOrder` constructs its existential witness from the local `PiLp` and `lp` lattice, ordered-addition, scalar-monotonicity, and solid-norm instances in `AmbientLattice.lean`. Completeness is inherited from the established normed `PiLp`/`lp` construction.

## Definitions versus proof claims

The principal statement-level definitions are in `TheoremStatement.lean`; the constants themselves are defined in `LocalUnconditional.lean`: `unconditionalBasisConstant:62`, `unconditionalConstant:109`, `lambdaDPR:125`, `chiDPR:130`, `GLFactorization:159`, `lambdaGL:359`, and `chiGL:364`. The source contains values for these definitions. This audit records where those expressions and structures come from; it makes no natural-language faithfulness claim about them.

Theorems such as `frame_block_le_chiDPR` have numerous genuine hypotheses because they are reusable intermediate results. The source trace above identifies the later proofs that discharge them. A hypothesis of an intermediate result is not an axiom or an extra parameter of the final closed theorem.

## Axiom and unsafe-declaration inspection

The independent placeholder scanner reports no executable `axiom`, `constant`, `opaque`, `unsafe`, `partial`, `sorry`, `sorryAx`, `admit`, `native_decide`, `implemented_by`, or `extern` declarations in the 148-module local syntactic import closure of `RealMainTheorem.lean`. The detailed token/comment-aware evidence is in `placeholder_scan.json` and its companion report. This is source-scan evidence; the full compiled dependency traversal is a separate check.

Three imported project files use `set_option allowUnsafeReducibility true`, followed by local reducibility attributes: `ProductFrameMoments.lean:10`, `ProductFrameSymmetry.lean:6`, and `ProductFrameTrace.lean:69`. These are not `unsafe` mathematical declaration keywords. The compiled auditor nevertheless checks `ConstantInfo.isUnsafe` and `.isPartial` on every reachable constant and separately records any project-origin axiom or opaque constant, including private declarations.

The mathematical audit has not modified any `.lean` file in `ComplementedSubspace/` or `BanLat/`. `TraceDependencies.lean` is separate audit machinery and does not supply the theorem with a hypothesis or proof replacement.

## Mechanical graph methodology and run artifacts

`TraceDependencies.lean` imports the actual project root, then obtains the target from `env.checked.get.find?`. It walks every reachable declaration with a visited set. Edges are labelled `type`, `value`, or `inductive_constructor`. For definitions, theorems, and opaque declarations, values are requested using `ConstantInfo.value? (allowOpaque := true)`. The default `false` would omit theorem proofs and would not suffice for this audit.

The edge convention matches the pinned Lean `CollectAxioms.collect`: types and values for definitions/theorems/opaque declarations; types for axioms, constructors, and recursors; types plus constructors for inductives; quotient primitives as leaves. `Expr.getUsedConstants` includes constants inside expressions and structure projection type names. The walker uses the checked environment directly and does not substitute cached imported axiom lists for proof-body traversal. It separately calls stock `collectAxioms` as a cross-check.

Origins are determined with `Environment.getModuleIdxFor?` and `allImportedModuleNames`, not just declaration-name prefixes. Consequently local private names with an `_private...` prefix are still counted as project-owned if their defining module is under `ComplementedSubspace` or `BanLat`. Missing checked constants, missing expected bodies, and absent import-origin entries are recorded rather than silently discarded. The run fails if the graph or origin classification is incomplete, or if its axiom list disagrees with stock `collectAxioms`.

The traversal emits:

- `dependency_nodes.jsonl`: every visited constant, declaration kind, defining module, project ownership, unsafe/partial/body flags, and the type/Prop status of suspicious local constants.
- `dependency_edges.jsonl`: the complete labelled dependency graph.
- `dependency_direct.jsonl`: the target's immediate elaborated references and their origins/kinds.
- `kernel_dependency_summary.json` and `dependency_trace.txt`: counts, completion status, axiom cross-check, and explicit anomaly lists.
- `dependency_source_map.json`: 85 independently selected principal source declarations with mechanically checked line numbers and source SHA-256 hashes, produced by `map_dependency_sources.ps1`.

The final graph execution passed, as recorded in `dependency_trace_run.txt` and summarized above. The dependency agent independently parsed the resulting graph and source map using `review_dependency_graph.py`; it did not run Lean or compile the project. The root agent remained the sole Lean compiler runner.
