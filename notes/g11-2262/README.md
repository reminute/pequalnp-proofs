# G11 circuit lower bound, L-meta-2262

These Lean proofs establish two cases of the 22-gate lower bound in L-meta-2262. The target is the edge function of G11. On an input marking a set of vertices, the function is true exactly when both endpoints of a graph edge are marked. The graph has vertices 0 through 10 and 16 edges. [Graph and independent sets](src/G11NineEdges.lean)

The bound applies to a least fan-in-two AND/OR circuit for this function under the hypotheses of L-meta-2262. These include top form, the gate-count and residual minimum-cover inequalities, and two incomparable dirty AND gates with a common top. A dirty gate can output true on a negative graph input.

Let `U` be `Ustar G C`, the graph edges outside all raw cross pairs of tops. Let `r` be the cardinality of `orN G C \ lam G C`. This counts OR gates that can output true on a negative graph input, excluding gates in the distinguished set `lam`.

- `G11SmallUncovered.posted_with_small_U` proves `22 ≤ C.size` when `U.card ≤ 2`, for every value of `r`. [PostedSmall.lean](src/PostedSmall.lean)
- `G11Residual.posted_no_rare_all` proves `22 ≤ C.size` when `r = 0`, for every number of centreless tops. It combines the circuit structure with finite certificates on the 16 edges and independent vertex sets of G11. [PostedNoRareAll.lean](src/PostedNoRareAll.lean)

The remaining case of L-meta-2262 has both `0 < r` and `3 ≤ U.card`. At the common top, the two dirty gates may reach the same operand through OR gates or reach opposite operands.

The companion also checks the first two child statements of the four-child reduction for L-meta-2262. The first theorem, `G11Reduction.solved_small_or_zero`, combines the two cases above in the statement printed by the project checker. The second, `G11Reduction.solved_path`, shows that a dirty gate in the cone of a common top reaches at least one operand through an OR path under the child's top-form and incomparability assumptions. [ClosedChildren.lean](src/ClosedChildren.lean)

## Reproduce the checks

Use Python 3.9 or newer, Lean 4.36.0, and an already prepared upstream checkout at commit `2e67c7c8499e2e12d39c1f31c085c0e4e94b0391`. The upstream `lean/` directory must contain the compiled project definitions and its cached dependencies, including mathlib at `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. [Pinned upstream checkout](https://github.com/open-goat/pequalnp-proofs/tree/2e67c7c8499e2e12d39c1f31c085c0e4e94b0391/lean)

From this directory, use a fresh output directory for a clean check.

```sh
python build.py --upstream /path/to/pequalnp-proofs/lean --build-dir ./build
```

The script locates the installed elan release under `ELAN_HOME` or `~/.elan`. For another installation, pass `--lean /path/to/the/release/bin/lean`. On Windows, use the release's `lean.exe`. The script runs each compiler invocation with one worker, writes the companion modules to the specified build directory, then imports the entry points and runs `#print axioms`. The expected axioms for each theorem are `propext`, `Classical.choice`, and `Quot.sound`.

Use `--target MODULE:THEOREM` to check a single entry point and its dependencies. Repeat the flag to check additional declarations. All companion sources are in `src/`; compilation uses these sources and the prepared upstream libraries.

## Sources

- `ConeBase.lean` reuses the wire-evaluation and reachability lemmas in the checked L-meta-1490 proof. [L_meta_1490.lean](https://github.com/open-goat/pequalnp-proofs/blob/2e67c7c8499e2e12d39c1f31c085c0e4e94b0391/lean/PEqualNP/Outside/L_meta_1490.lean)
- The gate-removal and wire-renumbering arguments in `LeastAlias.lean` come from the checked L-meta-1485 proof. [L_meta_1485.lean](https://github.com/open-goat/pequalnp-proofs/blob/2e67c7c8499e2e12d39c1f31c085c0e4e94b0391/lean/PEqualNP/Outside/L_meta_1485.lean)
- The parent reduction R-meta-1597-318 uses the two disjoint triangles and disjoint five-cycle that give G11's vertex-cover lower bound of seven. `SmallUncovered.lean` uses these cycles to bound the cover after deleting `U`. [R_meta_1597_318.lean](https://github.com/open-goat/pequalnp-proofs/blob/2e67c7c8499e2e12d39c1f31c085c0e4e94b0391/lean/PEqualNP/Outside/R_meta_1597_318.lean)
