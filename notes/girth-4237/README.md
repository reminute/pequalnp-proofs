# Girth-five graph edge functions and shared circuit gates

This Lean companion to L-meta-4237 proves conditional size bounds for fan-in-two monotone circuits computing the edge function of a graph of girth at least five. On a Boolean vertex input, the edge function is true when the input contains both endpoints of some edge. The existence of a universal linear bound in the posted problem remains open.

`GirthRepresent.checked_child` proves the first of the reduction's two child statements, in the exact form printed by the project verifier. The second child asks for a uniform bound for minimum-size monotone circuits that contain the witness, on graphs whose nonisolated vertices have degree at least three. [DeskChild.lean](src/DeskChild.lean)

## Results

- Fix an integer `k ≥ 0`. If `|E(G)| > (2^(k+1)−1)(s+1)`, the circuit contains `k+1` distinct gates, each read by at least two distinct later gates. For each earlier and later gate in that set, there is an input on which the later gate agrees with the output and the earlier gate disagrees. Its active vertices form either a clique of at most two vertices or the external neighborhood of such a clique. In the absence of this witness, `GirthRepresent.tested_easy` proves the edge bound for every `k`. [SampleWitness.lean](src/SampleWitness.lean) · [NativeWitness.lean](src/NativeWitness.lean) · [OrderedRepresentatives.lean](src/OrderedRepresentatives.lean)
- For an edge subset `S`, write `s` for the circuit size and choose an integer `B ≥ 1`. If at most `k` gates are read more than once and have sample-block rank greater than `B`, then `|S| ≤ (2^(k+1)−1) B (s+1)`. At `B=1`, one exceptional gate gives `3(s+1)` and two give `7(s+1)`. Here repeated occurrences in the same operand list count separately, and the designated output contributes one read. [FewShared.lean](src/FewShared.lean)
- For the graph class in the posted problem, the full L-meta-4237 statement is equivalent to the existence of a uniform `K` with `|E(G)| ≤ K(s+1)`. The proof inserts a constant-true gate into AND-gate cones, then uses a degree-core argument and a bound on the number of essential input vertices. [PostedEdgeEquiv.lean](src/PostedEdgeEquiv.lean)
- A separate bound counts distinct consumers of a gate on a path to the output. It gives `|S| ≤ s+1 + Σⱼ (liveReads(j)−1)(rank(j)−1)`, where subtraction is truncated at zero. A consumer reading the same wire twice contributes one live read. [LiveDagBound.lean](src/LiveDagBound.lean)
- The same bound `|S| ≤ (2^(k+1)−1) B (s+1)` holds with at most `k` representative gates on paths to the output. Each live gate of rank above `B` with multiple consumers must have a representative at or before its index. The representative must accept every positive sample the gate accepts and reject every negative sample the gate rejects. A gate can represent itself, so the bound also applies when at most `k` live gates have both high rank and multiple consumers. [LiveFewShared.lean](src/LiveFewShared.lean) · [RankExceptions.lean](src/RankExceptions.lean)
- For a signal measure subadditive under AND and OR, with zero weight on constants and input weight at most `B`, one shared gate of arbitrary fanout gives output weight at most `3B(s+1)`. The proof pins that gate separately to false and true. [PinnedSharing.lean](src/PinnedSharing.lean)

## Build

Use Python 3.9 or later and Git. Prepare a checkout of [open-goat/pequalnp-proofs at commit 2e67c7c](https://github.com/open-goat/pequalnp-proofs/tree/2e67c7c8499e2e12d39c1f31c085c0e4e94b0391), with Lean `leanprover/lean4:v4.36.0` and the package revisions in its manifest. In that checkout's `lean` directory, run `lake exe cache get` and `lake build PEqualNP.Defs`. The compiler uses mathlib revision `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. [Pinned manifest](https://github.com/open-goat/pequalnp-proofs/blob/2e67c7c8499e2e12d39c1f31c085c0e4e94b0391/lean/lake-manifest.json)

From this companion directory, choose an empty build directory outside the upstream checkout and run

```sh
python build.py --upstream /path/to/pequalnp-proofs/lean --build-dir /path/to/empty-build
```

The script verifies the checkout revision and toolchain, compiles the local source dependencies in order, and imports the entry modules for an axiom audit. It checks that each reported dependency belongs to `propext`, `Classical.choice`, or `Quot.sound`. It locates the standard elan toolchain automatically. Use `--lean /path/to/lean` to select another installation of the same release.

To check just the first child, append `--target DeskChild:GirthRepresent.checked_child`. Repeat `--target` to select several theorems. New entry modules can use the same option once their local imports are in `src/`. [build.py](build.py)

## Sources

- `OwnershipBase.lean` extracts the wire evaluation and strict-cone lemmas from the checked L-meta-1490 proof. [Upstream L_meta_1490.lean](https://github.com/open-goat/pequalnp-proofs/blob/2e67c7c8499e2e12d39c1f31c085c0e4e94b0391/lean/PEqualNP/Outside/L_meta_1490.lean)
- `PinnedShannon.lean` and `PinnedSupport.lean` reproduce the upstream circuit helper modules. The support file imports the local copy of Shannon. [Upstream Shannon.lean](https://github.com/open-goat/pequalnp-proofs/blob/2e67c7c8499e2e12d39c1f31c085c0e4e94b0391/lean/PEqualNP/MetaComplexity/Helpers/Shannon.lean) · [Upstream Support.lean](https://github.com/open-goat/pequalnp-proofs/blob/2e67c7c8499e2e12d39c1f31c085c0e4e94b0391/lean/PEqualNP/MetaComplexity/Helpers/Support.lean)
- The intersection matrix in `EdgeRank.lean` follows Stasys Jukna, *Boolean Function Complexity*, Theorem 7.2. The file gives a real right inverse using an edge's two endpoint columns and its edge column. `PlaneFormulaCore.lean` and `PlaneFormulaRankKW.lean` supply the formula datatype and rank lemmas from the team's earlier projective-plane work. [EdgeRank.lean](src/EdgeRank.lean) · [PlaneFormulaRankKW.lean](src/PlaneFormulaRankKW.lean)
