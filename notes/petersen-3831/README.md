# Signed Petersen circuits · L-meta-3831

The checked reduction leaves one question open. Can a circuit of at most 14 gates compute the signed nine-input Petersen edge function when its unique reader of input zero has an internal partner and a later NOT changes on at least three of the 32 sensitive input pairs? The original assignment follows from a negative answer. [Remaining statement](remaining.statement) · [Lean implication](src/FromRemaining.lean)

**The first child is proved.** In every candidate computing the target, the other operand of the unique reader is an internal wire. Some strictly later NOT outputs true before the physical input changes from zero to one and false afterward on at least three distinct sensitive pairs. The local project verifier accepted the reduction with two children, of 1,722 and 1,723 characters. It rechecked 1,649 constants on the submission base and 1,645 on the earlier proof baseline. The first proof uses the verifier's literal printed statement. [First child](src/Child.lean) · [Reduction source](src/Reduction.lean) · [Packed representation](src/Packed.lean)

## Why the three pairs exist

- Enumerating the eight other inputs gives 32 settings on which the graph changes at vertex zero. For any candidate raw partner, this set contains a setting where it is false and one where it is true. On one of those pairs, the AND or OR masks the only read of input zero. [Sensitive rows](src/SensitiveRows.lean) · [Raw-partner proof](src/RawPartner.lean) · [Equivalence with the internal-only case](src/RawBridge.lean)
- On each sensitive pair, flip the physical input from false to true. The required output falls from true to false. Tracing changed operands backward gives an odd number of inversions on a path. Since the unique first reader is an AND or OR, some later NOT on the path falls on that pair. The circuit model's default for missing and forward wire reads is included in the argument. [Signed path](src/SignedPath.lean)
- The falling NOTs cover all 32 pairs. Summing their cover sizes over at most 14 gates forces one gate to cover at least three. The four-word bitset in the reduction records the eight free inputs, with vertex zero omitted. [Cover count](src/InversionCover.lean) · [Packing proof](src/Packed.lean)

## Additional checked restrictions

- Pinning physical input zero to true produces a fan-in-two circuit for the unsigned eight-input residual graph. The actual constant-propagation result retains at least 12 gates. If the reader is an OR, it becomes true and each subsequent gate reading its output also disappears after effective operands are normalized. A circuit with at most 14 gates can have at most one such subsequent gate. [Cofactor and lower bound](src/Cofactor.lean) · [Consumer count](src/CofactorFanout.lean)
- An AND with a partner always equal to true, or an OR with a partner always equal to false, can be bypassed without changing the circuit's function. The checked fixed-first-AND lower bound excludes these cases. In the OR case, any internal partner whose prefix value depends on at most two of the eight other inputs is also excluded. [Erasure](src/ErasePartner.lean) · [Constant case](src/ConstantClosed.lean) · [Two-input OR case](src/ClosedPartner.lean)

## Reproduction

Use Python 3.9 or later, Git, and an upstream checkout with its `lean` project built. The submission base is `60161243826570a9c92d2752bec0224eb9efe53d`. The script also accepts the earlier proof baseline `2e67c7c8499e2e12d39c1f31c085c0e4e94b0391`. Both use Lean `4.36.0` and mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Run the following command from this directory to rebuild the exact solved child and its five source dependencies.

```sh
python build.py --upstream /path/to/pequalnp-proofs/lean --build-dir /tmp/petersen-child --target Child:Petersen3831.checked_child
```

To check the implication and all additional results in a separate directory, run

```sh
python build.py --upstream /path/to/pequalnp-proofs/lean --build-dir /tmp/petersen-all
```

The script compiles the selected companion modules and their dependencies from source, then imports each entry point and checks its axiom report. It permits Lean's `propext`, `Classical.choice`, and `Quot.sound`. For the additional restrictions it also rebuilds four proof files from the pinned upstream tree and verifies their worktree contents against that revision. Their declaration namespaces are preserved. Pass `--lean /path/to/lean` to select a release binary outside the usual elan installation. [Build script](build.py)

## Prior proofs

Rob1Ham's earlier reduction already requires an internal partner enabled on sensitive rows in the open cases and splits those cases by the reader's operation and gate position. That reduction was officially checked at `3882f4f0`. The additional condition proved here is a signed path downstream of the reader and a single later NOT that falls on at least three of the 32 sensitive input pairs. [Rob1Ham, PR #9236](https://github.com/open-goat/pequalnp-proofs/pull/9236)

The wire-evaluation and strict-cone lemmas in `OwnershipBase` come from the accepted L-meta-1490 proof. The source extract and the generic input-renaming lemmas are reused from the Fano companion. The residual-edge proof specializes the earlier Petersen relabelings to the two first-AND representatives. [Ownership source](src/OwnershipBase.lean) · [Upstream L-meta-1490](https://github.com/open-goat/pequalnp-proofs/blob/2e67c7c8499e2e12d39c1f31c085c0e4e94b0391/lean/PEqualNP/Outside/L_meta_1490.lean) · [Prior companion](https://github.com/reminute/pequalnp-proofs/tree/a1ca6b03d9659f314839b213621c49ee0a5587ce/notes/fano-2348) · [Residual-edge relabelings](src/EdgeAndCases.lean)

The two-coordinate case uses the upstream fixed-first-AND lower bounds for pairs (0,1) and (0,4). The latter credits the restriction and frontier certificates from L-meta-1672. The cofactor proof uses L-meta-2305's simplifier, adapted there from stierms's L-meta-517, and L-meta-2307's eight-input lower bound, which credits L-meta-1664. [L-meta-1667](https://github.com/open-goat/pequalnp-proofs/blob/2e67c7c8499e2e12d39c1f31c085c0e4e94b0391/lean/PEqualNP/Outside/L_meta_1667.lean) · [L-meta-1670](https://github.com/open-goat/pequalnp-proofs/blob/2e67c7c8499e2e12d39c1f31c085c0e4e94b0391/lean/PEqualNP/Outside/L_meta_1670.lean) · [L-meta-2305](https://github.com/open-goat/pequalnp-proofs/blob/2e67c7c8499e2e12d39c1f31c085c0e4e94b0391/lean/PEqualNP/Outside/L_meta_2305.lean) · [L-meta-2307](https://github.com/open-goat/pequalnp-proofs/blob/2e67c7c8499e2e12d39c1f31c085c0e4e94b0391/lean/PEqualNP/Outside/L_meta_2307.lean)
