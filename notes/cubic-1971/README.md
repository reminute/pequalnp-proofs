# Cubic graph circuits · L-meta-1971

L-meta-1971 asks whether fixing some unmarked input to false saves at least four gates in a smallest circuit. The graph has girth at least seven, each unmarked vertex has degree three, and the circuit satisfies the assignment's limits on raw input reads. The general four-gate saving remains open.

The first reduction child proves that when the sole reader of a degree-three vertex is an AND and every later gate is an AND or OR, its partner depends on more than two other inputs. The remaining child asks for the four-gate saving in circuits satisfying the resulting restriction. The local project checker accepted the reduction and rechecked 1,648 constants. It printed children of 1,452 and 1,951 characters. [Exact first child](src/ClosedWidth.lean) · [Remaining child](remaining.statement) · [Implication from the remaining child](src/FromRemaining.lean) · [Reduction](src/Reduction.lean)

**A rejecting input for an AND gate.** Suppose a smallest fan-in-two circuit uses an AND with operands a raw input `v` and a wire `k`, and no NOT occurs after that gate. There is an input the circuit rejects on which `v` is true and `k` is false. Otherwise the gate could be replaced by `v` on every rejecting input. The later AND/OR gates preserve acceptance when a wire increases, so this replacement would compute the same function with one fewer gate. [Rejecting witness](src/RejectWitness.lean) · [Monotone suffix](src/SuffixBarrier.lean) · [Gate removal](src/NormalForm.lean)

**A restriction on a sole reader.** In the graph problem, suppose this AND is the only gate that effectively reads an unmarked vertex `v`. For every set of at most two other raw inputs, two assignments agree on those inputs and give different values to its partner wire. This also holds if either coordinate is marked. On a row where toggling `v` changes the graph output, the partner must enable the AND. Fixing the partner to the opposite value requires blocking all three neighbor branches, and girth makes their blocking literals distinct. [Partner width](src/PartnerWidth.lean) · [Signed certificates](src/PartnerCertificate.lean)

The companion also classifies the sole reader on the three-neighbor subcube, describes partners determined by two unmarked inputs, and proves a four-gate saving for an explicitly specified block with private intermediates. [Reader classification](src/NormalForm.lean) · [Two-input partners](src/EdgePartner.lean) · [Local four-gate saving](src/LocalSaving.lean)

## Reproduce the proofs

Use Python 3.9 or later, Git, and a checkout of `pequalnp-proofs` with `PEqualNP.Defs` and mathlib built. The build script accepts the publication baseline `19b9ebcdbad73b4e7dc900df1e5c49dc7034a8eb` and the earlier proof baseline `2e67c7c8499e2e12d39c1f31c085c0e4e94b0391`. Both use Lean `4.36.0` and mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. From this directory, give the script a separate output directory.

```sh
python build.py --upstream /path/to/pequalnp-proofs/lean --build-dir /tmp/cubic-1971
```

The script rebuilds the companion theorems from source, imports them in a fresh Lean process, and checks every selected axiom report against `propext`, `Classical.choice`, and `Quot.sound`. To check the literal solved child and its dependencies, append `--target ClosedWidth:Cubic1971.closedWidth`. An installation outside elan can be selected with `--lean /path/to/lean`. [Build script](build.py)

The graph lemmas used to separate the neighbor branches are included from the L-meta-4237 proof companion. The merged PR #5773 treats a sole reader with a distinct raw partner. PR #7700 proposed removing marked vertices, but the project declined that submission before its build. [Graph lemmas](src/EdgeNegatives.lean) · [PR #5773](https://github.com/open-goat/pequalnp-proofs/pull/5773) · [PR #7700](https://github.com/open-goat/pequalnp-proofs/pull/7700)
