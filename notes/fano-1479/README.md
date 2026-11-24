# Fano incidence circuits with a double reread

L-meta-1479 asks for a monotone circuit on seven point inputs and seven line inputs. It must use at most 27 binary AND/OR gates, each reading two distinct earlier wires. An input is accepted exactly when it contains an incident point and line. At one such pair, the output's two directional linear parts must both vanish. Existence at 27 gates remains open in this work.

## A sufficient two-output construction

Fix point 0. Let `H` test whether the input contains an incidence involving a point other than 0. Let `N` test whether one of the three lines through 0 is selected. Given valid wires for both functions in one circuit, append two OR gates and one AND gate to compute `(H OR point₀) AND (H OR N)`. This equals the Fano incidence function. At the point-only and line-only inputs for incidence (1,1), both operands of the final AND vanish. Its linear parts therefore vanish in both directions. A 24-gate circuit computing the two wires would settle the posted problem. [JointFactor.lean](src/JointFactor.lean)

The reduction separates this open construction from the existence of a directional trace through an arbitrary normalized circuit. The trace follows any prescribed input seed and vanishes at a specified AND gate whose two operands are false on the base input. The companion proves the second child in the exact form printed by the desk checker. [TraceChild.lean](src/TraceChild.lean)

The six remaining point stars compute `H` with 23 gates. Two further OR gates compute `N`. Appending the three output gates gives a 28-gate example. The companion proves correctness for all inputs and both traces at incidence (1,1) in Lean. The two existence statements use the desk's first child with the bound changed to 25 and the original problem with the bound changed to 28. [Joint25.lean](src/Joint25.lean) · [Joint28.lean](src/Joint28.lean)

The Python checker independently evaluates the 28-gate construction on all 16,384 inputs and both directions at all 21 incidences. Exactly 12 incidences have two vanishing linear parts. It also checks the ordinary 27-gate star circuit, which has zero such incidences. [circuits.py](circuits.py)

## Structural results

- When each operand of a correct circuit's final AND accepts a singleton input, at least twelve incidences have both directional linear parts zero. The singleton inputs accepted by the two operands form opposite sides of a complete bipartite subgraph of the Fano incidence graph. One side has at most one vertex. The twelve edges outside its closed neighborhood give the stated traces. [TwelveFlags.lean](src/TwelveFlags.lean) · [FactorSupport.lean](src/FactorSupport.lean)
- Any correct AND-output circuit of size at most 26 yields a witness of size at most 27. If one operand accepts no singleton, the construction appends the AND of the original output and that earlier operand. [AndRoot.lean](src/AndRoot.lean) · [OnePad.lean](src/OnePad.lean)
- On an incidence, both singletons are rejected. Both directional linear parts vanish exactly when every proof tree for that incidence uses each of its two input variables at least twice. An OR chooses one child and an AND uses both. Repeated uses of a shared wire count separately in the tree. [FlagCertificates.lean](src/FlagCertificates.lean)
- Deleting point 0 leaves a graph with a unique cover by at most six star centers, namely its six remaining points. Two distinct points have at most one common line. In particular the three-line pencil at 0 shares no two-line OR with the six point stars in the explicit construction. [ResidualCover.lean](src/ResidualCover.lean)

## Reproducing the checks

The Lean sources use Lean 4.36.0. The build script checks the upstream revision, mathlib revision, and axioms of the default targets. Give it a built upstream `lean` directory checked out at `2e67c7c8499e2e12d39c1f31c085c0e4e94b0391` and a separate directory for generated files.

```sh
python build.py --upstream /path/to/pequalnp-proofs/lean --build-dir /path/to/fano-build
python circuits.py
```

## Prior work

The earlier reduction by kadakatzenberg uses extremal Boolean inputs and directional linear parts at the fixed incidence (0,0). The two-output construction supplies the output gates explicitly and isolates a 24-gate simultaneous computation. [Earlier reduction, PR #5650](https://github.com/open-goat/pequalnp-proofs/pull/5650)

Erywim separately proposed starting with a circuit of at most 25 gates for the full incidence function and allowing two gates for the reread. That proposal provides context for the padding results in this companion. [PR #7737](https://github.com/open-goat/pequalnp-proofs/pull/7737)

`OwnershipBase.lean` extracts the wire evaluation and strict-cone lemmas from the checked L-meta-1490 proof. The proof-tree and factor modules use those wire evaluation lemmas. [Upstream L_meta_1490.lean](https://github.com/open-goat/pequalnp-proofs/blob/2e67c7c8499e2e12d39c1f31c085c0e4e94b0391/lean/PEqualNP/Outside/L_meta_1490.lean)
