# NKBesicovitch

A [Lean 4](https://lean-lang.org/) project, built on
[mathlib](https://github.com/leanprover-community/mathlib4), for formalising work
around the **(n,k)-Besicovitch conjecture**.

## Status

Work in progress. Both requested theorems are stated in `Challenge.lean`, but
their central analytic proofs are incomplete. A successful build currently
includes two proof gaps, in addition to the three deliberate challenge holes.
This is **not yet a verified proof or a Palomar submission**.

The target range is

\[
  n < p_c^{k-1}+k,\qquad p_c^3-2p_c^2-2p_c+2=0,\quad 2<p_c<3,
\]

and the separate pair \((n,k)=(5,2)\). Here a Besicovitch set contains a
translate of the closed unit disk in every k-dimensional direction.
The exact constant is approximately 2.481194304; its existence, uniqueness,
and the strict bounds `2.481 < criticalExponent < 2.482` have been proved in Lean.
For `k = 2`, the general theorem requires `n < p_c + 2 < 4.482`, so the `(5,2)`
result needs a separate proof. The corresponding projection
exponent is approximately 1.675130871.

Also proved are the full-dimensional boundary case, normalization of disk
averages, and the passage from a uniform open-set maximal estimate to a
quantitative volume lower bound. The delta version is proved using compact
disks, positive finite plate volumes, and Fatou's lemma with thresholds that
may vary by direction. Strict-margin selection shows that the target range
needs only projection estimates above the endpoint. The local strong X-ray
bound for general inputs is now proved. The chart transfer, induction, and
four-dimensional seed estimates remain to be developed.

The Grassmannian now has its natural probability measure, constructed from Haar
measure on the orthogonal group. Lean verifies that it is independent of the
initial plane and is the unique rotation-invariant probability measure. The
flag disintegration needed for the induction remains to be proved.

Plate maximal functions on open indicators are proved Borel measurable through
lower semicontinuity. The delta-to-volume argument therefore needs only its
uniform analytic estimate and a direction probability measure.

The projection development proves the two-slice seed, pair and corner
improvements, finite stopping argument, and projection estimates at every
exponent strictly above `1.675130871…`. The stronger selectable form is also
proved: in every positive-measure Borel subset of `[0,1]`, a jointly measurable
family of finite time patterns has polynomially controlled parameter volume,
coordinates, and projection constants. `Projection/Selection/Main.lean`
assembles this result. Common good-time selection now gives the restricted
X-ray estimate `r^K |F| ≤ C M(F)^(2-β) |E|^β` for `β_c < β ≤ 2` and some
integer `K > 2`. This gives the mixed-norm bound for each piece with
comparable parallel-fiber measures. The mixed norm uses Mathlib's `eLpNorm`,
and its countable triangle inequality is proved. The double dyadic
decomposition, interpolation, and summation now give the full indicator
estimate `‖T 1_E‖_(L^Q L^(Q/(β-1))) ≤ C |E|^(βθ/Q)` for every `0 < θ < 1`,
uniformly on fixed bounded support and slopes. Input superlevel decomposition
and homogeneity now extend this to the strong estimate
`‖T f‖_(L^Q L^(Q/(β-1))) ≤ C ‖f‖_p` for every `p > Q/β`.
`Operators/XRay/Strong.lean` proves it for all Borel nonnegative extended-valued
inputs supported in a fixed bounded set, with bounded Borel slopes. Zero and
infinite input norms are included. `FullLineBound.lean` extends this to the
full line integral with the same exponents. The transverse-to-perpendicular
displacement comparison and arclength factor are also proved. The direction
measure comparison and assembly over spherical charts remain incomplete.

See [PLAN.md](PLAN.md) for the source audit and detailed proof decomposition,
and [formalization.yaml](formalization.yaml) for provenance and proof status.

## Building

Requires [`elan`](https://github.com/leanprover/elan). The toolchain is pinned in
`lean-toolchain` and installed automatically.

```bash
lake exe cache get   # fetch prebuilt mathlib oleans
lake build
```

## Layout

| Path | Contents |
| --- | --- |
| `NKBesicovitch.lean` | Root module; imports everything below |
| `Challenge.lean` | Minimal Mathlib-only statement surface |
| `Solution.lean` | Matching theorem interface, currently with incomplete dependencies |
| `comparator.json` | Compares the exponent bounds, both positive-measure targets, and both definitions |
| `NKBesicovitch/Basic.lean` | Disk property and exact exponent, using Mathlib's Euclidean space directly |
| `NKBesicovitch/Exponents.lean` | Certified root and projection-exponent arithmetic |
| `NKBesicovitch/Grassmannian/` | Direction topology, orthogonal action, canonical probability |
| `NKBesicovitch/Geometry/` | Disks and the full-dimensional case |
| `NKBesicovitch/Operators/` | Nonnegative disk, plate, and local X-ray operators |
| `NKBesicovitch/Projection/` | Pair/corner estimates, finite stopping, and selectable projection schemes |
| `NKBesicovitch/PositiveMeasure/` | Passage from maximal estimates to measure |
| `NKBesicovitch/Induction/` | General-range proof frontier |
| `NKBesicovitch/FiveTwo/` | Separate (5,2) proof frontier |
| `lakefile.toml` | Package configuration and the mathlib dependency |
| `lean-toolchain` | Pinned Lean toolchain |

## Mathematical sources

The conjecture asks for positive measure whenever \(2\le k<n\).
Oberlin's [*Two bounds for the X-ray transform*](https://doi.org/10.1007/s00209-009-0589-5),
Theorem 3, relates this question to mixed-norm X-ray estimates. The supplied
September 2026 projection manuscript proposes the exponent leading to the
larger ratio above. Its projection estimate and quantitative selection now
have Lean proofs; the transfer and induction needed for the requested
positive-measure theorem remain incomplete.
The separate (5,2) route uses the corrected
[Guth–Zahl estimate](https://arxiv.org/abs/1701.07045),
[Katz–Rogers concentration theorem](https://arxiv.org/abs/1802.09094),
and a Fourier terminal step from the Bourgain–Oberlin method.
No claim of research priority or completed formalization is made at this stage.

## Verification status

The challenge and solution are separate Lake libraries; neither imports the
other. Comparator permits only `propext`, `Quot.sound`, and `Classical.choice`.
It must reject the current solution's `sorryAx` dependencies. The eventual
submission also requires independent kernel replay and a source-fidelity audit.
The standard Palomar verifier currently uses Linux tooling; it has not been run
on this macOS development machine.
