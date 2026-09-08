# NKBesicovitch

A [Lean 4](https://lean-lang.org/) project, built on
[mathlib](https://github.com/leanprover-community/mathlib4), for formalising work
around the **(n,k)-Besicovitch conjecture**.

## Status

Work in progress. Both requested theorems are stated in `Challenge.lean`, but
their central analytic proofs are incomplete. A successful build currently
includes two proof gaps, in addition to the two deliberate challenge holes.
This is **not yet a verified proof or a Palomar submission**.

The target range is

\[
  n < p_c^{k-1}+k,\qquad p_c^3-2p_c^2-2p_c+2=0,\quad 2<p_c<3,
\]

and the separate pair \((n,k)=(5,2)\). Here a Besicovitch set contains a
translate of the closed unit disk in every k-dimensional direction.
The exact constant is approximately 2.481194304; its existence, uniqueness,
and rational bounds have been proved in Lean. The corresponding projection
exponent is approximately 1.675130871.

Also proved are the full-dimensional boundary case, normalization of disk
averages, and the passage from a uniform open-set maximal estimate to a
quantitative volume lower bound. The delta version is proved using compact
disks, positive finite plate volumes, and Fatou's lemma with thresholds that
may vary by direction. Strict-margin selection shows that the target range
needs only projection estimates above the endpoint. The projection,
mixed-norm induction, and four-dimensional seed estimates remain to be developed.

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
| `comparator.json` | Compares both theorems and all three custom statement definitions |
| `NKBesicovitch/Basic.lean` | Euclidean space, disk property, exact exponent |
| `NKBesicovitch/Exponents.lean` | Certified root and projection-exponent arithmetic |
| `NKBesicovitch/Grassmannian/` | Directions and their projection-operator topology |
| `NKBesicovitch/Geometry/` | Disks and the full-dimensional case |
| `NKBesicovitch/Operators/` | Nonnegative disk, plate, and local X-ray operators |
| `NKBesicovitch/Projection/` | Line-family definitions and corner iteration arithmetic |
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
larger ratio above; that new analytic argument still requires formal proof.
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
