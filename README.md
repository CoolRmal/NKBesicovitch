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
needs only projection estimates above the endpoint. The strong geometric
X-ray bound for general inputs and the finite plate induction are now proved.
The fixed-support Schwartz Fourier terminal estimate is now proved.
Disk localization, approximation, and the four-dimensional seed remain incomplete.

The Grassmannian now has its natural probability measure, constructed from Haar
measure on the orthogonal group. Lean verifies that it is independent of the
initial plane and is the unique rotation-invariant probability measure. The
flag integration identity is now proved in orthogonal frame coordinates.

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
displacement comparison and arclength factor are also proved.
`SphericalBound.lean` now proves the full geometric estimate with the same
exponents, using volume-preserving coordinates, the cone formula for
sphere measure, and a finite cover by bounded slope caps. Borel measurability
of the geometric direction norm and its exact conversion to a Haar-frame
norm are also proved. `Induction/XRayStep.lean` now proves the
one-dimensional plate induction step, including its volume normalization
and a constant independent of plate thickness. Power inequalities now
extend both plate and X-ray estimates to larger exponent scales, and
`Induction/DiagonalStep` gives the compatible diagonal step. The zero-plane
seed, exponent selection, and full finite induction are now proved in
`Induction/Seed`, `XRayExponents`, `Lift`, and `Iteration`. After `j` lifts
in codimension `c`, the deficit is `c/ρ^j` for any fixed
`2 < ρ < criticalExponent`. The target range therefore supplies a deficit
below one in dimension `n-1`. `Induction/Globalization` extends these local
plate estimates to all Borel nonnegative inputs for `0 < δ ≤ 1`, with the
same deficit and only an extra factor `3^(n/p)`. The signed Fourier-slice
identity, Schwartz regularity of line integrals, and exact averaged
inverse-radius Fourier weight are now proved. `XRay/AveragedFourier` gives
the joint `L²` bound with decay `R^(-1/2)` for a Fourier gap of radius `R`,
with a finite constant. The smoothed `L²` and fixed-support `L∞` endpoints
are now proved uniformly under normalized kernel dilation. Smooth amplitude
decomposition and layer-cake integration prove the full interpolation theorem
within the Schwartz domain. `XRay/SmoothedDecay` consequently gives the
uniform frequency gain `a^(-1/p)` for every finite `p ≥ 2` on fixed bounded
support. Projected-kernel decay and bounded-translation estimates now control
the spatial tails. `XRay/WeightedDecay` retains the same frequency gain after
multiplication by any polynomial weight `(1 + ‖x‖²)^A`, for `a ≥ 1`.
`XRay/LowFrequency` proves the corresponding weighted bound for every fixed
Schwartz kernel and finite `p ≥ 1`, without a Fourier-gap hypothesis.
The smooth low-frequency kernel and its annular differences are now constructed.
Their finite dyadic sums telescope exactly, and the smoothed approximations
converge uniformly to every Schwartz input, with Fourier error tending to zero
in `L¹`. Polynomial weights preserve closed Fourier support, including on each
X-ray fiber. Uniform polynomial spatial decay now gives an integrable bound on
every full affine plane, so its signed integrals converge as well.
`Grassmannian/NormalLiftCoordinates` identifies intrinsic plane volume with
product volume, and `XRay/PlaneIntegral` proves signed Fubini in every rotated
flag frame, including arbitrary translations. `Fourier/BandlimitedPlane` now
proves the full comparison with local plate averages: if the Fourier support
lies in the ball of radius `aR`, the full absolute integral on every translated
`k`-plane is bounded by the thickness-`a⁻¹` plate maximum of
`(1 + ‖x‖²)^A f`, for `2A > k`. The constant is independent of scale, plane,
translation, and input. `Induction/TerminalDecay` now integrates the plate
and weighted X-ray estimates, giving `a^(-(1-α)/p)`. `TerminalSeries` sums
the dyadic majorants when `α < 1`, with joint measurability proved.
`TerminalPlane` assembles a measurable majorant for all signed affine-plane
integrals of Schwartz inputs supported in a fixed ball, with a uniform
`Lᵖ` bound. Smooth disk localization, passage to open indicators, and the
separate four-dimensional seed needed for `(5,2)` remain incomplete.

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
larger ratio above. Its projection estimate, quantitative selection, transfer
to spherical X-ray estimates, and finite plate induction now have Lean proofs.
The fixed-support Schwartz terminal estimate is proved; its passage to
arbitrary Besicovitch sets remains open.
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
