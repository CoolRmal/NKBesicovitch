# NKBesicovitch

A Lean 4 formalization of Hausdorff-dimension and positive-measure bounds for
**(n,k)-Besicovitch sets**,
built on [mathlib](https://github.com/leanprover-community/mathlib4).

The goal is to advance the **(n,k)-Besicovitch conjecture**: every measurable
set containing a unit k-disk in every direction should have positive volume
when `2 ≤ k < n`. The results below establish a range of cases and give
Hausdorff-dimension estimates beyond that range.

## The results

An **(n,k)-Besicovitch set** contains a translate of the closed unit
k-dimensional disk in every k-dimensional direction in Euclidean n-space.

For every `1 ≤ k ≤ n`, this project proves

$$
  \boxed{\dim_H E \ge n-\frac{n-k}{p_c^k}}.
$$

This Hausdorff-dimension bound requires no measurability or boundedness
assumption on the set. For ordinary **Kakeya sets**, where `k = 1`, it gives

$$
  \dim_H E \ge n-\frac{n-1}{p_c}
  \approx 0.596968283 \cdot n+0.403031717.
$$

The project also proves **positive volume** for Lebesgue measurable sets
whenever

$$
  n < p_c^{k-1}+k.
$$

Here $p_c$ is the unique root in $(2,3)$ of

$$
  p_c^3-2p_c^2-2p_c+2=0.
$$

Lean also proves the exact rational bounds

$$
  \boxed{2.481 < p_c < 2.482}.
$$

The approximation is $p_c\approx2.481194304$. Both theorems use the exact
root, so their statements do not depend on floating-point calculations.

## A brief history

For line segments (`k = 1`), Besicovitch constructions show that containing
every direction is compatible with zero volume. The Kakeya conjecture asks
whether such sets nevertheless have full Hausdorff dimension. For planes and
higher-dimensional disks (`k ≥ 2`), the conjectured conclusion is stronger:
positive volume. This is the conjecture pursued here. See
[Oberlin's introduction](https://arxiv.org/abs/math/0512377) for the connection
between the two problems.

- **Falconer (1980) and Bourgain (1991).** Falconer's plane-integral estimates
  establish positive measure when $k>n/2$. Bourgain's induction reaches the
  much wider range $n\le 2^{k-1}+k$. These results and their analytic mechanisms
  are described in [Oberlin's account](https://arxiv.org/abs/math/0512377).
- **Katz and Tao (2002).** Their arithmetic projection method gives a Kakeya
  Minkowski-dimension bound of $1+(n-1)/\beta_c$, where
  $\beta_c\approx1.675130871$ solves $\beta_c^3-4\beta_c+2=0$.
  They also prove the separate Hausdorff bound $(2-\sqrt{2})(n-4)+3$.
  See [*New bounds for Kakeya problems*, Theorem 1.1](https://arxiv.org/abs/math/0102135).
- **Oberlin (2006 preprint; published 2010).** Mixed-norm X-ray estimates and
  plane induction yield Hausdorff dimension at least
  $n-(n-k)/(1+\sqrt{2})^k$, and positive measure when
  $n<(1+\sqrt{2})^{k-1}+k$.
  See [*Two bounds for the X-ray transform*, Corollary 1.3 of the preprint](https://arxiv.org/abs/math/0610942).
- **Later developments.** Hickman, Rogers, and Zhang's polynomial-partitioning
  work improves Kakeya estimates in many dimensions. Its high-dimensional
  Hausdorff bounds retain the leading coefficient $2-\sqrt{2}$.
  See [their comparison in Section 9.2](https://arxiv.org/abs/1908.05589).

The cited Oberlin preprints formulate `(n,k)` sets using translates of entire
k-planes. This repository explicitly works with unit k-disks, so its
statements also apply when only a finite disk in each direction is present.

## What is new here?

**The claimed advance is to obtain the Katz–Tao numerical exponent for
Hausdorff dimension, and to improve Oberlin's displayed positive-measure
range.** The comparison is:

| Conclusion | Earlier result | This repository |
| --- | --- | --- |
| Kakeya Hausdorff dimension | $(2-\sqrt{2})(n-4)+3$ (Katz–Tao) | $n-(n-1)/p_c$ |
| (n,k) Hausdorff dimension | $n-(n-k)/(1+\sqrt{2})^k$ (Oberlin) | $n-(n-k)/p_c^k$ |
| Sufficient condition for positive volume | $n<(1+\sqrt{2})^{k-1}+k$ (Oberlin) | $n<p_c^{k-1}+k$ |

Here $p_c\approx2.481194304$ exceeds $1+\sqrt{2}\approx2.414213562$.
For Kakeya sets, the coefficient of $n$ increases from approximately
$0.585786$ to $0.596968$. This improves the cited Hausdorff bounds in
sufficiently high dimensions; stronger bounds exist in some lower dimensions.
The table compares these specific historical results, rather than claiming
an optimal bound for every `(n,k)`.

The numerical exponent itself already appears in Katz–Tao:
$\beta_c=p_c/(p_c-1)$ makes their Minkowski bound equal to $n-(n-1)/p_c$.
But **Hausdorff dimension is at most Minkowski dimension**, so their Minkowski
lower bound does not imply the Hausdorff lower bound proved here.

The additional analytic ingredient developed from the supplied September 2026
manuscript is a continuous projection estimate with joint measurable parameter
selection. The formalization carries this through mixed-norm X-ray estimates,
plate induction, and a countable-cover argument for Hausdorff dimension.
A Fourier argument then gives positive measure in the stated range.
This supplies the analytic estimates and geometric consequences in Lean,
including the measurability and uniformity needed to connect them.

**Novelty status:** these comparisons identify the mathematical improvement
claimed by the project. The formal statements are proved and mechanically
checked; independent mathematical review and confirmation of priority against
the full literature remain pending. The full (n,k)-Besicovitch conjecture
is beyond the range established here.

## Proof and verification status

**Both theorems and the exponent bounds are proved in Lean.** Their dependencies
use only Lean's standard axioms: `propext`, `Classical.choice`, and `Quot.sound`.
There are no `sorry`s in the proof library or `Solution.lean`.

- **Challenge:** `Challenge.lean` explicitly states all three targets. Its three
  deliberate `sorry`s are challenge placeholders.
- **Solution:** `Solution.lean` exposes both theorems and imports the
  completed proof of the exponent bounds.
- **Checks:** the full build and local Comparator checks pass. At submitted
  commit `33f0c94`, [Palomar's mechanical verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/34319928936)
  also passed for all three targets, including the sandboxed checks and replay
  through both Lean's kernel and the independent NanoDa kernel.

See the [Hausdorff verification report](verification/hausdorff-development.md)
for the earlier local checks. [formalization.yaml](formalization.yaml) records
provenance and review status. After mechanical verification, Palomar's
[rendering attempt](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/34356373507)
failed in its core-notation audit, matching the reported
[renderer issue #134](https://github.com/PalomarRegistry/PalomarSubmission/issues/134).
That rendering failure is separate from proof verification; the successful
mechanical check alone does not establish registration or mathematical novelty.

## How the proof fits together

1. **Projection estimates.** Prove the pair and corner arguments and a
   measurable selection theorem above the critical projection exponent
   $\beta_c=p_c/(p_c-1)\approx1.675130871$.
2. **X-ray estimates.** Turn those projection bounds into mixed-norm estimates
   for integration along lines.
3. **Dimension induction.** Use the X-ray estimates to improve bounds for
   maximal averages over thickened disks.
4. **Hausdorff dimension.** Group a countable ball cover by radius and sum
   the maximal estimates. Every exponent below `n - α` has positive
   Hausdorff measure when the plate estimate has deficit `α`.
5. **Fourier argument.** Sum the frequency estimates when the dimension
   condition gives a strictly positive decay margin.
6. **Positive measure.** Approximate open-set indicators and use outer
   regularity to reach Lebesgue measurable Besicovitch sets.

The library also constructs the rotation-invariant probability measure on
Grassmannians and proves the measurability and normalization facts used above.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build
```

The project pins Lean and mathlib to `v4.34.0-rc1`. The default build checks
the library, challenge, and solution.

## Where to look

| File or folder | Purpose |
| --- | --- |
| [Challenge.lean](Challenge.lean) | Read the precise statements |
| [Solution.lean](Solution.lean) | Public interface to the proved results |
| [Exponents.lean](NKBesicovitch/Exponents.lean) | Cubic root, numerical bounds, and exponent arithmetic |
| [Grassmannian/](NKBesicovitch/Grassmannian/) | Directions, rotations, and canonical probability measure |
| [Projection/](NKBesicovitch/Projection/) | Projection estimates and measurable selection |
| [Operators/](NKBesicovitch/Operators/) | X-ray, interpolation, and Fourier estimates |
| [Induction/](NKBesicovitch/Induction/) | Dimension induction and assembly of the general theorem |
| [Hausdorff/](NKBesicovitch/Hausdorff/) | Ball covers, maximal-estimate transfer, and the Hausdorff bound |
| [PositiveMeasure/](NKBesicovitch/PositiveMeasure/) | Passage from analytic estimates to positive volume |
| [PLAN.md](PLAN.md) | Detailed proof structure and source notes |
| [PROGRESS.md](PROGRESS.md) | Implementation and verification details |

Copyright 2026 Yongxi Lin. Released under the [Apache 2.0 license](LICENSE).
