# NKBesicovitch

A Lean 4 formalization of Hausdorff-dimension and positive-measure bounds for
**(n,k)-Besicovitch sets**,
built on [mathlib](https://github.com/leanprover-community/mathlib4).

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

## Proof and verification status

**Both theorems and the exponent bounds are proved in Lean.** Their dependencies
use only Lean's standard axioms: `propext`, `Classical.choice`, and `Quot.sound`.
There are no `sorry`s in the proof library or `Solution.lean`.

- **Challenge:** `Challenge.lean` explicitly states all three targets. Its three
  deliberate `sorry`s are challenge placeholders.
- **Solution:** `Solution.lean` exposes both theorems and imports the
  completed proof of the exponent bounds.
- **Checks:** the full build and a Comparator development run pass for all
  three targets, including statement comparison, axiom checks, and Lean kernel
  replay. Full Linux sandbox and independent-kernel verification remain pending.

See the [Hausdorff verification report](verification/hausdorff-development.md)
for the scope of these checks. [formalization.yaml](formalization.yaml) records
provenance and review status; final Palomar verification is still pending.

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

## Background and sources

The Besicovitch conjecture asks whether every measurable (n,k)-Besicovitch set
has positive volume for `2 ≤ k < n`. This project establishes the range above.

The proof follows the X-ray and maximal-operator induction developed in
Oberlin's [*Two bounds for the X-ray transform*](https://doi.org/10.1007/s00209-009-0589-5)
and [*Bounds for Kakeya-type maximal operators associated with k-planes*](https://arxiv.org/abs/math/0512377).
The September 2026 manuscript supplied by the project owner develops a
selectable continuous projection estimate at the exponent
$\beta_c=p_c/(p_c-1)$. The same numerical exponent already occurs in
[Katz–Tao's Minkowski bound](https://arxiv.org/abs/math/0102135).
Here the selectable estimate feeds mixed-norm bounds and the Hausdorff
and positive-measure consequences. Independent review of the claimed
improvement over published Hausdorff bounds is still pending.

Copyright 2026 Yongxi Lin. Released under the [Apache 2.0 license](LICENSE).
