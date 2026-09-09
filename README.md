# NKBesicovitch

A Lean 4 formalization of a positive-measure result for **(n,k)-Besicovitch sets**,
built on [mathlib](https://github.com/leanprover-community/mathlib4).

## The result

An **(n,k)-Besicovitch set** contains a translate of the closed unit
k-dimensional disk in every k-dimensional direction in Euclidean n-space.

For integers `1 ≤ k ≤ n`, this project proves that every Lebesgue measurable
set with this property has **positive volume** whenever

$$
  n < p_c^{\,k-1}+k.
$$

Here $p_c$ is the unique root in $(2,3)$ of

$$
  p_c^3-2p_c^2-2p_c+2=0.
$$

Lean also proves the exact rational bounds

$$
  \boxed{2.481 < p_c < 2.482}.
$$

The approximation is $p_c\approx2.481194304$. The theorem uses the exact
root, so its statement does not depend on floating-point calculations.

## Proof and verification status

**The theorem and exponent bounds are proved in Lean.** Their dependencies
use only Lean's standard axioms: `propext`, `Classical.choice`, and `Quot.sound`.
There are no `sorry`s in the proof library or `Solution.lean`.

- **Challenge:** `Challenge.lean` contains minimal definitions and the two
  theorem statements. Its two deliberate `sorry`s are the challenge placeholders.
- **Solution:** `Solution.lean` exposes the general theorem and imports the
  completed proof of the exponent bounds.
- **Comparator:** a development run checked both statements, fixed definitions,
  permitted axioms, and replayed the proofs in Lean. Full Linux sandbox and
  independent-kernel verification remain pending.

See the [verification report](verification/critical-range-development.md) for
the precise scope of that run. [formalization.yaml](formalization.yaml) records
provenance and review status; final Palomar verification is still pending.

## How the proof fits together

1. **Projection estimates.** Prove the pair and corner arguments and a
   measurable selection theorem above the critical projection exponent
   $\beta_c=p_c/(p_c-1)\approx1.675130871$.
2. **X-ray estimates.** Turn those projection bounds into mixed-norm estimates
   for integration along lines.
3. **Dimension induction.** Use the X-ray estimates to improve bounds for
   maximal averages over thickened disks.
4. **Fourier argument.** Sum the frequency estimates when the dimension
   condition gives a strictly positive decay margin.
5. **Positive measure.** Approximate open-set indicators and use outer
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
| [PositiveMeasure/](NKBesicovitch/PositiveMeasure/) | Passage from analytic estimates to positive volume |
| [PLAN.md](PLAN.md) | Detailed proof structure and source notes |
| [PROGRESS.md](PROGRESS.md) | Implementation and verification details |

## Background and sources

The Besicovitch conjecture asks whether every measurable (n,k)-Besicovitch set
has positive volume for `2 ≤ k < n`. This project establishes the range above.

The proof follows the X-ray and maximal-operator induction developed in
Oberlin's [*Two bounds for the X-ray transform*](https://doi.org/10.1007/s00209-009-0589-5)
and [*Bounds for Kakeya-type maximal operators associated with k-planes*](https://arxiv.org/abs/math/0512377).
The sharper projection exponent comes from the September 2026 manuscript
supplied by the project owner. This repository provides a Lean verification
of that projection argument and its positive-measure consequence.

Copyright 2026 Yongxi Lin. Released under the [Apache 2.0 license](LICENSE).
