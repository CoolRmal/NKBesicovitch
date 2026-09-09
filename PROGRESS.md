# Formalization status

The project contains the general critical-exponent positive-measure result,
the Hausdorff-dimension lower bound, and the exact numerical exponent bounds.
The independent positive-measure problem for `(5,2)` remains removed.

## Completed target proofs

- `NKBesicovitch.criticalExponent_bounds` proves the exact rational enclosure
  `2.481 < criticalExponent < 2.482`.
- `NKBesicovitch.volume_pos_of_criticalExponent` proves positive volume for
  Lebesgue measurable `(n,k)`-Besicovitch sets when `1 ≤ k ≤ n` and
  `n < criticalExponent^(k-1) + k`.
- `NKBesicovitch.le_dimH_of_isBesicovitch` proves
  `dimH E ≥ n - (n-k)/criticalExponent^k` for every `1 ≤ k ≤ n`, with no
  measurability, boundedness, or measurable-center hypothesis.

All three statements are exposed by `Solution.lean`. Their proofs use only
`propext`, `Classical.choice`, and `Quot.sound`. `Challenge.lean` imports only
Mathlib and retains three deliberate proof placeholders for these statements.

## Main components

| Component | Completed work |
| --- | --- |
| Exponents | Root existence and uniqueness, exact rational bounds, projection exponent, and strict parameter margins |
| Grassmannians | Compact direction topology, orthogonal actions, transitivity, canonical probability, uniqueness, and flag integration |
| Projection estimates | Pair and corner inequalities, finite stopping trees, exponent improvement, and measurable simultaneous selection |
| Mixed-norm X-ray estimates | Restricted estimates, dyadic decomposition, strong interpolation, direction charts, and spherical transfer |
| Plate induction | Normalized plate bounds, compatible exponents, dimension lifting, finite iteration, and globalization |
| Hausdorff dimension | Small ball covers, orthogonal disk-to-plate comparison, scale costs, countable norm summation, deficit-to-dimension transfer, and the critical limit |
| Fourier estimates | Signed Fourier slicing, averaged Plancherel, smoothing, frequency decay, weighted kernels, and dyadic summation |
| Terminal argument | Uniform affine-plane bounds, disk normalization, smooth localization, approximation of open indicators, and outer regularity |

See [PLAN.md](PLAN.md) for the detailed decomposition and
[formalization.yaml](formalization.yaml) for source provenance.

## Verification

The implementation has no `sorry` declarations or custom axioms. Every library
module is imported by `NKBesicovitch.lean`; all files remain below the requested
1500-line limit.

The full default build passed with 3464 jobs. The only
warnings are the three intentional Challenge placeholders. The library has 327
modules, and its largest file has 160 lines. The metadata validates against
the upstream `formalization.yaml` schema.

The numerical bounds and general theorem passed a Comparator development run
at revision `8685c60b049dddf0e504251638f1cc0822508ec7`. That run compared the
fixed definitions, audited permitted axioms, and replayed the proof exports
in Lean. It did not provide Linux sandbox isolation or independent-kernel
verification. See [the report](verification/critical-range-development.md).

The current `comparator.json` targets the numerical bounds and both geometric theorems,
with nanoda enabled and no permission for `sorryAx`. Final sandboxed Comparator
and independent-kernel verification of the current revision remain pending.
The project is not yet ready for Palomar submission.

A fresh macOS Comparator development run on 2026-09-09 accepted all three
current targets, compared their fixed definitions, and replayed the exported
proofs in Lean. The new Hausdorff target and reusable transfer also passed
individual axiom audits. See [the Hausdorff report](verification/hausdorff-development.md).
This development run used no Linux sandbox or independent kernel.

Local `tmp/` and `output/` research materials are outside the formalization and
remain untracked.
