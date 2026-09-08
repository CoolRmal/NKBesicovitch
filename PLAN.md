# Formalization plan

The goal is to prove both requested positive-measure theorems, with no extra
axioms and no `sorry` in their proof dependencies. This file records the initial
decomposition, not a claim that the analytic steps have been verified in Lean.

## Statements and conventions

The ambient space is `EuclideanSpace ℝ (Fin n)` with its Euclidean norm and
canonical Lebesgue volume. A set has the `(n,k)` disk property when, for every
`k`-dimensional real linear subspace `V`, some translate of the closed unit ball
of `V` lies in the set. Measurability is stated using `NullMeasurableSet E volume`,
which includes Lebesgue measurable sets beyond the Borel sets.

The two targets are:

1. For `1 ≤ k ≤ n` and `(n : ℝ) < p_c ^ (k - 1) + k`, every Lebesgue measurable
   set with this disk property has positive volume.
2. Every Lebesgue measurable set in dimension five with the two-disk property
   has positive volume.

The endpoints `k = n` are included and will be proved directly. Requiring `k ≤ n`
prevents vacuous quantification over nonexistent subspaces. Requiring `1 ≤ k`
also prevents truncated natural subtraction from changing the intended range.
Boundedness, compactness, a measurable choice of centers, and concentration
hypotheses will not be added to the final statements.

The exact constant is the unique root in `(2,3)` of

    p³ - 2p² - 2p + 2 = 0.

Equivalently, `p_c = β_c / (β_c - 1)`, where `β_c` is the root in `(1,2)` of
`β³ - 4β + 2 = 0`. The intended values are approximately `2.481194304` and
`1.675130871`. The definition by supremum of the roots in `[2,3]` must be
accompanied by proofs of existence, uniqueness, and strict interval bounds.
No numerical approximation replaces the exact constant in the challenge.

## Available sources and their status

Local reference PDFs are in `~/Downloads/(n,k)/`. Extracted text and earlier
research audits are in the existing, untracked `tmp/research/` directory. These
are reference material, not Lean proofs. The linked ChatGPT project requires
login through the web tool; its similarly named local folder is accessible but
currently empty. The research PDFs and drafts are accessible independently.

| Source | Relevant content | Status |
| --- | --- | --- |
| `Projection_Estimate_near_1.675_Readable_Rigorous_Proof.pdf` | Sections 3–12: pair/corner densities, stopping tree, selectable patterns; §13: exponent iteration | Supplied manuscript; explicitly says its new arguments are not independently certified |
| `corner_optimal_constant_proof.pdf` | Original pair/corner argument | Supplied manuscript |
| `projection_to_mixed_norm_xray_detailed.pdf` | Selectable projections to restricted and strong mixed norms; direction charts | Supplied derivation conditional on the projection estimate |
| `oberlin_xray_to_nk_besicovitch_notes.pdf` | X-ray to plane-maximal induction and positive measure | Supplied derivation, to check against the papers |
| Oberlin, *Two bounds for the X-ray transform*, Math. Z. 266 (2010), 623–644, DOI `10.1007/s00209-009-0589-5` | Theorem 3; mixed-norm conventions and recursion | Published source |
| Oberlin, *Bounds for Kakeya-type maximal operators associated with k-planes*, arXiv:math/0512377 | Fourier terminal step and plane maximal recursion | Published source; distinguish full planes from local disks |
| `output/pdf/positive-measure-five-two-proof.tex` | Four-dimensional seed, strongification, weighted Fourier step, global unit disks | Existing supplied draft; its cited inputs must also be proved in Lean |
| Guth–Zahl, arXiv:1701.07045, corrected version | Proposition 2.1, exponent `3 + 1/40`, concentration dependence | Published input, not available as a Lean axiom |
| Katz–Rogers, arXiv:1802.09094 | Theorem 1.1 verifies polynomial concentration for separated directions | Published input, not an additional set hypothesis |

The existing prose audits support specific arguments but cannot discharge any
Lean dependency. In particular, the new projection exponent is not attributed
to Oberlin as an already published theorem. The `(5,2)` target uses only the
`p = 4` consequence of its draft; stronger operator assertions in that draft
are unnecessary for the requested result.

## Dependency decomposition and implementation order

### 1. Minimal statement surface and arithmetic

`Challenge.lean` imports only Mathlib and declares the ambient space, disk
property, exact constant, and two theorem statements. `Solution.lean` declares
the same theorem names using the developed proofs, without importing Challenge.
Comparator must compare all non-Mathlib definitions used in the statements.

`NKBesicovitch/Basic.lean`: geometric definitions and the full-dimensional case.
`NKBesicovitch/Exponents.lean`: root existence, rational enclosures, uniqueness,
the fractional-linear change between β and p, and strict-margin selection.
`NKBesicovitch/Projection/Iteration.lean`: corner exponent update and convergence.
The strict input inequality must produce a finite iteration and a positive
epsilon budget; the projection endpoint itself is not asserted.

### 2. Grassmannian geometry and canonical measure

`Grassmannian/Basic.lean`: use the subtype of real submodules of dimension k;
topologize it by the orthogonal projection operator. Mathlib's existing
`Module.Grassmannian` uses locally free quotients and is not this analytic API.
Reuse Mathlib finite-dimensional subspaces, projections, and isometries.

`Grassmannian/Measure.lean`: normalized Haar measure on the orthogonal group,
pushforward through a fixed k-plane; prove independence of the plane, rotation
invariance, probability mass, and uniqueness. Construction must assume `k ≤ n`.
`Grassmannian/NormalLift.lean` and `FlagMeasure.lean`: adjoin a normal line
to a transverse plane and average in orthogonal frame coordinates. The
canonical Grassmannian pushforward and iterated integral identity are now
proved. `Geometry/SphereMeasure.lean` identifies the line marginal with
normalized Euclidean surface measure.
Check every `Measure.map` has a measurable map; its fallback value must never
supply an apparent estimate. Coordinate charts must have the right Jacobians.

### 3. Operators and interpolation

`Operators/Defs.lean`: local disks, thickened plates, nonnegative maximal averages,
and the chart X-ray integral. Use `ℝ≥0∞` integrals and suprema where appropriate
to avoid the zero value of a nonintegrable Bochner integral or an unbounded real
supremum. Plate radii must be positive when dividing by their volume, and the
volume must first be proved positive and finite.

`Operators/Interpolation.lean`: only the restricted-to-strong and mixed-norm
interpolation required by the two routes. Reuse Mathlib `eLpNorm`, layer-cake,
Tonelli, Hölder, and geometric series. State both exponent order and positivity.
`Operators/XRay/`: the local chart transform, measurability, localization,
and change to spherical directions and perpendicular intercepts.

### 4. Projection estimate near 1.675

All proof files for this input belong to `Projection/`:

* `Defs`: line families `(x,ξ)`, `π_t(x,ξ)=x+tξ`, Lebesgue family mass,
  essential parallel multiplicity, and quantitative selectable patterns.
* `TwoSlice`, `Parallel`: the exact determinant-based seed, its outer-measure
  bound, and multiplicity normalization facts. These estimates, both
  improvements, and finite-height existence at every strict exponent above
  the critical root are now proved, including full quantitative selection.
* `Pair`: changes of variables, pair incidence density, marginal identities,
  and pair improvement.
* `Corner`: three-line code, its two fiber bounds, and outer marginal identity.
* `Stopping`: density balancing, simultaneous child pruning, and the finite
  uniform/concentrated tree. Maintain the distinct original, pruned, and
  tested fiber sets throughout the proof.
* `Selection`: separated-time reservoirs, dual pairs, a common outer scalar,
  and polynomial lower bounds on the measure of admissible parameter tuples.
  The jointly Borel two-slice seed, dual-pair reservoir, common outer-scalar
  reservoir, and separated root and child triples are proved with explicit
  constants. The finite-coordinate scheme and its two-slice seed, joint
  one-node parameters, parameter-volume exponent `4 + (8 + 6L)A`, and
  uniform outer and inner input constants are proved. Whole-tree selection
  is jointly Borel with parameter-volume exponent `(4 + (8 + 6L)A) S_J`,
  where `S_J` counts nonterminal labeled nodes; selecting the root triple
  adds three. Measurable labeled heights lie in the original time set, and
  selected parameters realize analytic trees using only those heights.
  All tree coordinates have the same polynomial bound at every depth.
  The realization retains uniform geometric and input-estimate control.
  Inner and outer coefficients are one explicit monomial; their propagation
  through refinement and the stopping proof yields a polynomial stopping
  constant uniform over every selected tree with fixed balanced-mass
  coefficients. The finite label count now gives common balanced-mass
  coefficients, a polynomial stopping threshold, and an explicit bound
  covering both large and bounded projection sizes. The full selected-tree
  estimate has a uniform polynomial constant, preserved when restoring
  parallel multiplicity. The arrays are now reindexed into finite vectors
  by a volume-preserving measurable equivalence. `TreeScheme` assembles
  the selectable corner improvement, starting directly at the two-slice
  seed exponent `2`. `Selection/Main` proves existence of a selectable
  scheme at every `β > β_c` by the same numerical iteration principle
  used for finite-height estimates. No endpoint estimate is asserted.
* `Selection/CommonParameters` now finds one common parameter for a
  polynomial fraction of the line-family volume. `Operators/XRay/Basic`
  and `GoodTimes` provide joint line-time measurability and small-slice
  removal retaining half the time measure, including the zero-volume case.
  `Operators/XRay/Restricted` assembles the bound
  `r^K |F| ≤ C M(F)^(2-β) |E|^β`, with `K > 2` and uniform constants.
  `Localization` bounds intercepts uniformly for fixed support and slopes.
  `FiberBlocks` and `UniformFibers` now give the mixed-norm bound on every
  piece with comparable parallel-fiber sizes, independently of that size.
  `Operators/MixedNorm/` proves the indicator formula, both fiber-size
  bounds, and the countable triangle inequality using Mathlib's `eLpNorm`.
  `XRay/Indicator` now completes the double dyadic decomposition, geometric
  interpolation, and summation. It proves the full indicator estimate with
  input-volume exponent `βθ/Q` for every `0 < θ < 1`, uniformly on fixed
  bounded support and slopes. `InputBound`, `Normalized`, `Scaling`, and
  `Strong` now extend this to every Borel nonnegative extended-valued input
  with `p > Q/β`. The superlevel series treats infinite pointwise values,
  and homogeneity handles zero and infinite norms. `FullLineBound` now
  extends this to the full line integral on bounded support using unit
  interval translations and a finite cover. `TransverseMeasure` controls
  the perpendicular-displacement norm by the transverse intercept norm;
  `Arclength` supplies the exact factor from normalizing the direction.
  `NormalCoordinates` now identifies Euclidean coordinates while preserving
  volume. `DirectionMeasure` compares sphere measure with slope volume
  through the cone formula, and `DirectionCover` supplies a finite cap cover.
  `DirectionNorm`, `Spherical`, and `SphericalBound` now assemble the full
  spherical estimate with the same exponents. The finite-cover norm
  inequality needs no joint measurability hypothesis. `DirectionMeasurability`
  now proves Borel measurability for finite positive displacement exponents
  by descent from the orthogonal group, and identifies the frame norm with
  the spherical norm including the exact surface-area normalization.

Essential fiber bounds must be used almost everywhere or justified by removing
a null set of directions once. Projection images need not be Borel; use outer
measure or prove their completed measurability. Constants must be uniform over
the line family and over the admissible time-selection reservoir.

### 5. From maximal estimates to positive measure

`PositiveMeasure/FromMaximal.lean`: use outer regularity, not pointwise smooth
majorants of an arbitrary null set. A uniform open-superset lower bound yields
the desired lower bound for an arbitrary set, hence for measurable sets.

`PositiveMeasure/Approximation.lean`: increasing nonnegative compact smooth
approximations to open indicators, monotone convergence along disks, interchange
of suprema, and Fatou in direction space. Localize full-plane estimates using a
partition of unity to obtain a support-independent unit-disk bound.

`PositiveMeasure/Delta.lean`: thickened plate lower bounds on open supersets and
the zero-thickness limit. A bound with positive scale loss alone is insufficient
for positive measure; prove a uniform bound or use the Fourier terminal gain.
This folder owns the entire passage from delta maximal control to measure.

### 6. Bourgain–Oberlin induction

All induction files belong to `Induction/`:

* `MixedNorm`: selectable projections imply the necessary local X-ray bound.
  Integrate translations before directions; retain finite input exponent and
  a small exponent loss.
* `Step`: flag Fubini, Hölder on perpendicular fibers, and the exact recurrence
  for the plate loss and input/output exponents.
* `Fourier`: Plancherel and the line-transform Fourier identity with weight
  `|ξ|⁻¹` are proved in `XRay/FourierSlice`, `SchwartzLine`, `FourierFrame`,
  and `AveragedFourier`, using `Geometry/PolarIntegral` and
  `RotatedHyperplaneIntegral`. The joint `L²` estimate has the finite
  constant and decay `R^(-1/2)` for a Fourier gap of radius `R > 0`.
  `Fourier/Convolution` and `Dilation` now give the multiplier bound and
  exact normalized kernel scaling. `XRay/SmoothedBound` proves the uniform
  fixed-support `L∞` endpoint and the `L²` gain for these dilations.
  `Interpolation/SmoothAmplitude` and `EndpointTail` provide smooth amplitude
  splitting and the squared-tail distribution estimate. Layer-cake integration,
  a smooth frequency partition, and separate control of zero frequency remain.
* `Terminal`: polynomially weighted bandlimited fiber comparison, summable
  dyadic gain, and the local full-plane bound.
* `Range`: choose all strict margins, iterate from zero-dimensional disks
  to `(k-1)`-planes, apply the Fourier lift, and assemble the first theorem.

Current state: `PlateGeometry`, `PlateVolume`, and `PlateIntegral` prove
the normalized comparison with factor `2^m`, uniform over all positive
thicknesses. `Step` averages it using the flag law, and `XRayStep` applies
the proved spherical X-ray estimate. This gives the one-dimensional
step from input exponent `Q/(β-1)` to every exponent above `Q/β`, retaining
outer exponent `Q`. `PlatePower` and `XRay/ScaledBound` now increase the
exponent scales without changing the gain ratio. `DiagonalStep` applies
output Hölder and the flag argument to compatible diagonal estimates.
`Estimates` records the local diagonal deficit. `Seed` proves the initial
ambient-dimension loss, `XRayExponents` chooses a compatible scale at every
fixed subcritical ratio, and `Lift` divides the deficit by that ratio.
`Iteration` proves the full finite recurrence `c/ρ^j`. The requested strict
range now supplies a deficit below one in dimension `n-1` at finite input
exponent at least two. `Globalization` now extends every such local estimate
to arbitrary Borel nonnegative inputs for `0 < δ ≤ 1`. Translation covariance,
joint measurability of moving-ball maxima, and Tonelli give the explicit
factor `3^(n/p)` without changing the deficit. `Range` uses this global
estimate. The signed Fourier-slice identity and averaged Plancherel estimate
are now proved, including a finite constant for the half-derivative gain.
Both smoothed endpoints are uniform under normalized kernel dilation. Smooth
amplitude splitting now gives the distribution estimate for interpolation
while preserving the Schwartz input domain and its support constraint.
The remaining gap includes layer-cake integration of this tail estimate,
the frequency partition, weighted tails, bandlimited comparison with local
plate averages, and Fourier terminal assembly.

### 7. Independent `(5,2)` seed

`FiveTwo/PolynomialConcentration.lean`: formalize the needed Katz–Rogers result.
`FiveTwo/Shading.lean`: formalize corrected Guth–Zahl Proposition 2.1, including
the required polynomial partitioning, grains, and two-ends ingredients. Search
Mathlib before decomposing each source ingredient; none may be assumed.
`FiveTwo/Maximal.lean`: separated-direction covering, equal-density measurable
shadings, restricted weak estimate, and strongification at input exponent 4.
Choose `ε = η = 1/160`, giving loss `α = 79/80 < 1` and threshold `121/40 < 4`.
`FiveTwo/Main.lean`: terminal Fourier gain `2^(-j/320)`, sum over j, globalize to
unit disks, then apply `PositiveMeasure/FromMaximal`.

This is a substantial independent branch. Published theorem statements are
proof obligations, never custom axioms or user-facing hypotheses.

## Verification and checkpoints

Each step gets a compiling, accurately typed statement before its proof is
filled. Build dependencies incrementally. Keep files below 1500 lines, with
short named mathematical components instead of long monolithic proofs.
Commit and push completed checkpoints to the existing public GitHub repository.

Development builds may contain explicitly tracked `sorry`s. Completion requires:

* Both full targets proved with no `sorryAx` in their transitive dependencies.
* Challenge audited for geometric meaning, exact constant, measurability,
  dimensions, and endpoint behavior, independently of Solution.
* Comparator checks the theorem types and definition bodies with only
  `propext`, `Quot.sound`, and `Classical.choice` permitted, then kernel checks.
* `formalization.yaml` follows the upstream schema and honestly records all
  remaining gaps, provenance, AI assistance, and review status.
* README describes the conjecture, cited history, actual results and limitations;
  it must not claim novelty or completion from a compiling skeleton.

The source-to-Lean table is refined as analytic leaves are stated. A planned
module in this document is not an implemented API or a discharged dependency.
