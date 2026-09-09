# Formalization plan

The general critical-exponent positive-measure and Hausdorff-dimension theorems,
and the numerical exponent bounds, are proved in Lean, with no custom axioms or `sorry` in their
dependencies. This file records the proof structure and source conventions.
Final sandboxed Comparator and independent-kernel verification remain pending.

## Statements and conventions

The ambient space is `EuclideanSpace ℝ (Fin n)` with its Euclidean norm and
canonical Lebesgue volume. A set has the `(n,k)` disk property when, for every
`k`-dimensional real linear subspace `V`, some translate of the closed unit ball
of `V` lies in the set. Measurability is stated using `NullMeasurableSet E volume`,
which includes Lebesgue measurable sets beyond the Borel sets.

The targets are:

1. For `1 ≤ k ≤ n` and `(n : ℝ) < p_c ^ (k - 1) + k`, every Lebesgue measurable
   set with this disk property has positive volume.
2. The exact rational enclosure `2.481 < p_c < 2.482`.
3. For `1 ≤ k ≤ n`, every set with the disk property has Hausdorff dimension
   at least `n - (n-k)/p_c^k`, without a measurability or boundedness hypothesis.

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

The existing prose audits support specific arguments but cannot discharge any
Lean dependency. In particular, the new projection exponent is not attributed
to Oberlin as an already published theorem.

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
  Smooth amplitude splitting, the squared-tail distribution estimate, and
  weighted layer-cake integration now prove full interpolation in
  `Interpolation/Schwartz`. `XRay/SmoothedDecay` gives the uniform frequency
  gain `a^(-1/p)` on fixed bounded support for every finite `p ≥ 2`.
  Projected-kernel decay, bounded translations, and convolution transfer now
  prove rapid spatial tails. `XRay/WeightedDecay` retains this gain with
  every polynomial weight `(1 + |x|²)^A` for `a ≥ 1`. `LowFrequency` proves
  the weighted fixed-kernel bound for finite `p ≥ 1` without a Fourier gap.
  `Fourier/FrequencyKernels` now constructs the smooth cutoff and its annular
  difference, including the Fourier gap and outer frequency radius.
  `DyadicDecomposition` proves the exact finite telescoping identities.
  `DyadicConvergence` proves Fourier-error convergence in `L¹` and uniform
  convergence of the smooth approximations. `ConvolutionDecay` now proves
  polynomial spatial decay uniformly over all dilation scales at least one.
  `PlaneConvergence` constructs an integrable majorant on every affine plane
  and proves convergence of its full signed integrals by dominated convergence.
  `Grassmannian/NormalLiftCoordinates` identifies lifted intrinsic plane
  volume with product volume. `XRay/PlaneIntegral` proves signed full-plane
  Fubini in every rotated flag frame, with arbitrary translations.
* `Terminal`: `Fourier/BandlimitedPlane` now proves the weighted bandlimited
  comparison uniformly over all positive scales, directions, and translations.
  It uses a reproducing kernel and a positive weighted plane kernel. Averaging
  translated plates replaces the discrete covering in the supplied proof:
  unit tangential shifts are absorbed by the plane weight, thickness-sized
  shifts by the smoothing profile, and Tonelli controls the pairing by the
  plate maximum times the kernel mass. The mass is independent of scale and
  bounded uniformly in direction and translation. The weight condition is
  exactly `2A > k`, and no compact-support hypothesis is imposed here.
  Joint continuity of signed X-ray integrals and proper descent of plate
  maxima now give jointly Borel majorants in frame and lower-plane direction.
  `TerminalDecay` integrates the global plate estimate and weighted X-ray
  bound, obtaining `a^(-(1-α)/p)`. `TerminalSeries` sums all dyadic scales
  and the low-frequency term. Signed dyadic decomposition and flag Fubini
  yield `HasPlateEstimate.exists_affinePlane_majorant` in `TerminalPlane`, with a uniform joint
  norm for Schwartz inputs supported in any fixed ball. Remaining steps:
  use positivity to bound smooth disk inputs, localize them smoothly to
  remove support dependence, and pass monotonically to finite-measure
  open indicators. The measurable majorants control the disk operator
  directly without introducing a full-plane maximal operator.
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
factor `3^(n/p)` without changing the deficit. This global estimate feeds
the terminal argument used by `Range`. The signed Fourier-slice identity and averaged Plancherel estimate
are now proved, including a finite constant for the half-derivative gain.
Both smoothed endpoints are uniform under normalized kernel dilation. Smooth
amplitude splitting and weighted layer-cake integration now prove interpolation
while preserving the Schwartz domain and support constraint. Signed integration
is linear on this domain, and `SmoothedDecay` supplies the uniform gain
`a^(-1/p)` for every finite `p ≥ 2`. Normalized dilation and bounded
translations preserve uniform projected-kernel decay. Absolute convolution
bounds transfer it to the smoothed input, giving arbitrarily rapid frequency
and spatial tails outside the support ball. The weighted joint norm now
retains `a^(-1/p)` for every polynomial transverse weight. A fixed smoothing
kernel also has a weighted bound at every finite `p ≥ 1`, covering the
low-frequency piece without a gap at the origin. Smooth low-frequency and
annular kernels, the finite dyadic identities, Fourier-error convergence in
`L¹`, and uniform convergence of the approximations are now proved.
`Fourier/PolynomialSupport` proves that polynomial weights preserve closed
Fourier support, and `XRay/Bandlimited` gives weighted Schwartz fibers with
the original frequency radius. Uniform spatial decay now justifies convergence
through integrals over entire affine planes. Orthogonal product coordinates
and Schwartz integrability also give signed full-plane flag Fubini, including
all translations and rotations. The weighted bandlimited comparison with
local plate averages is now proved by positive-kernel translation averaging.
Joint measurability, integration of the weighted frequency gain, geometric
summation, and signed dyadic decomposition now assemble the Schwartz
terminal bound with a fixed support radius. `TerminalDisk` now proves its
positive disk consequence. A nonnegative smooth bump equal to one on the
radius-two ball and supported in the radius-three ball gives localization
within the Schwartz domain. Averaging translates removes dependence on
support. `SmoothApproximation` approximates each open indicator pointwise
by dominated positive Schwartz inputs. Bounded disk convergence and Fatou
pass the global estimate to open indicators. `TerminalPositiveMeasure`
applies outer regularity, and `Range` now proves the full general target.
The complete dependency chain passes the standard-axiom audit.

## Verification and checkpoints

Each step gets a compiling, accurately typed statement before its proof is
filled. Build dependencies incrementally. Keep files below 1500 lines, with
short named mathematical components instead of long monolithic proofs.
Commit and push completed checkpoints to the existing public GitHub repository.

Development builds may contain explicitly tracked `sorry`s. Completion requires:

* All three targets proved with no `sorryAx` in their transitive dependencies.
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
# Hausdorff-dimension extension (proved)

The new proved target is `le_dimH_of_isBesicovitch`, explicitly stated in
`Challenge.lean`: every `(n,k)`-Besicovitch set with `1 ≤ k ≤ n` has
Hausdorff dimension at least `n - (n-k)/criticalExponent^k`. No measurability
or boundedness assumption on the set is needed for the covering argument.
The independent positive-measure problem for `(5,2)` remains out of scope.

For each strict exponent `s < n-α`, a zero Hausdorff measure assumption
provides countable ball covers with arbitrarily small total `s`-cost.
Group the balls into dyadic radius classes. Thicken each group by its scale.
Intrinsic disk integration and orthogonal product coordinates bound the
amount of the disk covered by each group by a constant times its plate
maximal function. The global plate estimate bounds its direction-space
norm by its covering cost to the power `1/p` times
`δ^((n-s-α)/p)`. The positive exponent makes the sum over scales finite.
Countable subadditivity along every disk and the triangle inequality in
direction space then contradict an arbitrarily small covering cost.
Thus `dimH E ≥ n-α`. Apply finite deficit iteration with
`α=(n-k)/ρ^k` and let `ρ` approach `criticalExponent` from below.
The full-dimensional case follows from its positive volume.

Completed components: small Hausdorff ball covers; orthogonal disk-to-plate
comparison; dyadic group volume and norm estimates; Hausdorff transfer;
critical-exponent limit and public solution interface. All nine modules in
`Hausdorff/` compile without placeholders. The full build passes, and both
the reusable transfer and the final target use only standard Lean axioms.
Comparator's macOS development run accepted all three targets, including
fixed-definition comparison and fresh Lean kernel replay.
Independent mathematical review and novelty assessment remain pending.
