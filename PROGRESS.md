# Verified progress and remaining proof frontier

This is an implementation ledger. `PLAN.md` retains the complete objective and
source decomposition. The final theorems are not proved yet.

## Completed foundations

* `Fourier/PolynomialSupport` proves that coordinate multiplication, and
  hence every weight `(1 + ‖x‖²)^A`, preserves closed Fourier support.
  The proof uses Mathlib's Fourier differentiation identity, support
  locality of derivatives, and an orthonormal expansion of the squared norm.
  `XRay/Bandlimited` gives a weighted Schwartz representative on each
  transverse fiber with the original ambient frequency radius.
* `Fourier/FrequencyKernels` constructs a Schwartz kernel whose Fourier
  transform equals one on the unit ball, vanishes outside radius two, and
  has norm at most one. Its annular difference has a unit Fourier gap and
  vanishes at norm at least four. Dilation gives the corresponding support
  radii at every positive frequency scale.
* `Fourier/DyadicDecomposition` proves exact finite telescoping for the
  kernels and their convolutions. `DyadicConvergence` proves eventual
  equality at each fixed Fourier frequency, convergence of the Fourier
  error in the one-norm, and uniform convergence of the approximations on
  the whole ambient space. Convergence through unbounded plane integrals
  is not inferred from uniform convergence and remains a separate obligation.
* `XRay/FrameDilation` gives exact line-integral scaling. `KernelDecay`
  separates integrable line-parameter decay from arbitrary transverse
  decay, uniformly over rotations. `KernelTranslation` and `KernelTail`
  control bounded ambient translations and retain arbitrary frequency
  decay at distant transverse points. `ConvolutionBound` and `SmoothedTail`
  transfer these estimates to the signed smoothed transform, with the
  input entering through its one-norm.
* `PolynomialWeight` proves integrability of the spatial decay profiles.
  `XRay/WeightedTail` gives a global majorant for the polynomially weighted
  transform; `WeightedNorm` integrates it to an unweighted norm plus a
  rapidly decaying one-norm term. `WeightedDecay` combines this with
  interpolation and support-restricted Holder to retain `a^(-1/p)` for
  every weight `(1 + ‖x‖²)^A`, finite `p ≥ 2`, and `a ≥ 1`.
* `Fourier/BandlimitedPlane` proves that the full absolute integral of a
  bandlimited Schwartz function on any affine `k`-plane is bounded by the
  thickness-`a⁻¹` plate maximum of its polynomially weighted absolute value,
  when the Fourier radius is `aR` and `2A > k`. The constant is independent
  of positive scale, direction, translation, and input. `ReproducingKernel`
  proves exact reproduction and a positive polynomial convolution bound.
  `PlaneKernel`, `PlaneKernelMass`, and `PlaneKernelPairing` establish the
  weighted kernel, its uniform mass, and the Tonelli pairing identity.
  `TranslatedAverages` and `PlateKernelBound` control that pairing by plate
  averages, using bounded kernel variation under plate-sized shifts.
* `Fourier/ConvolutionDecay` proves spatial polynomial decay of the smooth
  approximations uniformly over all dilation scales at least one.
  `PlaneConvergence` supplies an integrable majorant on every affine plane
  and proves convergence of the full signed plane integrals.
  `Grassmannian/NormalLiftCoordinates` identifies intrinsic volume on lifted
  planes with the product of lower-plane volume and arclength.
  `XRay/PlaneIntegral` proves signed Fubini in all rotated flag frames and
  for arbitrary translations. Schwartz integrability justifies the iterated
  integrals before any absolute value is taken.
* `XRay/LowFrequency` proves a joint `L¹`-to-`Lᵖ` bound for fixed smoothing
  on bounded support and the polynomially weighted `Lᵖ` bound for every
  finite `p ≥ 1`. No Fourier-gap assumption is used, so this supplies the
  low-frequency estimate needed by the terminal argument.
* `Fourier/Convolution` proves the `L²` multiplier bound for Schwartz
  convolution. `Dilation` proves that normalized kernel dilation preserves
  the one-norm and rescales the Fourier transform by the reciprocal factor.
  `XRay/ConvolutionBound` bounds signed smoothed line integrals uniformly by
  support radius, input bound, and kernel mass. `SmoothedBound` combines
  these into uniform `L²` and `L∞` endpoints for a dilated kernel with a
  Fourier gap: the former gains `a^(-1/2)`, while the latter has no scale loss.
* `Interpolation/SmoothAmplitude` splits a compactly supported Schwartz
  input at every positive amplitude threshold into two Schwartz functions
  with no increase in spatial support. `EndpointTail` combines this with
  the endpoint bounds and Chebyshev to control output superlevel measure
  by the squared input tail. `TailIntegral` evaluates that tail by applying
  layer-cake to the measure weighted by `‖f‖²`. `TailBound` and `Schwartz`
  now prove the full `Lᵖ` interpolation theorem for `p > 2`, with a finite
  constant and two-norm dependence `A^(2/p)`. All endpoint applications
  stay inside their proved Schwartz domain with its support constraint.
* `XRay/SchwartzLine` now proves integrability on every normal line, and
  `FourierFrame` bundles signed line integration as a complex linear map.
  `SmoothedDecay` applies the interpolation theorem to normalized kernel
  dilations and proves joint `Lᵖ` decay `a^(-1/p)` for every finite `p ≥ 2`.
  The constant is finite and uniform over all `a > 0` and all Schwartz
  inputs supported in the fixed ball. The `p = 2` endpoint is included
  using the averaged Plancherel bound directly.
* `XRay/FourierSlice` proves the signed Fourier-slice identity for integrable
  complex inputs. `SchwartzLine` proves continuity, Schwartz regularity,
  and fiberwise Plancherel for signed line integrals. `FourierFrame` places
  them on one fixed displacement space and proves joint measurability.
* `Geometry/PolarIntegral` supplies nonnegative polar integration and the
  exact change in radial density under a one-dimensional drop.
  `RotatedHyperplaneIntegral` proves that Haar-averaged hyperplane volume
  is ambient volume weighted by inverse radius, with the ratio of sphere
  areas. Positive hyperplane dimension excludes the atomic zero-dimensional
  exception. `XRay/AveragedFourier` combines this with Plancherel and proves
  joint `L²` decay `R^(-1/2)` for Schwartz inputs whose Fourier transform
  vanishes on the radius-`R` ball. The constant is finite and independent
  of `R > 0`. Absolute values are taken after the signed line integral.
* `Induction/Globalization` extends a local diagonal plate estimate to all
  Borel nonnegative inputs, including unbounded support and infinite values,
  for `0 < δ ≤ 1`. Its extra factor is `3^(n/p)`, with no change to the
  thickness deficit. `PlateTranslation` proves exact covariance;
  `PlateLocalizationMeasurability` proves joint measurability in a Haar frame
  and ball center. `PlateLocalization` averages the localized maxima, and
  `BallLocalization` proves the exact Tonelli identity for the input norms.
  `Range` now obtains the global estimate before the Fourier terminal gap.
* `Induction/Estimates` records a local diagonal estimate with deficit `α`:
  its thickness factor is `δ^(-α/p)`, with a finite constant uniform over
  inputs in each fixed ball. `Seed` proves deficit `n` at every `p ≥ 1`
  by Hölder and ball-volume scaling, including the zero-plane seed.
  `Parameters` and `XRayExponents` choose compatible exponents at every
  fixed `2 < ρ < criticalExponent`, with displacement/input ratio exactly
  `ρ` and displacement exponent above any prescribed lower bound.
* `Induction/Lift` proves that one lift divides the deficit by `ρ`, with
  the new input exponent at least two. `Iteration` now proves the complete
  finite induction: in codimension `c > 0`, after `j` lifts the deficit is
  `c/ρ^j`. Every proper-dimensional case in the requested strict range
  consequently has a lower-dimensional plate estimate with a positive
  deficit below one. `Range` now obtains this proved estimate before its
  remaining Fourier terminal proof gap.
* `Operators/PlateMeasurability`: lower semicontinuity and Borel measurability
  now hold for every Borel nonnegative input, including infinite values.
  The moving open-plate indicator supplies the semicontinuity; the input
  itself need not be continuous. `Geometry/Plates` contains the shared
  positive finite volume facts formerly in `PositiveMeasure/Delta`.
* `Operators/PlatePower`: normalized Hölder gives `(M f)^t ≤ M (f^t)`
  for every `t ≥ 1`. A local plate estimate at `(p,q)` therefore extends
  to `(tp,tq)` with the constant raised to `1/t`, preserving the deficit.
  `XRay/Power` proves the analogous spherical norm inequality using the
  exact arclength support interval `[-R,R]`. `XRay/ScaledBound` applies
  it to the proved projection-derived estimate at every common larger
  exponent scale. `Induction/DiagonalStep` combines the plate extension,
  output Hölder on direction probability spaces, and flag integration
  into a diagonal induction step with explicit compatible exponents.
* `Induction/PlateGeometry`, `PlateVolume`, `PlateIntegral`: projection
  places a lifted plate inside the cylinder over the lower-dimensional
  plate. A half-scale lower plate times a unit-length interval gives
  the uniform volume comparison. The resulting normalized maximal
  comparison has factor `2^m`, independent of the plane, centers, and
  positive thickness. `Operators/PlateRotation` proves exact covariance.
* `Operators/XRay/Frame`: frame transforms are Borel and preserve the
  fixed-radius support ball uniformly over rotations. Their displacement
  norms equal the geometric X-ray norms. `MixedNorm/MapProd` supplies the
  upper norm inequalities without measurability assumptions on plate
  suprema. `Induction/Step` combines the lower-dimensional bound with flag
  integration. `XRayStep` now proves a one-dimensional induction step:
  for a suitable `Q > 2`, input exponent `Q/(β-1)` in the lower dimension
  becomes any exponent above `Q/β` in the higher dimension, with outer
  exponent `Q` and only a thickness-independent change in the constant.
* `Grassmannian/NormalLift`, `FlagMeasure`: adjoining a unit normal line
  to a transverse plane preserves the required dimension and is continuous.
  An independent Haar rotation and lower-dimensional Grassmannian plane
  give the canonical higher-dimensional plane probability. The resulting
  iterated integral identity supplies flag integration in frame coordinates.
* `Geometry/SphereRotations`, `SphereMeasure`: the orthogonal action on
  unit directions is continuous and transitive. The cone formula proves
  invariance of sphere measure, and uniqueness identifies a Haar orbit
  with normalized Euclidean surface measure. `NormalIsometry` transports
  perpendicular displacement spaces. `XRay/DirectionMeasurability` proves
  rotation covariance and Borel measurability of the direction norm for
  finite positive displacement exponents, then identifies its Haar-frame
  norm with the spherical norm, including the surface-area factor.
* `Operators/XRay/SphericalBound`: the strong bound is now proved for the
  geometric X-ray transform, with arclength along lines, Lebesgue measure
  on perpendicular displacement hyperplanes, and Euclidean surface
  measure on the sphere. It has the same exponents as the model estimate
  and a constant uniform over all Borel inputs on fixed bounded support.
  `Geometry/NormalCoordinates` supplies volume-preserving orthonormal
  coordinates. `DirectionChart`, `DirectionMeasure`, and `DirectionCover`
  give hemisphere parametrizations, the sphere-measure comparison via
  cones, and a finite cover by caps with bounded slopes. `DirectionNorm`
  and `Spherical` assemble the local comparisons. `MixedNorm/FiniteCover`
  sums the cap norms without an extra joint measurability assumption.
* `Operators/XRay/FullLineBound`: the strong mixed-norm bound now holds
  for the full line integral `chartXRay`, with the same exponents, on any
  fixed bounded support and bounded Borel slope set. `TimeTranslation`
  preserves the input and output norms when moving a unit interval;
  `FullLine` obtains a finite interval cover of the vertical support.
* `Operators/XRay/Transverse`, `TransverseMeasure`: when the normal vectors
  have nonzero inner product, projection between their normal hyperplanes
  is an invertible contraction and preserves each geometric line.
  `MixedNorm/VolumeComparison` uses Haar uniqueness and equal unit-ball
  volumes to prove that any linear contraction between isomorphic finite
  inner product spaces does not increase image volume. Consequently the
  perpendicular-displacement `L^r` norm is bounded by the transverse norm.
  `Arclength` proves the exact norm factor when normalizing a nonzero
  direction; nonnegative integrals may be infinite.
* `Operators/XRay/Strong`: for every `β_c < β ≤ 2`, there is a finite
  outer exponent `Q > 2` such that every `p > Q/β` gives
  `‖T f‖_(L^Q L^(Q/(β-1))) ≤ C ‖f‖_p`, uniformly over Borel nonnegative
  extended-valued inputs on a fixed bounded support and bounded Borel
  slope set. `InputDyadic` covers infinite pointwise values by a divergent
  large-level series. `NormalizedLevels` and `InputSeries` control the
  superlevel measures using the support and the normalized input norm.
  `XRay/InputSums`, `InputBound`, and `Normalized` transfer the indicator
  estimate to general normalized inputs. `Scaling` removes normalization,
  including zero and infinite norms, by an infimum over strict upper bounds.
* `Operators/XRay/Indicator`: for every `β_c < β ≤ 2`, there is a finite
  outer exponent `Q > 2` such that, for every `0 < θ < 1`,
  `‖T 1_E‖_(L^Q L^(Q/(β-1))) ≤ C |E|^(βθ/Q)` uniformly over Borel subsets
  of a fixed bounded support and a fixed bounded Borel slope set.
  `ValueDecomposition`, `FiberDecomposition`, and `DyadicDecomposition`
  reduce the transform to two countable halving scales, handling null
  fibers almost everywhere. `InterpolatedFibers` and `Interpolation/`
  introduce positive powers of both scales and sum the geometric series.
  The conclusion has no remaining restriction on the fiber measures.
* `Operators/MixedNorm/Basic`, `Fibers`, `Sums`: mixed norms are defined by
  iterating Mathlib's `eLpNorm`, first in intercepts and then in directions.
  Fiber norms are measurable; the indicator formula, lower-gap and upper
  fiber-size estimates, finite triangle inequality, monotone convergence,
  and countable triangle inequality are proved. Infinite norms are allowed.
* `Operators/XRay/FiberBlocks`, `UniformFibers`: restricting to directions
  with fiber measure in `(a/2,a]` gives a Borel family with multiplicity at
  most `a` and an explicit gap for every nonzero fiber. The restricted
  estimate gives a mixed-norm bound uniform over all `a > 0`, with outer
  exponent `K > 2` and inner exponent `K/(β-1)`. Fiber-size powers cancel
  exactly; zero-volume families are included.
* `Projection/Selection/ParameterBox`, `CommonParameters`: all time-set
  selections with measure at least `r` lie in a common finite box of known
  volume. Tonelli and averaging produce one parameter retaining at least
  `(c/(2C)^D) r^(A+BD)` of the line-family volume. The result also covers
  families of volume zero.
* `Operators/XRay/SelectedFamily`, `RestrictedSelection`, `SelectionLosses`,
  `Restricted`: common good-time selection gives the full restricted bound
  `r^K |F| ≤ C M(F)^(2-β) |E|^β` for every `β_c < β ≤ 2`, some integer
  `K > 2`, every finite-volume Borel spatial set, and every bounded Borel
  family of lines with transform at least `0 < r ≤ 1`. The constants are
  independent of both sets and `r`; no positive-volume assumption is used.
* `Operators/XRay/Localization`: rich-line sets are Borel, and bounded
  support and slopes force their intercepts into one fixed ball uniformly
  over every Borel subset of the support and every positive threshold.
* `Operators/XRay/Basic`, `GoodTimes`: the local indicator transform equals
  the measure of its jointly Borel line-time set. Removing spatial slices
  larger than `2|E|/r` leaves at least `r/2` good times on every line with
  transform at least `r`. The good-time sets are jointly Borel, their
  projections lie in the required small spatial slices, and the theorem
  includes ambient sets of volume zero without an extra positivity
  assumption. The general nonnegative local transform is Borel for Borel
  input functions.
* `Projection/Selection/Main`: every exponent strictly above
  `projectionExponent ≈ 1.675130871` admits a selectable projection scheme
  in every positive slope dimension. The scheme works in every
  positive-measure Borel subset of `[0,1]`, with joint measurability and
  polynomial bounds on parameter volume, coordinates, and the full
  projection constant. `RootCoordinates` and `FiniteTreeParameters`
  reindex the root and tree into finite vectors while preserving volume
  and bounds; `TreeScheme` assembles the selectable corner improvement.
  `IterationPrinciple` supplies the common numerical approximation
  argument for both selectable schemes and finite-height estimates.

* `Projection/Selection/Scheme`, `SeedScheme`, `SchemeBounds`: a finite-coordinate
  scheme interface records measurable labeled heights, joint selection,
  polynomial parameter volume, coordinate bounds, and an explicit uniform
  projection constant. The two-slice scheme is constructed in every positive
  slope dimension. The bounds can be applied using any positive lower bound
  on the time-set measure.
* `Projection/Selection/NodeParameters`, `NodeGeometry`: the jointly Borel
  parameter set for one corner node contains a common scalar, one outer
  scheme parameter, and one inner scheme parameter for each outer label.
  Every labeled child triple remains separated in the original time set,
  including when distinct labels have the same numerical height.
* `Projection/Selection/NodeMass`, `NodePolynomial`, `NodeBounds`: finite
  product measure and Tonelli give a uniform parameter-volume lower bound
  with exponent `4 + (8 + 6L)A` for one node, where `L` is the input label
  count and `A` its selection-volume exponent. Outer and inner coordinate
  and input-estimate constants have explicit polynomial upper bounds.
* `Projection/Selection/SeparatedTriples`: triples with every pair separated
  by `|I|/100` have measure at least `|I|³/4`. Their selection is jointly
  Borel. An admissible inner time and its dual, together with the base
  height, form another such triple in the same original time set.
* `Projection/Selection/CornerScalar`, `CornerRelation`, `CornerRelationMass`:
  the inner-to-outer scalar conversion has the exact measure factor
  `|(u-a)/(u-c)|`, bounded below by `|I|/100` on separated outer times.
  Integrating the available inner scalar-set measure gives at least
  `δ|I|⁴/80000` of compatible outer time-scalar measure.
* `Projection/Selection/CornerOuterTimes`, `CornerReservoir`: selecting
  outer scalars with time fibers of measure at least
  `δ|I|⁷/320000000000` leaves a scalar set of measure at least
  `δ|I|³/160000`. The scalar absolute values lie between
  `δ(|I|/100)²` and `(100/|I|)³`; each outer time supplies an inner time
  fiber of measure at least `δ|I|⁵/8000000`. The scalar selection and
  outer and inner time relations are jointly Borel.
* `Projection/Selection/SeparatedPairs`, `SeparatedTimes`, `TwoSlice`:
  removing finitely many neighborhoods preserves an explicit amount of
  time measure. Pairs separated by `|I|/100` have measure at least `|I|²/2`
  and two-slice constant at most `(100/|I|)^m`. These selections are jointly
  Borel in measurable families of time sets and base heights.
* `Projection/Selection/DualPairs`, `DualScalar`, `DualScalarBounds`:
  the five required time separations preserve at least `|I|²/2` of pair
  measure. The second-time-to-scalar map has an explicit inverse and
  change-of-variables formula. Its absolute value lies between `δ|I|/100`
  and `(100/|I|)²`, and its absolute Jacobian is at least `δ|I|/100`.
* `Projection/Selection/DualRelation`, `DualTimes`, `DualReservoir`:
  Tonelli gives at least `δ|I|³/200` of admissible time-scalar measure.
  Removing scalars with time fibers smaller than `δ|I|⁵/8000000` leaves
  at least `δ|I|³/400` of that measure and a scalar set of measure at least
  `δ|I|²/400`. The retained scalar set and its time fibers are jointly Borel.
* `Exponents`: existence and uniqueness of the cubic root defining `p_c`;
  exact rational enclosure `2.481 < p_c < 2.482`; the projection exponent
  `β_c = p_c/(p_c-1)` and its cubic equation.
* `Induction/Parameters`: every strict target dimension inequality survives
  replacement of `p_c` by a smaller ratio, hence admits a projection exponent
  strictly above `β_c`. This avoids any endpoint assumption.
* `Geometry/Disks`: equivalence of the quantified disk predicate and disk
  containment; compactness of disks; positive volume in full dimension.
* `Grassmannian/Basic`: k-dimensional subspaces and the topology induced by
  their orthogonal projection operators; projection injectivity.
* `Grassmannian/Rotations`, `Action`, `Transitivity`, `Topology`, `Measure`:
  compact orthogonal group and normalized Haar measure; continuous and
  transitive action on directions; compact, Hausdorff, second-countable
  Grassmannian; canonical probability measure for `k ≤ n`. The measure is
  independent of the initial plane, gives positive mass to every nonempty
  open set, and is the unique rotation-invariant probability measure.
* `Operators`: extended-nonnegative disk and plate averages and a local X-ray
  transform. Disk averages of indicators containing the disk equal one.
* `Geometry/RigidMotions`, `Operators/Semicontinuity`, `PlateMeasurability`:
  rigid motions transport disks and plates and preserve volume; Fatou gives
  lower semicontinuity of nonnegative parameter integrals. The plate maximal
  operator on any open indicator is lower semicontinuous and hence Borel
  measurable on directions, even though the supremum ranges over all centers.
* `Projection`: line-family definitions, essential parallel multiplicity,
  the corner update formula and its fixed-point arithmetic. No geometric
  projection estimate is inferred just from this arithmetic.
* `Projection/TwoSlice`: the seed estimate with exact factor
  `|(t-s)^m|⁻¹`, via the two-position map's determinant and outer measure.
  Projection images need not be Borel sets. `Projection/Parallel` bounds
  parallel multiplicity by every projection size and identifies zero
  multiplicity with zero mass for measurable line families.
* `Projection/Incidence`, `PairMass`: intrinsic coordinates for pairs of lines
  meeting at a fixed height; the slice-multiplicity integral and exact pair-mass
  identity; the Cauchy–Schwarz lower bound for pair mass. Its division-free
  statement includes zero and infinite measures.
* `Projection/PairCode`: the dual-height code identity and explicit inverse
  parametrization of each first-line fiber, with nonzero denominators stated.
* `Projection/PairData`, `PairDensity`, `PairRefinement`: the exact Jacobian of
  the double-projection coordinates, measurable density, total and restricted
  mass identities, support and pointwise projection bounds, and the volume
  lost when removing pairs below a density threshold. No Borel assumption is
  imposed on the projection images themselves.
* `Projection/CodeCoordinates`, `CodeDensity`, `CodeMarginal`, `FiberProjection`:
  the code change of variables, measurable code density and its total mass,
  the exact pointwise marginal identity at dual heights, and the pair-fiber
  projection bound. The latter is proved for every code value with outer
  measure, in a form that avoids division by the density threshold.
* `Projection/FiberSelection`, `SimultaneousRefinement`, `PairSelection`:
  finite simultaneous density cutoffs lose at most the sum of their individual
  volume bounds. A half-mass budget retains half the pair mass. For positive
  finite original mass, one code fiber retains half its density and satisfies
  all the selected projection bounds simultaneously.
* `Projection/CodeSlices`, `CodeBound`: the exact upper bound for code density
  by parallel multiplicity times one projection size. The proof transports
  exceptional slopes through an invertible affine map, so it uses the
  essential supremum faithfully and holds for every code value.
* `Projection/BoundedFamilies`, `Estimates`, `PairWitness`: bounded line
  families have finite projection, multiplicity, and pair masses. The uniform
  projection-estimate predicate has its exponent-two seed, and the selected
  family satisfies all the finite numerical inequalities for pair amplification.
* `Projection/PairAlgebra`, `PairParameters`, `PairStep`, `PairImprovement`:
  the full basic pair improvement `β ↦ 2 - 1/(2β)` for bounded Borel families,
  including the uniform constant, positive threshold, zero-mass case, and
  all finite-mass checks. In particular, the exponent `7/4` holds on the five
  heights `{0, 1, 2, 3, 3/2}`. This does not yet establish the target exponent
  near `1.675`, which requires the stronger corner improvement.
* `Projection/CornerCoordinates`, `CornerCode`, `CornerInverse`, `CornerMeasure`:
  intrinsic three-line corner coordinates, the exact outer/inner code
  decomposition, the inverse reconstruction, and the two-factor Jacobian.
* `Projection/CornerDensity`, `CornerFiberBound`, `CornerParent`, `CornerParentBound`:
  measurable corner-code density with the correct total mass, a Borel positive
  first-line family, and both corner-fiber upper bounds. The first uses the
  measure of that Borel family; the second uses a parent-pair density bound
  assumed only on pairs occurring in the corner family. Both bounds use the
  essential parallel multiplicity and hold at every code value.
* `Projection/CornerOuter`, `CornerProjection`, `CornerOuterMeasure`, `CornerRefinement`:
  the pointwise outer marginal, corner-fiber projection bounds, total and
  restricted outer-density mass identities, and low-density deletion bounds.
  Projection and outer-data image sizes remain outer measures throughout.
* `Projection/SliceRefinement`: the restricted slice-multiplicity identity
  and simultaneous removal of lines through small original slice fibers.
  The refined Borel line family retains half the original volume whenever
  the finite sum of deletion bounds is at most half that volume.
* `Projection/FiberCutoff`, `SliceBallMass`, `Companions`: a measurable cutoff
  for monotone continuous fiber masses, continuity of slice mass in expanding
  slope balls, and Borel companions with exactly the prescribed mass on
  every sufficiently large original slice fiber. Positive slope dimension is
  explicit; null sphere boundaries justify the continuity step.
* `Projection/BalancedPairs`, `BalancedCorners`, `CornerJunction`: simultaneous
  companions over a half-mass center family, the exact pair mass `|G₀|η`,
  the exact corner mass `|G₀|η²`, and volume-preserving coordinates consisting
  of a parent pair and the last-line slope.
* `Projection/ParentCorners`, `InnerCorners`, `CornerCounting`: exact masses
  for restricted parent and inner-pair lifts. Deleting inner pairs costs at
  most their mass times the first-companion mass; the explicit deletion
  budget preserves half the lifted parent mass.
* `Projection/CornerFiberSelection`, `SimultaneousCorners`, `CornerSelection`,
  `CornerWitness`: finite outer-density refinement, simultaneous projection
  bounds on a positive corner-code fiber, and a Borel first-line family
  satisfying both numerical density upper bounds. All conversions to real
  measures have explicit finiteness proofs.
* `Projection/CodeRestriction`, `CodePruning`, `SimultaneousCodePruning`:
  restricted code-mass identities and pointwise additivity under deletion.
  Poor density retention costs at most twice the deleted pair mass for one
  code, and simultaneous pruning costs at most `1 + 2|I|` times that mass.
  Zero original density contributes no original pair mass.
* `Projection/ProjectionImage`: concentration bounds double-projection image
  size, and the later finite density cutoffs use these smaller image sizes
  in their deletion budget.
* `Projection/InnerCodeBound`, `CodeImage`: the first use of the input
  projection estimate on each retained inner-code fiber. It gives a uniform
  density lower bound and hence a finite outer-measure bound on the retained
  code image, without assuming that image is measurable.
* `Projection/CornerAlgebra`, `CornerStep`: the second use of the input
  projection estimate on the selected corner fiber. Eliminating its density
  gives the outer-threshold bound from the parent density; the multiplicity
  exponent is exactly two. This remains a conditional step with explicit
  density and deletion-budget hypotheses, not the full corner improvement.
* `Projection/Concentration`, `FiniteStopping`: the uniform/concentrated
  alternative and selection of a deepest uniform node in a fixed finite
  labeled family. Given the root and terminal bounds, every selected child
  admits a concentrated subset with the stated deletion allowance.
* `Projection/ChildRefinement`: the common child family, simultaneous density
  cutoffs, and simultaneous code retention, with a single explicit bound
  for the total three-stage deletion.
* `Projection/StoppingParameters`, `StoppingBudget`: the exact `ρᵢ` and `αᵢ`
  parameters, their level gaps, and the child budget in both real and extended
  measures. A finite large-projection threshold exists, beyond which the
  child deletion is at most half the parent quota.
* `Projection/CornerPreparation`: lifting a parent family and the refined
  child family to a Borel corner family of positive mass, preserving both
  restrictions and the quantitative mass lower bound.
* `Projection/OuterThreshold`, `OuterStep`: the explicit positive half-mass
  outer threshold and the corner-mass inequality obtained from code-image
  bounds. The outer deletion budget is now discharged internally.
* `Projection/MonomialBounds`, `ThresholdBounds`, `BalancedMassBounds`:
  the real-power identities and inequalities converting balanced masses
  and the inner-code size estimate into the required outer-threshold bound.
* `Projection/CornerAmplification`, `NormalizedAmplification`: the complete
  normalized numerical implication from the balanced-mass, retained-corner,
  inner-image, and outer-projection inequalities to the finite-depth line
  mass exponent. The favorable stopping term is discarded with its sign
  justified, and the main exponent is exactly `cornerUpdate β`.
* `Projection/CornerDepth`: a positive finite depth achieves every exponent
  strictly above the ideal corner update.
* `Projection/CornerPattern`, `PatternConstants`: explicit admissible node
  data, its child labels and complete finite height set, a common input
  estimate constant, and a common positive inner Jacobian bound.
* `Projection/PatternCodeImages`, `PatternOuter`, `PatternRefinement`:
  inner-code image and outer-estimate constants chosen before the line
  family. Concentrated children give one Borel pair family with all the
  code-image bounds while losing at most half the parent quota.
* `Projection/PatternCorners`, `PatternBound`: geometric assembly at a
  uniform parent with concentrated children, followed by the normalized
  line-mass bound. Its constant is independent of the line family, stopping
  level, and depth; the pattern and balanced-mass coefficients are fixed
  inputs. The tree modules below supply such a node.
* `Projection/StoppingBoundary`, `BalancedStopping`: terminal pair images
  have measure at most `N²`; a finite large-projection threshold makes every
  root pair low-density. The actual balanced companion construction gives
  the coefficients `1/(4r)` and `1/(2r)` for its pair mass, with companion
  mass `L/(2rN)` and a half-mass center family.
* `Projection/CornerTree`, `TreeStopping`, `CompanionSystem`, `TreeFamilies`:
  finite labeled trees with exact child triples, simultaneous companion
  families shared at repeated heights, and a selected parent and its
  concentrated children. Terminal nodes have no input-estimate assumption.
* `Projection/TreeThreshold`, `TreeBound`, `TreeNormalized`: one fixed
  projection-size threshold and estimate constant for the whole tree.
  Balanced families and finite stopping supply the geometric hypotheses;
  the two-slice seed handles bounded projection size and small line mass.
* `Projection/TimeTranslation`, `PatternExistence`, `TreeConstruction`:
  translating input heights preserves the projection estimate and its
  constant. Avoiding finitely many degenerate heights gives admissible
  patterns at every distinct parent triple, and grafting these patterns
  constructs a tree of every finite depth.
* `Projection/CornerNormalizedImprovement`: a nonempty finite input estimate
  at `1 < β ≤ 2` gives every exponent strictly above `cornerUpdate β` when
  parallel multiplicity is at most one and projection size is at least one.
  The output heights and constant are chosen before the line family. Tree
  existence, balanced companions, and stopping are discharged internally.
* `Projection/Dilation`, `Normalization`, `CornerImprovement`: spatial
  dilation scales line mass by `r^(2m)` and projections and essential
  parallel multiplicity by `r^m`. Normalizing positive multiplicity and
  handling zero mass separately restores the general estimate
  `L ≤ C M^(2-β) N^β`. The full corner improvement is now proved.
* `Projection/IterationBounds`, `Main`: the corner update is continuous
  and strictly decreases every exponent above the critical root. An
  infimum argument proves that every `β > projectionExponent` admits
  a finite nonempty height set and a uniform projection estimate in
  positive slope dimension. This includes exponents arbitrarily close
  to `1.675130871` from above, without an endpoint assertion.
* `PositiveMeasure/FromMaximal`: a uniform disk maximal estimate on open
  indicators gives `1/C ≤ volume E`, even without measurability of E.
* `PositiveMeasure/Delta`: compact disks inside open sets admit positive
  thickness; every thinner positive plate has average one; plate volumes are
  positive and finite.
* `PositiveMeasure/PlateBound`: a uniform delta-plate maximal estimate gives
  `1/C ≤ volume E`. Fatou handles direction-dependent scale thresholds.
  Measurability of the plate maximal functions is now proved internally.
  The direction probability measure and uniform analytic estimate remain
  explicit inputs; the canonical measure meets the probability requirement.

## Open proof frontier

There are two `sorry` occurrences in the proof development, in
`Induction/Range.lean` and `FiveTwo/Main.lean`, plus the three deliberate Challenge
holes. These stand for large analytic developments, not two short lemmas.

The projection estimate, including its quantitative selectable form, is now
proved at every strict exponent above the critical root. Joint good-time
selection and Tonelli now give the restricted X-ray bound in terms of
line-family volume and essential parallel multiplicity. Uniform bounded
support for rich-line families is also proved. Restricting to comparable
parallel fibers now gives the mixed-norm estimate on each block, uniformly
in its fiber size. The double dyadic decomposition, geometric interpolation,
and both infinite sums are now proved, giving the full indicator estimate
with input-volume exponent `βθ/Q` for any `0 < θ < 1`. The general-input
level decomposition is now proved: the `L^p` norm controls large levels,
and the fixed support controls small levels. Homogeneity gives the full
strong local estimate for every `p > Q/β`, including zero and infinite
norms. The estimate now extends to full lines on bounded support.
Transverse projection controls the perpendicular-displacement norm, and
direction normalization gives the arclength factor. Volume-preserving
Euclidean coordinates, the direction-measure comparison, and a finite
cap cover now give the full spherical mixed-norm bound. The geometric
displacement norm is now Borel measurable for finite positive exponents,
and its Haar-frame norm equals the spherical norm with the exact
surface-area normalization. The strict dimension margin allows the small
input-exponent loss.

The canonical Grassmannian probability measure is implemented, including its
orbit integral formula and uniqueness. Flag integration is now proved in
orthogonal frame coordinates: the joint Haar and lower-dimensional plane
law has the required Grassmannian pushforward. The uniform normalized
plate comparison and a one-dimensional induction step using the proved
X-ray bound are now complete. Power inequalities increase both plate
exponents and all three X-ray exponents without changing the relevant
ratios. Output Hölder and flag integration give a diagonal step with
explicit exponent compatibility. The zero-plane seed, compatible exponent
selection, and finite deficit iteration are now proved. The general target
range yields a positive deficit below one in dimension `n-1`, with finite
input exponent at least two. Moving-ball averaging now extends the local
plate estimates to arbitrary inputs without changing the deficit. The
signed Fourier-slice identity, Schwartz regularity, and averaged
Plancherel formula are now proved. A positive Fourier gap gives the joint
`L²` half-derivative gain with a finite constant. The uniform fixed-support
`L∞` endpoint, normalized kernel dilation, and full Schwartz interpolation
are now proved. Their application gives the frequency gain `a^(-1/p)`
for all finite `p ≥ 2`, now also with polynomial transverse weights when
`a ≥ 1`. Rapid tail control and the weighted fixed-kernel low-frequency
estimate are proved. The smooth dyadic kernels, finite telescoping identities,
uniform approximation, and preservation of Fourier support under polynomial
weights are also proved. Uniform polynomial spatial decay now justifies
convergence through full-plane integration by an integrable majorant on each
affine plane. Intrinsic product-volume coordinates and Schwartz integrability
also prove signed full-plane Fubini in rotated flag frames. The remaining
general-range work is now terminal assembly: the weighted bandlimited
comparison with local plate averages has been proved, with constants uniform
in scale, direction, translation, and input. It remains to integrate and sum
the frequency bounds, localize smooth positive inputs, and pass to open
indicators using the proved passage from uniform maximal bounds to positive
measure.

The independent (5,2) branch still needs the corrected Guth–Zahl and
Katz–Rogers proofs, its maximal estimate, and the Fourier terminal argument.
All these inputs require proofs in Lean; none may be installed as axioms.
The remaining work includes the final source-fidelity audit, Comparator and
kernel verification, Palomar-ready metadata, and the requested README
history and novelty discussion after the two full theorems are proved.

## Verification conventions

`lake build` includes the library, Challenge and Solution as separate targets.
The only intended build warnings are the five explicit holes. All current
files are shorter than 1500 lines. Imports use individual tactic modules.

The initial axiom audits of `criticalExponent_bounds` and
`le_volume_of_diskMaximal_bound` used only `propext`, `Classical.choice` and
`Quot.sound`. The same check passed for `le_volume_of_plateMaximal_bound` and
`Induction.exists_projectionExponent_for_dimension` in the second checkpoint.
`Grassmannian.eq_probability_of_invariant` also passes the standard-axiom
check, with no source warnings.
The same audit passes for `measurable_plateMaximal_indicator`.
It also passes for the exact two-slice projection bound.
The pair-mass lower bound, dual-height code identity, and restricted
double-projection density identity pass the same audit.
The exact pointwise code marginal and pair-fiber projection bound also pass.
The simultaneous code-fiber selection theorem passes the same audit.
The code-density upper bound also passes, with no extra axioms or source warnings.
The full basic pair-improvement theorem and its `7/4` consequence pass the same audit.
The corner-fiber projection bound, the upper bound from parent density, and
the outer-density deletion bound also pass, using only the three standard axioms.
The measurable companion selection and half-mass slice refinement pass the
same audit, as do the explicit decimal exponent bounds and the lemma excluding
`(5,2)` from the general critical-exponent condition.
The simultaneous balanced-pair construction and exact balanced-corner mass
also pass this audit.
The restricted corner half-mass bound, simultaneous corner-code selection,
and finite numerical corner witness pass the same audit.
The bad-code deletion bound, simultaneous code pruning, retained code-image
bound, concentrated-image refinement, and corner-threshold bound also pass.
The finite stopping selection, child refinement with the concrete stopping
parameters, and positive corner-family construction pass the same audit.
The outer step with its internal threshold, normalized numerical
amplification, and finite-depth choice also pass, as does the inverse-density
power identity used to rewrite the inner-code image bound.
The assembled stopping-node bound, root density threshold, and balanced
stopping-data construction also pass the standard-axiom audit.
The full normalized corner-improvement theorem and finite-tree construction
pass the same audit, with no source warnings.
The full corner improvement and the projection-estimate theorem at every
strictly supercritical exponent pass the standard-axiom audit as well.
The selectable two-slice seed, complete quantitative dual-pair reservoir,
and joint measurability of the reservoir selection pass the same audit,
with no source warnings or additional proof holes.
The common outer-scalar reservoir and its joint measurability, the root
triple measure bound, and preservation of child-triple separation also pass
the standard-axiom audit with no source warnings.
The constructed finite-coordinate seed scheme, joint one-node selection,
one-node polynomial measure bound, and uniform inner input estimate pass
the same audit with no source warnings.
The volume-preserving tree-coordinate split, joint whole-tree selection,
full root-and-tree polynomial volume bound, measurable labeled heights,
and analytic tree realization also pass the standard-axiom audit, with
no new proof gaps or source warnings.
The uniform tree-coordinate bound, quantitative control of selected
patterns, polynomial stopping-coefficient bound, and common stopping
bound across selected trees also pass the standard-axiom audit.
The common companion bounds, polynomial stopping threshold, full polynomial
normalized tree estimate, and full estimate for every selected tree parameter
also pass the standard-axiom audit with no source warnings. The refactored
multiplicity-normalization theorem and existing strictly supercritical
finite-height theorem pass again. The complete build succeeds with 2845
jobs and only the five intended challenge and final-theorem holes.
The root-vector volume equivalence, assembled selectable corner improvement,
and selectable projection theorem at every strictly supercritical exponent
pass the standard-axiom audit with no source warnings. The finite-height
theorem also passes after sharing the numerical iteration principle.
The local indicator-transform identity and half-measure good-time theorem
also pass this audit, including the zero-volume case, with no source warnings.
The polynomial common-parameter theorem, full restricted X-ray bound, and
uniform intercept localization pass the standard-axiom audit with no source
warnings. The complete build succeeds with 2852 jobs and the same five
intended holes.
The indicator mixed-norm formula, countable mixed-norm triangle inequality,
and restricted mixed-norm estimate uniform over parallel-fiber scales pass
the same standard-axiom audit with no source warnings. The complete build
succeeds with 2857 jobs and the same five intended holes.
The full double dyadic decomposition, uniform interpolated series bound,
and assembled mixed-norm indicator estimate pass the standard-axiom audit
with no source warnings. The complete build succeeds with 2867 jobs and
the same five intended holes.
The input superlevel decomposition and assembled strong local X-ray estimate
pass the standard-axiom audit with no source warnings. The complete build
succeeds with 2875 jobs and the same five intended holes.
The full-line strong estimate, perpendicular-displacement norm comparison,
and arclength identity pass the standard-axiom audit with no source warnings.
The complete build succeeds with 2896 jobs and the same five intended holes.
The sphere-measure norm comparison, finite bounded-slope cover, finite-cover
norm inequality, perpendicular chart comparison, and full spherical X-ray
estimate pass the standard-axiom audit with no source warnings. The numerical
critical-exponent bound also passes again. The complete build succeeds with
2970 jobs and the same five intended holes.
The continuous normal-plane lift, flag probability pushforward, normalized
sphere law of a Haar orbit, and exact Haar-frame X-ray norm identity pass
the standard-axiom audit with no source warnings. The complete build
succeeds with 2977 jobs and the same five intended holes.
The uniform plate-volume comparison, exact rotation covariance, and assembled
one-dimensional induction step from the spherical X-ray estimate pass the
standard-axiom audit with no source warnings. The complete build succeeds
with 2985 jobs and the same five intended holes.
General-input plate measurability, exponent inflation of plate estimates,
the proved spherical X-ray estimate at all common larger exponent scales,
and the compatible diagonal induction step pass the standard-axiom audit
with no source warnings. The complete build succeeds with 2991 jobs and
the same five intended holes.
The ambient-dimension seed, prescribed-ratio X-ray exponent selection,
unconditional deficit-reducing lift, and complete finite induction to a
subunit deficit pass the standard-axiom audit with no source warnings.
The complete build succeeds with 2996 jobs and the same five intended holes.
Translation covariance, joint measurability of moving-ball plate maxima,
the exact averaged input-norm identity, and globalization with unchanged
deficit pass the standard-axiom audit with no source warnings. The complete
build succeeds with 3001 jobs and the same five intended holes.
Signed Fourier slicing, Schwartz regularity of line integrals, the exact
rotated-hyperplane measure identity, averaged Plancherel, and the finite
half-derivative bound pass the standard-axiom audit with no source warnings.
The complete build succeeds with 3382 jobs and the same five intended holes.
The smoothed endpoint bounds, exact Fourier scaling and one-norm preservation
under kernel dilation, and the smooth-decomposition output-tail estimate
pass the standard-axiom audit with no source warnings. The numerical
critical-exponent bound also passes again. The complete build succeeds
with 3389 jobs and the same five intended holes. All 264 library modules
remain below the requested file-size limit; the largest has 160 lines.
Weighted layer-cake integration, the moment and norm interpolation theorems,
and their application to smoothed X-ray transforms for every finite `p ≥ 2`
pass the standard-axiom audit with no source warnings. The full build
succeeds with 3394 jobs and the same five intended holes. The library now
contains 268 modules, with the largest still 160 lines.
Projected-kernel dilation and decay, translation control, smoothed tails,
the polynomially weighted frequency gain, and the weighted low-frequency
bound pass the standard-axiom audit with no source warnings. The complete
build succeeds with 3404 jobs and the same five intended holes. All 278
library modules satisfy the file-size limit; the largest has 160 lines.
The changed Lean files satisfy the 100-character line limit.
Preservation of Fourier support under polynomial weights, weighted bandlimited
X-ray fibers, the low-frequency kernel construction, finite dyadic convolution
identities, and uniform convergence of the dyadic approximations pass the
standard-axiom audit without source warnings. The full build succeeds with
3409 jobs and the same five intended holes. All 283 library modules remain
within the file-size limit, with a maximum of 160 lines. The metadata continues
to validate against the upstream schema.
Uniform polynomial spatial decay of smooth approximations, dominated
convergence on every full affine plane, intrinsic orthogonal coordinates on
lifted planes, and signed full-plane Fubini in rotated flag frames pass the
standard-axiom audit without source warnings. The full build succeeds with
3413 jobs and the same five intended holes. All 287 library modules satisfy
the file-size limit; the largest remains 160 lines. Changed Lean files stay
within 100 columns, and metadata validates against the upstream schema.
Bandlimited reproduction, the positive convolution majorant, translated-average
control, the weighted plane kernel and its uniform finite mass, and the full
weighted bandlimited plane comparison pass the standard-axiom audit without
source warnings. The full build succeeds with 3421 jobs and the same five
intended holes. All 295 library modules satisfy the file-size limit, with a
maximum of 160 lines. The new Lean files satisfy the 100-character line limit,
and metadata validates against the upstream schema.
`Challenge.lean` now includes the numerical bound as an explicit Comparator
target. `Solution.lean` exports its complete proof from `Exponents.lean`.
The Solution theorem for (5,2) correctly reports `sorryAx`.
Comparator has not been run, and this snapshot is not submission-ready.
Metadata validates against the upstream `formalization.yaml` v0.4 schema.

Existing untracked `tmp/` and `output/` contain supplied research material;
they were not added to the repository by these proof checkpoints.
