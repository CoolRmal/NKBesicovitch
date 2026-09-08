# Verified progress and remaining proof frontier

This is an implementation ledger. `PLAN.md` retains the complete objective and
source decomposition. The final theorems are not proved yet.

## Completed foundations

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

The canonical Grassmannian probability measure is now implemented. Its orbit
integral formula and uniqueness can be used to identify distributions in the
induction. **Flag disintegration** is still open: construct the joint law of a
line and a plane in its orthogonal complement and identify its Grassmannian
pushforward. The current measure implications accept any explicit probability
measure, including this canonical one.

The remaining operator work is to develop the actual uniform analytic estimates
supplying the positive-measure implications.
The general range needs the selectable corner/projection estimate, the
mixed-norm transfer and the induction. The (5,2) branch needs the corrected
Guth–Zahl and Katz–Rogers proofs and the Fourier terminal estimate. All these
inputs require proofs in Lean; none may be installed as axioms.

For the projection estimate, the pair-incidence mass, low-density deletion,
code-fiber projection bound, and simultaneous fiber-selection steps are now
proved, including the code-density upper bound using parallel multiplicity.
The basic pair improvement is proved. The stronger corner improvement and
quantitative selection of its height patterns are still open.
The exact corner identities, both fiber upper bounds, outer-density deletion,
initial slice refinement, and measurable selection of companions with exactly
prescribed fiber mass are now proved, as are the exact balanced pair and
corner masses, restricted parent/inner-pair counts, and simultaneous outer
fiber selection. The next corner steps are the finite uniform/concentrated
pruning tree, the inner-code refinement and image-size bound, and their
combination with the selected-fiber inequalities for exponent improvement.
Quantitative height selection is also still open.

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
`Challenge.lean` now includes the numerical bound as an explicit Comparator
target. `Solution.lean` exports its complete proof from `Exponents.lean`.
The Solution theorem for (5,2) correctly reports `sorryAx`.
Comparator has not been run, and this snapshot is not submission-ready.
Metadata validates against the upstream `formalization.yaml` v0.4 schema.

Existing untracked `tmp/` and `output/` contain supplied research material;
they were not added to the repository by these proof checkpoints.
