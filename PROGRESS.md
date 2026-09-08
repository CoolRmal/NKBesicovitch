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
`Induction/Range.lean` and `FiveTwo/Main.lean`, plus the two deliberate Challenge
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
and code-fiber projection-bound steps are now proved. Fiber selection,
the code-density upper bound using parallel multiplicity, pair improvement,
and corner improvement are still open.

## Verification conventions

`lake build` includes the library, Challenge and Solution as separate targets.
The only intended build warnings are the four explicit holes. All current
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
The Solution theorem for (5,2) correctly reports `sorryAx`.
Comparator has not been run, and this snapshot is not submission-ready.
Metadata validates against the upstream `formalization.yaml` v0.4 schema.

Existing untracked `tmp/` and `output/` contain supplied research material;
they were not added to the repository by these proof checkpoints.
