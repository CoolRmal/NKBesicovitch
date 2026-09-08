# Verified progress and remaining proof frontier

This is an implementation ledger. `PLAN.md` retains the complete objective and
source decomposition. The final theorems are not proved yet.

## Completed foundations

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
The basic pair improvement, full corner improvement, and existence of a
finite-height estimate at every exponent strictly above the critical root
are proved. The selectable version inside a prescribed positive-measure
time set still needs uniform polynomial control of the final estimate constant.
The exact corner identities, both fiber upper bounds, outer-density deletion,
initial slice refinement, and measurable selection of companions with exactly
prescribed fiber mass are now proved, as are the exact balanced pair and
corner masses, restricted parent/inner-pair counts, and simultaneous outer
fiber selection. Inner-code pruning, its image-size bound, and both uses of
the input projection estimate are now proved with explicit hypotheses.
The finite stopping selection, common-child construction, and the concrete
child deletion budget are now proved, including their lift to positive
corner mass. The finite-tree assembly is now complete: admissible heights
and trees are constructed from the input projection estimate, common
constants are chosen across all nodes, and the root, terminal, and finite
stopping arguments provide the needed families. Spatial dilation restores
the general multiplicity factor, and the approximation argument reaches
every strict exponent above the critical root. The remaining projection
work is quantitative height selection: Borel parameter families of
polynomially controlled volume and estimate constants inside arbitrary
positive-measure time sets. The current finite-height existence theorem
does not supply that stronger selection rule.
The selectable two-slice seed, quantitative dual-pair reservoir, common
outer-scalar reservoir, and separated root and child triples are now proved.
The finite-coordinate scheme interface and its seed, one-node joint
selection, polynomial parameter measure, and uniform input constants are
also proved. The existing corner theorem accepts the seed exponent `2`, so
the planned iteration can start there directly. A separate selectable pair
step is not required for this route.
Whole-tree coordinates now split into root and child product coordinates
by a volume-preserving measurable equivalence. The recursive selection is
jointly Borel. If `S_J` is the number of nonterminal labeled nodes, its
parameter-volume exponent is `(4 + (8 + 6L)A) S_J`; selecting the separated
root triple adds three. The constants are positive and independent of the
time set. All labeled output heights are jointly measurable and lie in
the original time set. Every selected parameter realizes an admissible
analytic `CornerTree` using only those labeled heights.
All tree coordinates now obey the same bound `C (100/|I|)^(8B)` at every
depth. Selected analytic patterns retain common separation, label-count,
input-estimate, and Jacobian bounds. The inner and outer analytic
coefficients reduce to the same explicit monomial. Prescribed constants
now pass through child refinement and the stopping-node proof, and the
resulting stopping constant has a uniform positive integer-power bound
in `1/|I|`. For fixed balanced-mass coefficients, that bound works at
every internal node of every selected tree, independently of depth.
The finite label count now gives fixed lower balanced-mass coefficients
and a pair-mass upper coefficient independent of the numerical height set.
`ControlledThreshold` bounds all root and pruning thresholds by a polynomial
in `1/|I|`. `TreeUniformBound` and `TreeControlledBound` retain a prescribed
stopping coefficient and combine the large-size case with an explicit
two-slice bound. `TreePolynomialBound` bounds the resulting constant by a
single positive integer power of `1/|I|`.
`Selection/TreeEstimate` applies this estimate to every selected parameter.
Both the normalized estimate and the full parallel-multiplicity estimate
have constants depending only on the input scheme and fixed depth, with
the stated polynomial dependence on time-set measure. The remaining
projection work is to reindex the finite arrays into the scheme interface
and iterate the selectable corner improvement.

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
finite-height theorem pass again. The complete build succeeds with 2838
jobs and only the five intended challenge and final-theorem holes.
`Challenge.lean` now includes the numerical bound as an explicit Comparator
target. `Solution.lean` exports its complete proof from `Exponents.lean`.
The Solution theorem for (5,2) correctly reports `sorryAx`.
Comparator has not been run, and this snapshot is not submission-ready.
Metadata validates against the upstream `formalization.yaml` v0.4 schema.

Existing untracked `tmp/` and `output/` contain supplied research material;
they were not added to the repository by these proof checkpoints.
