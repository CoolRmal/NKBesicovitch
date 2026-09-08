/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Grassmannian.Topology
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# The natural probability measure on the real Grassmannian

Push forward normalized Haar measure along an orbit map. Right invariance of
Haar measure and transitivity show that the choice of initial direction does
not affect the result. The dimension bound in `probability` ensures that a
direction exists, including the cases `k = 0` and `k = n`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace NKBesicovitch.Grassmannian

variable {n k : ℕ}

/-- The distribution of a fixed direction under a Haar-distributed orthogonal operator. -/
noncomputable def orbitMeasure (V : Grassmannian n k) : Measure (Grassmannian n k) :=
  (Rotations.probability n).map (fun u ↦ rotate u V)

instance (V : Grassmannian n k) : IsProbabilityMeasure (orbitMeasure V) :=
  Measure.isProbabilityMeasure_map (measurable_orbit V).aemeasurable

instance (V : Grassmannian n k) :
    SMulInvariantMeasure (Rotations n) (Grassmannian n k) (orbitMeasure V) :=
  smulInvariantMeasure_map (Rotations.probability n) _
    (fun u v ↦ rotate_mul u v V) (measurable_orbit V)

instance (V : Grassmannian n k) : Measure.IsOpenPosMeasure (orbitMeasure V) :=
  (continuous_orbit V).isOpenPosMeasure_map (orbit_surjective V)

theorem orbitMeasure_rotate (u : Rotations n) (V : Grassmannian n k) :
    orbitMeasure (rotate u V) = orbitMeasure V := by
  unfold orbitMeasure
  simp_rw [← rotate_mul]
  change Measure.map ((fun v ↦ rotate v V) ∘ (· * u)) _ = _
  rw [← Measure.map_map (measurable_orbit V)
    (continuous_mul_const u).measurable, map_mul_right_eq_self]

theorem orbitMeasure_eq (V W : Grassmannian n k) : orbitMeasure V = orbitMeasure W := by
  obtain ⟨u, rfl⟩ := exists_rotate_eq V W
  exact (orbitMeasure_rotate u V).symm

/-- The natural, rotation-invariant probability measure on k-dimensional directions. -/
noncomputable def probability (hkn : k ≤ n) : Measure (Grassmannian n k) :=
  orbitMeasure (Classical.choice (nonempty_iff.mpr hkn))

instance (hkn : k ≤ n) : IsProbabilityMeasure (probability hkn) := by
  unfold probability
  infer_instance

instance (hkn : k ≤ n) :
    SMulInvariantMeasure (Rotations n) (Grassmannian n k) (probability hkn) := by
  unfold probability
  infer_instance

instance (hkn : k ≤ n) : Measure.IsOpenPosMeasure (probability hkn) := by
  unfold probability
  infer_instance

theorem orbitMeasure_eq_probability (hkn : k ≤ n) (V : Grassmannian n k) :
    orbitMeasure V = probability hkn := orbitMeasure_eq V _

theorem measurePreserving_rotate (hkn : k ≤ n) (u : Rotations n) :
    MeasurePreserving (rotate u) (probability hkn) (probability hkn) :=
  measurePreserving_smul u (probability hkn)

theorem lintegral_probability (hkn : k ≤ n) (V : Grassmannian n k)
    {f : Grassmannian n k → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ W, f W ∂probability hkn) = ∫⁻ u, f (rotate u V) ∂Rotations.probability n := by
  rw [← orbitMeasure_eq_probability hkn V]
  exact lintegral_map hf (measurable_orbit V)

/-- Rotation invariance determines a probability measure on directions uniquely. -/
theorem eq_probability_of_invariant (hkn : k ≤ n) (μ : Measure (Grassmannian n k))
    [IsProbabilityMeasure μ] [SMulInvariantMeasure (Rotations n) (Grassmannian n k) μ] :
    μ = probability hkn := by
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  have hinv (u : Rotations n) : (∫⁻ V, f (rotate u V) ∂μ) = ∫⁻ V, f V ∂μ :=
    (measurePreserving_smul u μ).lintegral_comp hf
  calc
    (∫⁻ V, f V ∂μ) =
        ∫⁻ u, ∫⁻ V, f (rotate u V) ∂μ ∂Rotations.probability n := by
      simp only [hinv, lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ V, ∫⁻ u, f (rotate u V) ∂Rotations.probability n ∂μ :=
      lintegral_lintegral_swap (hf.comp continuous_rotate.measurable).aemeasurable
    _ = ∫⁻ V, f V ∂probability hkn := by
      simp only [← lintegral_probability hkn _ hf, lintegral_const, measure_univ, mul_one]

end NKBesicovitch.Grassmannian
