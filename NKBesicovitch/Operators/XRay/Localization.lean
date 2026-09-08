/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Uniform intercept bounds for local X-ray superlevel sets

A bounded spatial support and bounded slopes put every rich line's
intercept in one fixed ball. The bound is uniform over subsets of the
support and over positive richness thresholds. The superlevel sets are
Borel when the spatial set and slope set are Borel.
-/

@[expose] public section

open MeasureTheory Set Bornology NKBesicovitch.Projection
open scoped ENNReal

namespace NKBesicovitch.XRay

variable {m : ℕ}

/-- Lines in the prescribed slope set with indicator transform at least `r`. -/
noncomputable def richLines (E : Set (EuclideanSpace ℝ (Fin m) × ℝ))
    (Ξ : Set (EuclideanSpace ℝ (Fin m))) (r : ℝ) : Set (Line m) :=
  {g | g.2 ∈ Ξ ∧ ENNReal.ofReal r ≤ localXRay (E.indicator (fun _ ↦ (1 : ℝ≥0∞))) g.2 g.1}

theorem measurableSet_richLines {E : Set (EuclideanSpace ℝ (Fin m) × ℝ)}
    (hE : MeasurableSet E) {Ξ : Set (EuclideanSpace ℝ (Fin m))} (hΞ : MeasurableSet Ξ) (r : ℝ) :
    MeasurableSet (richLines E Ξ r) := by
  have h := (hΞ.preimage (measurable_snd : Measurable (Prod.snd : Line m → _))).inter
    (measurableSet_le (measurable_const (a := ENNReal.ofReal r))
      (measurable_localXRay ((measurable_const (a := (1 : ℝ≥0∞))).indicator hE)))
  simpa only [richLines, preimage, ofPred_and] using h

theorem norm_intercept_le_of_mem_richLines {E : Set (EuclideanSpace ℝ (Fin m) × ℝ)}
    (hE : MeasurableSet E) {Ξ : Set (EuclideanSpace ℝ (Fin m))} {R A r : ℝ}
    (hR : ∀ p ∈ E, ‖p.1‖ ≤ R) (hA : ∀ ξ ∈ Ξ, ‖ξ‖ ≤ A) (hr : 0 < r)
    {g : Line m} (hg : g ∈ richLines E Ξ r) : ‖g.1‖ ≤ R + A := by
  have hmass : 0 < volume (lineTimes E g) := by
    rw [← localXRay_indicator_eq_volume_lineTimes hE]
    exact (ENNReal.ofReal_pos.mpr hr).trans_le hg.2
  obtain ⟨t, htunit, htE⟩ : (lineTimes E g).Nonempty :=
    nonempty_of_measure_ne_zero hmass.ne'
  have ht0 : 0 ≤ t := htunit.1
  have ht : |t| ≤ 1 := by
    rw [abs_of_nonneg ht0]
    exact htunit.2
  have hξ := hA g.2 hg.1
  have hpoint : ‖atHeight t g‖ ≤ R := hR (atHeight t g, t) htE
  have hnorm : ‖t • g.2‖ ≤ A := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right ht (norm_nonneg _)).trans (by
      simpa only [one_mul] using hξ)
  have heq : atHeight t g - t • g.2 = g.1 := by
    simp only [atHeight, add_sub_cancel_right]
  rw [← heq]
  exact (norm_sub_le _ _).trans (add_le_add hpoint hnorm)

/-- One intercept ball works for every Borel subset of a fixed bounded support. -/
theorem exists_uniform_intercept_bound {K : Set (EuclideanSpace ℝ (Fin m) × ℝ)}
    (hK : IsBounded K) {Ξ : Set (EuclideanSpace ℝ (Fin m))} (hΞ : IsBounded Ξ) :
    ∃ R : ℝ, 0 < R ∧ ∀ E : Set (EuclideanSpace ℝ (Fin m) × ℝ), MeasurableSet E → E ⊆ K →
      ∀ r : ℝ, 0 < r → richLines E Ξ r ⊆ Metric.closedBall 0 R ×ˢ Ξ := by
  obtain ⟨R, hR, hbound⟩ := hK.image_fst.exists_pos_norm_le
  obtain ⟨A, hA, hslopes⟩ := hΞ.exists_pos_norm_le
  refine ⟨R + A, add_pos hR hA, fun E hE hEK r hr g hg ↦ ⟨?_, hg.1⟩⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_intercept_le_of_mem_richLines hE
    (fun p hp ↦ hbound p.1 ⟨p, hEK hp, rfl⟩) hslopes hr hg

theorem isBounded_richLines {E : Set (EuclideanSpace ℝ (Fin m) × ℝ)}
    (hE : MeasurableSet E) (hEb : IsBounded E) {Ξ : Set (EuclideanSpace ℝ (Fin m))}
    (hΞ : IsBounded Ξ) {r : ℝ} (hr : 0 < r) : IsBounded (richLines E Ξ r) := by
  obtain ⟨R, _, hR⟩ := exists_uniform_intercept_bound hEb hΞ
  exact ((Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin m)))
    (r := R)).prod hΞ).subset
    (hR E hE Subset.rfl r hr)

end NKBesicovitch.XRay
