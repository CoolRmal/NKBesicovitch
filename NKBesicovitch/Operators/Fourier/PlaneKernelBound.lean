/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.Fourier.PlaneKernelMass
public import NKBesicovitch.Operators.PlateKernelBound

/-!
# Uniform plate bounds for weighted plane kernels

Every point of a plate is a unit tangential displacement plus a smaller-than-
thickness ambient displacement. The kernel shift bound therefore applies
throughout the plate, and averaging gives a constant independent of its
thickness, direction, and center.
-/

public section

open MeasureTheory Metric
open scoped ENNReal NNReal

namespace NKBesicovitch

theorem weightedPlaneKernel_sub_le_of_mem_plate {n k : ℕ} (V : Grassmannian n k)
    (a : ℝ) (ha : 0 < a) (A N : ℕ) (x z t : EuclideanSpace ℝ (Fin n))
    (ht : t ∈ plate a⁻¹ V.val 0) :
    weightedPlaneKernel V.val a A N x z ≤
      (4 : ℝ≥0∞) ^ (A + N) * weightedPlaneKernel V.val a A N x (z - t) := by
  obtain ⟨w, hw, htw⟩ := mem_thickening_iff.mp ht
  have hw' : w ∈ V.val ∧ ‖w‖ ≤ 1 := by simpa [unitDisk] using hw
  have he : ‖a • (t - w)‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg ha.le]
    have hnorm : ‖t - w‖ < a⁻¹ := by simpa only [dist_eq_norm] using htw
    nlinarith [mul_lt_mul_of_pos_left hnorm ha, mul_inv_cancel₀ ha.ne']
  simpa only [add_sub_cancel] using
    weightedPlaneKernel_sub_le V.val a A N x z ⟨w, hw'.1⟩ hw'.2 (t - w) he

/-- Weighted plane kernels pair with arbitrary inputs with a scale-independent plate bound. -/
theorem exists_lintegral_mul_weightedPlaneKernel_le {n k A N : ℕ}
    (hA : k < 2 * A) (hN : n < 2 * N) :
    ∃ C : ℝ≥0, ∀ (V : Grassmannian n k) (a : ℝ), 0 < a →
      ∀ (x : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞),
        Measurable f → (∫⁻ z, f z * weightedPlaneKernel V.val a A N x z) ≤
          C * plateMaximal a⁻¹ f V := by
  obtain ⟨B, hB⟩ := exists_lintegral_weightedPlaneKernel_le hA hN
  refine ⟨4 ^ (A + N) * B, fun V a ha x f hf ↦ ?_⟩
  have h := lintegral_mul_le_plateMaximal (inv_pos.mpr ha) V hf
    (measurable_weightedPlaneKernel V.val a A N x) (C := (4 : ℝ≥0) ^ (A + N))
    (fun z t ht ↦ by simpa only [ENNReal.coe_pow, ENNReal.coe_ofNat] using
      weightedPlaneKernel_sub_le_of_mem_plate V a ha A N x z t ht)
  simp only [ENNReal.coe_pow, ENNReal.coe_ofNat] at h
  apply h.trans
  calc
    _ ≤ (4 : ℝ≥0∞) ^ (A + N) * plateMaximal a⁻¹ f V * B := by
      gcongr
      exact hB V a ha x
    _ = _ := by simp only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat]; ac_rfl

end NKBesicovitch
