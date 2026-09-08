/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.WeightedNorm
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# The low-frequency smoothed X-ray bound

A fixed Schwartz smoothing kernel gives bounded weighted `Lᵖ` transforms
on input supported in a fixed ball, for every finite `p ≥ 1`. This includes
the low-frequency kernel without requiring its Fourier transform to vanish
at the origin.
-/

public section

open MeasureTheory Submodule Set Metric
open scoped SchwartzMap ENNReal NNReal

namespace NKBesicovitch.XRay

variable {m : ℕ} (v : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
  (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin (m + 1))))ᗮ)

/-- Fixed smoothing maps supported inputs from `L¹` to joint `Lᵖ`, uniformly in the input. -/
theorem exists_eLpNorm_frameLineIntegral_convolution_le_one
    (ψ : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ)) (R : ℝ≥0) {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ≥0, ∀ f : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ),
      Function.support (f : EuclideanSpace ℝ (Fin (m + 1)) → ℂ) ⊆ closedBall 0 R →
        eLpNorm (fun z : Rotations (m + 1) × EuclideanSpace ℝ (Fin m) ↦
          frameLineIntegral v b (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) ψ f)
            z.1 z.2) (ENNReal.ofReal p) ((Rotations.probability (m + 1)).prod volume) ≤
              C * eLpNorm f 1 volume := by
  let μ := (Rotations.probability (m + 1)).prod (volume : Measure (EuclideanSpace ℝ (Fin m)))
  let H := fun z : Rotations (m + 1) × EuclideanSpace ℝ (Fin m) ↦ ((1 + ‖z.2‖) ^ (m + 1))⁻¹
  have hH : MemLp H (ENNReal.ofReal p) μ :=
    (memLp_inv_one_add_norm_pow volume
      (by simp only [finrank_euclideanSpace, Fintype.card_fin]; omega) hp).comp_snd _
  obtain ⟨C, hC⟩ := exists_enorm_frameLineIntegral_convolution_le v b ψ (m + 1) R
  refine ⟨C * (eLpNorm H (ENNReal.ofReal p) μ).toNNReal, fun f hs ↦ ?_⟩
  refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' (ENNReal.ofReal p) hH.1
    (c := C * eLpNorm f 1 volume) (ae_of_all _ fun z ↦ ?_)).trans_eq ?_
  · have h := hC f hs z.1 z.2
    simpa only [Real.enorm_of_nonneg (by dsimp [H]; positivity : 0 ≤ H z),
      ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal,
      mul_assoc, mul_comm, mul_left_comm] using h
  · rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hH.2.ne]
    ac_rfl

/-- Every polynomially weighted low-frequency transform is bounded on fixed-support `Lᵖ`. -/
theorem exists_eLpNorm_weighted_frameLineIntegral_convolution_le
    (ψ : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ)) (A : ℕ) (R : ℝ≥0)
    {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ≥0, ∀ f : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ),
      Function.support (f : EuclideanSpace ℝ (Fin (m + 1)) → ℂ) ⊆ closedBall 0 R →
        eLpNorm (fun z : Rotations (m + 1) × EuclideanSpace ℝ (Fin m) ↦
          (1 + ‖z.2‖ ^ 2) ^ A • frameLineIntegral v b
            (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) ψ f) z.1 z.2)
          (ENNReal.ofReal p) ((Rotations.probability (m + 1)).prod volume) ≤
            C * eLpNorm f (ENNReal.ofReal p) volume := by
  have hq : 1 / p ≤ 1 := (div_le_one (zero_lt_one.trans_le hp)).mpr hp
  let K := (volume (closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) R)) ^ (1 - 1 / p)
  have hK : K ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr hq) measure_closedBall_lt_top.ne
  obtain ⟨B, C, hC⟩ := exists_eLpNorm_weighted_frameLineIntegral_dilation_le v b ψ A 0 R hp
  obtain ⟨D, hD⟩ := exists_eLpNorm_frameLineIntegral_convolution_le_one v b ψ R hp
  refine ⟨(B * D + C) * K.toNNReal, fun f hs ↦ ?_⟩
  have hf₁ : eLpNorm f 1 volume ≤ eLpNorm f (ENNReal.ofReal p) volume * K := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict (closedBall 0 R))
      (ENNReal.one_le_ofReal.mpr hp) f.continuous.measurable.aestronglyMeasurable
    simpa only [eLpNorm_restrict_eq_of_support_subset hs, Measure.restrict_apply_univ,
      ENNReal.toReal_one, div_one, ENNReal.toReal_ofReal (zero_le_one.trans hp)] using h
  have h := hC 1 zero_lt_one le_rfl f hs
  simp only [normalizedDilation_one, one_pow, inv_one, ENNReal.ofReal_one, mul_one] at h
  apply h.trans
  calc
    _ ≤ (B : ℝ≥0∞) * (D * eLpNorm f 1 volume) + C * eLpNorm f 1 volume :=
      add_le_add (mul_le_mul' le_rfl (hD f hs)) le_rfl
    _ = ((B : ℝ≥0∞) * D + C) * eLpNorm f 1 volume := by rw [add_mul, mul_assoc]
    _ ≤ ((B : ℝ≥0∞) * D + C) * (eLpNorm f (ENNReal.ofReal p) volume * K) :=
      mul_le_mul' le_rfl hf₁
    _ = _ := by
      simp only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_toNNReal hK]
      ac_rfl

end NKBesicovitch.XRay
