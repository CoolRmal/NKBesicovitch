/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.WeightedTail
public import NKBesicovitch.Operators.PolynomialWeight
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Weighted norm control by an unweighted norm and a rapid tail

Integrating the polynomial tail bounds costs only a finite spatial constant.
The resulting estimate retains arbitrary frequency decay in the tail term.
-/

public section

open MeasureTheory Submodule Set Metric
open scoped SchwartzMap ENNReal NNReal

namespace NKBesicovitch.XRay

variable {m : ℕ} (v : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
  (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin (m + 1))))ᗮ)

/-- Polynomial weights add only a rapidly decaying one-norm term to the unweighted norm. -/
theorem exists_eLpNorm_weighted_frameLineIntegral_dilation_le
    (ψ : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ)) (A L : ℕ) (R : ℝ≥0)
    {p : ℝ} (hp : 1 ≤ p) :
    ∃ B C : ℝ≥0, ∀ a : ℝ, ∀ ha : 0 < a, 1 ≤ a →
      ∀ f : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ),
      Function.support (f : EuclideanSpace ℝ (Fin (m + 1)) → ℂ) ⊆ closedBall 0 R →
        let g := fun z : Rotations (m + 1) × EuclideanSpace ℝ (Fin m) ↦
          frameLineIntegral v b (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
            (normalizedDilation a ha ψ) f) z.1 z.2
        eLpNorm (fun z ↦ (1 + ‖z.2‖ ^ 2) ^ A • g z) (ENNReal.ofReal p)
          ((Rotations.probability (m + 1)).prod volume) ≤
            B * eLpNorm g (ENNReal.ofReal p) ((Rotations.probability (m + 1)).prod volume) +
              C * ENNReal.ofReal ((a ^ L)⁻¹) * eLpNorm f 1 volume := by
  let μ := (Rotations.probability (m + 1)).prod (volume : Measure (EuclideanSpace ℝ (Fin m)))
  let H := fun z : Rotations (m + 1) × EuclideanSpace ℝ (Fin m) ↦ ((1 + ‖z.2‖) ^ (m + 1))⁻¹
  have hH : MemLp H (ENNReal.ofReal p) μ :=
    (memLp_inv_one_add_norm_pow volume
      (by simp only [finrank_euclideanSpace, Fintype.card_fin]; omega) hp).comp_snd _
  obtain ⟨B, C, hC⟩ := exists_norm_weighted_frameLineIntegral_dilation_le v b ψ A L (m + 1) R
  refine ⟨B, C * (eLpNorm H (ENNReal.ofReal p) μ).toNNReal, fun a ha ha₁ f hs ↦ ?_⟩
  let g := frameLineIntegralLinearMap v b
    (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) (normalizedDilation a ha ψ) f)
  let D : ℝ := (C : ℝ) * (a ^ L)⁻¹ * (eLpNorm f 1 volume).toReal
  have hg : AEStronglyMeasurable g μ := (measurable_frameLineIntegral v b
    (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
      (normalizedDilation a ha ψ) f).continuous.measurable).aestronglyMeasurable
  have hn (z) : 0 ≤ (B : ℝ) * ‖g z‖ + D * H z := by dsimp [D, H]; positivity
  calc
    _ ≤ eLpNorm ((B : ℝ) • (fun z ↦ ‖g z‖) + D • H) (ENNReal.ofReal p) μ := by
      apply eLpNorm_mono
      intro z
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Real.norm_of_nonneg (hn z)]
      simpa only [g, frameLineIntegralLinearMap_apply] using hC a ha ha₁ f hs z.1 z.2
    _ ≤ _ := (eLpNorm_add_le (hg.norm.const_smul _) (hH.1.const_smul _)
      (ENNReal.one_le_ofReal.mpr hp)).trans_eq (by
        rw [eLpNorm_const_smul, eLpNorm_const_smul, eLpNorm_norm]
        simp only [← ofReal_norm, Real.norm_of_nonneg B.coe_nonneg,
          Real.norm_of_nonneg (by dsimp [D]; positivity : 0 ≤ D), D,
          ENNReal.ofReal_mul C.coe_nonneg,
          ENNReal.ofReal_mul (by positivity : 0 ≤ (C : ℝ) * (a ^ L)⁻¹),
          ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal (f.memLp 1 volume).2.ne,
          ENNReal.coe_mul, ENNReal.coe_toNNReal hH.2.ne]
        ac_rfl)

end NKBesicovitch.XRay
