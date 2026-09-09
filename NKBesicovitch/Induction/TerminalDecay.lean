/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Induction.Globalization
public import NKBesicovitch.Operators.PlateFamilyNorm
public import NKBesicovitch.Operators.XRay.WeightedDecay
public import NKBesicovitch.Operators.XRay.LowFrequency

/-!
# The terminal frequency gain

The lower-dimensional plate deficit contributes `a^(α/p)` at thickness
`a⁻¹`. The weighted signed X-ray estimate contributes `a^(-1/p)`. Integrating
over frames and lower planes therefore gives the gain `a^(-(1-α)/p)`.
When `α < 1`, its dyadic values are summable.
-/

public section

open MeasureTheory Submodule Set Metric
open scoped SchwartzMap FourierTransform ENNReal NNReal

namespace NKBesicovitch.Induction

variable {m k : ℕ} [Nonempty (Fin m)]
  (v : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
  (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin (m + 1))))ᗮ)

/-- The plate loss and weighted X-ray gain combine in the joint frame-plane norm. -/
theorem HasPlateEstimate.exists_eLpNorm_plateMaximal_frame_decay
    {hkm : k ≤ m} {α p : ℝ} (h : HasPlateEstimate hkm α p) (hp : 2 ≤ p)
    (ψ : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ))
    (hgap : ∀ ξ, ‖ξ‖ < 1 → 𝓕 ψ ξ = 0) (A : ℕ) (R : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ a : ℝ≥0, ∀ ha : 0 < a, 1 ≤ a →
      ∀ f : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ),
      Function.support (f : EuclideanSpace ℝ (Fin (m + 1)) → ℂ) ⊆ closedBall 0 R →
        eLpNorm (fun z : Rotations (m + 1) × Grassmannian m k ↦
          plateMaximal (a : ℝ)⁻¹ (fun x ↦ ‖(1 + ‖x‖ ^ 2) ^ A • XRay.frameLineIntegral v b
            (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
              (normalizedDilation a ha ψ) f) z.1 x‖ₑ) z.2)
          (ENNReal.ofReal p) ((Rotations.probability (m + 1)).prod (Grassmannian.probability hkm)) ≤
            C * (a : ℝ≥0∞) ^ (-(1 - α) / p) * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  obtain ⟨B, hB⟩ := h.global_bound hp0
  obtain ⟨D, hD⟩ := XRay.exists_eLpNorm_weighted_frameLineIntegral_dilation_decay v b ψ hgap A R hp
  refine ⟨B * D, fun a ha ha₁ f hs ↦ ?_⟩
  let g := SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) (normalizedDilation a ha ψ) f
  let F := fun z : Rotations (m + 1) × EuclideanSpace ℝ (Fin m) ↦
    (1 + ‖z.2‖ ^ 2) ^ A • XRay.frameLineIntegral v b g z.1 z.2
  have hF : Measurable F :=
    (by fun_prop : Measurable (fun z : Rotations (m + 1) × EuclideanSpace ℝ (Fin m) ↦
      (1 + ‖z.2‖ ^ 2) ^ A)).smul (XRay.measurable_frameLineIntegral v b g.continuous.measurable)
  have hb := eLpNorm_plateMaximal_family_le (Rotations.probability (m + 1))
    (Grassmannian.probability hkm) (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top
    (B * a⁻¹ ^ (-α / p)) (hB a⁻¹ (inv_pos.mpr ha) (inv_le_one_of_one_le₀ ha₁)) hF.enorm
  rw [eLpNorm_enorm] at hb
  apply hb.trans
  have hd := hD a ha ha₁ f hs
  calc
    _ ≤ (B * a⁻¹ ^ (-α / p) : ℝ≥0) *
        (D * (a : ℝ≥0∞) ^ (-1 / p : ℝ) * eLpNorm f (ENNReal.ofReal p) volume) := by
      exact mul_le_mul_right (by simpa only [ENNReal.ofReal_coe_nnreal] using hd) _
    _ = _ := by
      rw [ENNReal.coe_mul, ENNReal.coe_mul,
        ENNReal.coe_rpow_of_ne_zero (inv_ne_zero ha.ne'), ENNReal.coe_inv ha.ne',
        ENNReal.inv_rpow, ← ENNReal.rpow_neg]
      have he : -(-α / p) + -1 / p = -(1 - α) / p := by ring
      rw [← he, ENNReal.rpow_add _ _ (by exact_mod_cast ha.ne') ENNReal.coe_ne_top]
      ac_rfl

omit [Nonempty (Fin m)] in
/-- The fixed low-frequency piece has a joint frame-plane bound without a Fourier gap. -/
theorem HasPlateEstimate.exists_eLpNorm_plateMaximal_frame_convolution_le
    {hkm : k ≤ m} {α p : ℝ} (h : HasPlateEstimate hkm α p) (hp : 1 ≤ p)
    (ψ : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ)) (A : ℕ) (R : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ f : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ),
      Function.support (f : EuclideanSpace ℝ (Fin (m + 1)) → ℂ) ⊆ closedBall 0 R →
        eLpNorm (fun z : Rotations (m + 1) × Grassmannian m k ↦
          plateMaximal 1 (fun x ↦ ‖(1 + ‖x‖ ^ 2) ^ A • XRay.frameLineIntegral v b
            (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) ψ f) z.1 x‖ₑ) z.2)
          (ENNReal.ofReal p) ((Rotations.probability (m + 1)).prod (Grassmannian.probability hkm)) ≤
            C * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  obtain ⟨B, hB⟩ := h.global_bound hp0
  obtain ⟨D, hD⟩ := XRay.exists_eLpNorm_weighted_frameLineIntegral_convolution_le v b ψ A R hp
  refine ⟨B * D, fun f hs ↦ ?_⟩
  let g := SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) ψ f
  let F := fun z : Rotations (m + 1) × EuclideanSpace ℝ (Fin m) ↦
    (1 + ‖z.2‖ ^ 2) ^ A • XRay.frameLineIntegral v b g z.1 z.2
  have hF : Measurable F :=
    (by fun_prop : Measurable (fun z : Rotations (m + 1) × EuclideanSpace ℝ (Fin m) ↦
      (1 + ‖z.2‖ ^ 2) ^ A)).smul (XRay.measurable_frameLineIntegral v b g.continuous.measurable)
  have hb := eLpNorm_plateMaximal_family_le (Rotations.probability (m + 1))
    (Grassmannian.probability hkm) (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top
    (B * (1 : ℝ≥0) ^ (-α / p)) (hB 1 zero_lt_one le_rfl) hF.enorm
  rw [eLpNorm_enorm] at hb
  simp only [NNReal.coe_one, NNReal.one_rpow, mul_one] at hb
  apply hb.trans
  simpa only [ENNReal.coe_mul, mul_assoc] using mul_le_mul_right (hD f hs) (B : ℝ≥0∞)

end NKBesicovitch.Induction
