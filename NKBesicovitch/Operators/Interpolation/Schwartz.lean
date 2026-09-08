/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.Interpolation.EndpointTail
public import NKBesicovitch.Operators.Interpolation.TailBound

/-!
# Interpolating the two and infinity endpoints on Schwartz functions

Smooth amplitude decomposition and layer-cake integration prove the strong
`Lᵖ` estimate for `p > 2` on compactly supported Schwartz inputs. The endpoint
two-norm constant enters as `A^(2/p)`. The remaining constant is finite and
depends only on `p` and the bounded-input endpoint constant.
-/

public section

open Function Set MeasureTheory
open scoped SchwartzMap ENNReal NNReal

namespace NKBesicovitch

variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Y]

/-- The moment form of interpolation between the two-norm and bounded-input endpoints. -/
theorem lintegral_enorm_rpow_le_of_endpoints (T : 𝓢(E, ℂ) →+ (Y → ℂ)) (μ : Measure Y)
    {s : Set E} (A : ℝ≥0) {B p : ℝ} (hB : 0 < B) (hp : 2 < p)
    (hmeas : ∀ f, AEStronglyMeasurable (T f) μ)
    (h₂ : ∀ f : 𝓢(E, ℂ), support (f : E → ℂ) ⊆ s →
      eLpNorm (T f) 2 μ ≤ A * eLpNorm f 2 volume)
    (h_top : ∀ f : 𝓢(E, ℂ), support (f : E → ℂ) ⊆ s → ∀ r : ℝ, 0 ≤ r →
      (∀ x, ‖f x‖ ≤ r) → ∀ᵐ y ∂μ, ‖T f y‖ ≤ B * r)
    (f : 𝓢(E, ℂ)) (hf : HasCompactSupport (f : E → ℂ)) (hs : support (f : E → ℂ) ⊆ s) :
    (∫⁻ y, ‖T f y‖ₑ ^ p ∂μ) ≤
      (ENNReal.ofReal (4 * B) ^ p * ENNReal.ofReal p * (ENNReal.ofReal (2 * B))⁻¹ ^ 2 *
        (ENNReal.ofReal (p - 2))⁻¹) * (A : ℝ≥0∞) ^ 2 * ∫⁻ x, ‖f x‖ₑ ^ p := by
  let K : ℝ≥0∞ := (ENNReal.ofReal (2 * B))⁻¹ ^ 2 * (A : ℝ≥0∞) ^ 2
  have hK : K ≠ ∞ := by dsimp [K]; finiteness
  have htail (t : ℝ) (ht : 0 < t) : μ {y | (4 * B) * t < ‖T f y‖} ≤
      K.toNNReal * (ENNReal.ofReal t)⁻¹ ^ 2 * ∫⁻ x in {x | t < ‖f x‖}, ‖f x‖ₑ ^ 2 := by
    have h := measure_norm_gt_le_of_endpoints T μ hB hmeas h₂ h_top f hf hs ht
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * B),
      ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.mpr (by positivity : 0 < 2 * B)).ne')
        (Or.inl ENNReal.ofReal_ne_top), mul_pow] at h
    rw [ENNReal.coe_toNNReal hK]
    simpa only [K, mul_assoc, mul_comm, mul_left_comm] using h
  have h := lintegral_enorm_rpow_le_of_sq_tail volume μ f.continuous.measurable
    (hmeas f) hp (by positivity : 0 < 4 * B) K.toNNReal htail
  rw [ENNReal.coe_toNNReal hK] at h
  simpa only [K, mul_assoc, mul_comm, mul_left_comm] using h

/-- A finite interpolation constant uniform over operators and their two-norm constants. -/
theorem exists_eLpNorm_bound_of_endpoints (μ : Measure Y) {B p : ℝ} (hB : 0 < B) (hp : 2 < p) :
    ∃ C : ℝ≥0, ∀ T : 𝓢(E, ℂ) →+ (Y → ℂ), ∀ A : ℝ≥0, ∀ s : Set E,
      (∀ f, AEStronglyMeasurable (T f) μ) →
      (∀ f : 𝓢(E, ℂ), support (f : E → ℂ) ⊆ s →
        eLpNorm (T f) 2 μ ≤ A * eLpNorm f 2 volume) →
      (∀ f : 𝓢(E, ℂ), support (f : E → ℂ) ⊆ s → ∀ r : ℝ, 0 ≤ r →
        (∀ x, ‖f x‖ ≤ r) → ∀ᵐ y ∂μ, ‖T f y‖ ≤ B * r) →
      ∀ f : 𝓢(E, ℂ), HasCompactSupport (f : E → ℂ) → support (f : E → ℂ) ⊆ s →
        eLpNorm (T f) (ENNReal.ofReal p) μ ≤
          C * (A : ℝ≥0∞) ^ (2 / p : ℝ) * eLpNorm f (ENNReal.ofReal p) volume := by
  let D : ℝ≥0∞ := ENNReal.ofReal (4 * B) ^ p * ENNReal.ofReal p *
    (ENNReal.ofReal (2 * B))⁻¹ ^ 2 * (ENNReal.ofReal (p - 2))⁻¹
  have hD : D ≠ ∞ := by dsimp [D]; finiteness
  have hp' : 0 < p := by linarith
  have hpinv : 0 ≤ 1 / p := by positivity
  refine ⟨D.toNNReal ^ (1 / p : ℝ), fun T A s hmeas h₂ h_top f hf hs ↦ ?_⟩
  have hm : (∫⁻ y, ‖T f y‖ₑ ^ p ∂μ) ≤ D * (A : ℝ≥0∞) ^ 2 * ∫⁻ x, ‖f x‖ₑ ^ p :=
    lintegral_enorm_rpow_le_of_endpoints T μ A hB hp hmeas h₂ h_top f hf hs
  have h := ENNReal.rpow_le_rpow hm hpinv
  rw [ENNReal.mul_rpow_of_nonneg _ _ hpinv, ENNReal.mul_rpow_of_nonneg _ _ hpinv,
    ← ENNReal.rpow_two (A : ℝ≥0∞), ← ENNReal.rpow_mul] at h
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp').ne'
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp'.le]
  rw [ENNReal.coe_rpow_of_nonneg _ hpinv, ENNReal.coe_toNNReal hD]
  simpa only [div_eq_mul_inv, one_mul] using h

/-- A half-derivative two-norm gain interpolates to a `1/p`-derivative gain. -/
theorem exists_eLpNorm_decay_of_endpoints (μ : Measure Y) {B p : ℝ}
    (hB : 0 < B) (hp : 2 < p) (K : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ a : ℝ, 0 < a → ∀ T : 𝓢(E, ℂ) →+ (Y → ℂ), ∀ s : Set E,
      (∀ f, AEStronglyMeasurable (T f) μ) →
      (∀ f : 𝓢(E, ℂ), support (f : E → ℂ) ⊆ s → eLpNorm (T f) 2 μ ≤
        K * (ENNReal.ofReal a) ^ (-1 / 2 : ℝ) * eLpNorm f 2 volume) →
      (∀ f : 𝓢(E, ℂ), support (f : E → ℂ) ⊆ s → ∀ r : ℝ, 0 ≤ r →
        (∀ x, ‖f x‖ ≤ r) → ∀ᵐ y ∂μ, ‖T f y‖ ≤ B * r) →
      ∀ f : 𝓢(E, ℂ), HasCompactSupport (f : E → ℂ) → support (f : E → ℂ) ⊆ s →
        eLpNorm (T f) (ENNReal.ofReal p) μ ≤
          C * (ENNReal.ofReal a) ^ (-1 / p : ℝ) * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_bound_of_endpoints (E := E) μ hB hp
  have hp₂ : 0 ≤ 2 / p := by positivity
  refine ⟨C * K ^ (2 / p : ℝ), fun a ha T s hmeas h₂ h_top f hf hs ↦ ?_⟩
  let A : ℝ≥0∞ := K * (ENNReal.ofReal a) ^ (-1 / 2 : ℝ)
  have hA : A ≠ ∞ := by dsimp [A]; finiteness
  have h := hC T A.toNNReal s hmeas (by simpa only [ENNReal.coe_toNNReal hA] using h₂)
    h_top f hf hs
  rw [ENNReal.coe_toNNReal hA, ENNReal.mul_rpow_of_nonneg _ _ hp₂, ← ENNReal.rpow_mul] at h
  have hexp : (-1 / 2 : ℝ) * (2 / p) = -1 / p := by ring
  rw [hexp] at h
  rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ hp₂]
  simpa only [mul_assoc] using h

end NKBesicovitch
