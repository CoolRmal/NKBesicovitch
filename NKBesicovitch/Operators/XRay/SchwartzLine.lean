/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.FourierSlice
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Signed line integrals of Schwartz functions

A bound by an integrable function of the line parameter gives continuity
in the normal displacement. Fourier inversion then identifies the signed
line integral with the inverse Fourier transform of a Schwartz restriction.
This supplies its Schwartz regularity and the exact fiberwise Plancherel identity.
-/

public section

open MeasureTheory Submodule
open scoped SchwartzMap FourierTransform RealInnerProductSpace

namespace NKBesicovitch.XRay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {v : E}

theorem norm_schwartz_add_normal_le (hv : ‖v‖ = 1) (f : 𝓢(E, ℂ))
    (y : (ℝ ∙ v)ᗮ) (t : ℝ) :
    ‖f ((y : E) + t • v)‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ 2 0 f) * (1 + t ^ 2)⁻¹ := by
  have hn : t ^ 2 ≤ ‖(y : E) + t • v‖ ^ 2 := by
    have he := norm_normalCoordinates_sq hv y t
    rw [normalCoordinates_apply] at he
    nlinarith [sq_nonneg ‖y‖]
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)]
  calc
    _ = ‖f ((y : E) + t • v)‖ + t ^ 2 * ‖f ((y : E) + t • v)‖ := by ring
    _ ≤ _ := add_le_add (f.norm_le_seminorm ℝ _)
      ((mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans (f.norm_pow_mul_le_seminorm ℝ 2 _))

theorem integrable_schwartz_normalLine (hv : ‖v‖ = 1) (f : 𝓢(E, ℂ)) (y : (ℝ ∙ v)ᗮ) :
    Integrable (fun t : ℝ ↦ f ((y : E) + t • v)) :=
  (integrable_inv_one_add_sq.const_mul _).mono'
    (f.continuous.comp (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ (norm_schwartz_add_normal_le hv f y))

theorem continuous_lineIntegral (hv : ‖v‖ = 1) (f : 𝓢(E, ℂ)) :
    Continuous (fun y : (ℝ ∙ v)ᗮ ↦ ∫ t : ℝ, f ((y : E) + t • v)) := by
  apply continuous_of_dominated
    (bound := fun t : ℝ ↦
      (SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ 2 0 f) * (1 + t ^ 2)⁻¹)
  · intro y
    exact (f.continuous.comp (by fun_prop)).aestronglyMeasurable
  · intro y
    exact ae_of_all _ (norm_schwartz_add_normal_le hv f y)
  · exact integrable_inv_one_add_sq.const_mul _
  · exact ae_of_all _ fun t ↦ f.continuous.comp (by fun_prop)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Integration along a line preserves the Schwartz class in the normal displacement. -/
theorem exists_schwartz_lineIntegral (hv : ‖v‖ = 1) (f : 𝓢(E, ℂ)) :
    ∃ g : 𝓢((ℝ ∙ v)ᗮ, ℂ), ∀ y, g y = ∫ t : ℝ, f ((y : E) + t • v) := by
  let r : 𝓢((ℝ ∙ v)ᗮ, ℂ) := SchwartzMap.compCLMOfAntilipschitz ℂ
    (ℝ ∙ v)ᗮ.subtypeL.hasTemperateGrowth (ℝ ∙ v)ᗮ.subtypeₗᵢ.isometry.antilipschitz (𝓕 f)
  have hr : (r : (ℝ ∙ v)ᗮ → ℂ) =
      𝓕 (fun y : (ℝ ∙ v)ᗮ ↦ ∫ t : ℝ, f ((y : E) + t • v)) := by
    funext ξ
    exact (fourier_lineIntegral hv f.integrable ξ).symm
  refine ⟨𝓕⁻ r, fun y ↦ ?_⟩
  rw [SchwartzMap.fourierInv_coe, hr]
  exact (integrable_lineIntegral hv f.integrable).fourierInv_fourier_eq
    (hr ▸ r.integrable) (continuous_lineIntegral hv f).continuousAt

/-- Plancherel on the normal hyperplane converts line integrals to Fourier restriction. -/
theorem integral_norm_sq_lineIntegral (hv : ‖v‖ = 1) (f : 𝓢(E, ℂ)) :
    (∫ y : (ℝ ∙ v)ᗮ, ‖∫ t : ℝ, f ((y : E) + t • v)‖ ^ 2) =
      ∫ ξ : (ℝ ∙ v)ᗮ, ‖𝓕 f (ξ : E)‖ ^ 2 := by
  obtain ⟨g, hg⟩ := exists_schwartz_lineIntegral hv f
  have he : (g : (ℝ ∙ v)ᗮ → ℂ) =
      fun y : (ℝ ∙ v)ᗮ ↦ ∫ t : ℝ, f ((y : E) + t • v) := funext hg
  have h := g.integral_norm_sq_fourier
  simpa only [SchwartzMap.fourier_coe, he, fourier_lineIntegral hv f.integrable] using h.symm

end NKBesicovitch.XRay
