/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Geometry.NormalCoordinates
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fourier restriction after integrating along a line

For an integrable complex-valued input, the Fourier transform of its signed
line integral is the restriction of its ambient Fourier transform to the
normal hyperplane. The unit normal fixes arclength normalization. Absolute
values are taken only after line integration in the later Fourier estimates.
-/

public section

open MeasureTheory Submodule
open scoped FourierTransform RealInnerProductSpace

namespace NKBesicovitch.XRay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {v : E}

theorem integrable_lineIntegral (hv : ‖v‖ = 1) {f : E → ℂ} (hf : Integrable f) :
    Integrable (fun y : (ℝ ∙ v)ᗮ ↦ ∫ t : ℝ, f ((y : E) + t • v)) := by
  have hi := ((measurePreserving_normalCoordinates hv).integrable_comp_emb
    (normalCoordinates hv).toHomeomorph.measurableEmbedding).mpr hf
  rw [Measure.volume_eq_prod] at hi
  simpa only [Function.comp_def, normalCoordinates_apply] using hi.integral_prod_left

/-- The Fourier-slice identity, with arclength along a unit normal. -/
theorem fourier_lineIntegral (hv : ‖v‖ = 1) {f : E → ℂ} (hf : Integrable f)
    (ξ : (ℝ ∙ v)ᗮ) :
    𝓕 (fun y : (ℝ ∙ v)ᗮ ↦ ∫ t : ℝ, f ((y : E) + t • v)) ξ = 𝓕 f (ξ : E) := by
  let g : E → ℂ := fun x ↦ Real.fourierChar (-⟪x, (ξ : E)⟫) • f x
  have hg : Integrable g := (Real.fourierIntegral_convergent_iff (ξ : E)).mpr hf
  have hi := ((measurePreserving_normalCoordinates hv).integrable_comp_emb
    (normalCoordinates hv).toHomeomorph.measurableEmbedding).mpr hg
  rw [Measure.volume_eq_prod] at hi
  have he (y : (ℝ ∙ v)ᗮ) (t : ℝ) :
      g (normalCoordinates hv (y, t)) = Real.fourierChar (-⟪y, ξ⟫) • f ((y : E) + t • v) := by
    simp only [g, normalCoordinates_apply, inner_add_left, inner_smul_left, conj_trivial,
      mem_orthogonal_singleton_iff_inner_right.mp ξ.2, mul_zero, add_zero]
    rfl
  rw [Real.fourier_eq, Real.fourier_eq]
  change _ = ∫ x, g x
  rw [← (measurePreserving_normalCoordinates hv).integral_comp
    (normalCoordinates hv).toHomeomorph.measurableEmbedding g, Measure.volume_eq_prod]
  rw [integral_prod (fun z : (ℝ ∙ v)ᗮ × ℝ ↦ g (normalCoordinates hv z)) hi]
  simp only [he, Circle.smul_def, integral_smul]

end NKBesicovitch.XRay
