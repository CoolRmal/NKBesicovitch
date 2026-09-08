/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.SchwartzLine
public import NKBesicovitch.Geometry.SphereRotations
public import NKBesicovitch.Operators.Fourier.Plancherel

/-!
# Signed X-ray integrals in a fixed orthogonal frame

Ambient rotation and an orthonormal basis identify all displacement fibers
with one Euclidean space. Signed integration preserves the Schwartz class,
and the frame Fourier transform is the ambient transform on the rotated
normal hyperplane. This formulation permits integration over Haar rotations.
-/

@[expose] public section

open MeasureTheory Submodule Metric
open scoped SchwartzMap FourierTransform ENNReal

namespace NKBesicovitch.XRay

variable {n m : ℕ} (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
  (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ)

/-- The signed arclength integral in a rotated orthonormal frame. -/
noncomputable def frameLineIntegral (f : EuclideanSpace ℝ (Fin n) → ℂ) (u : Rotations n)
    (x : EuclideanSpace ℝ (Fin m)) : ℂ :=
  ∫ t : ℝ, f (Unitary.linearIsometryEquiv u
    (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (x, t)))

theorem measurable_frameLineIntegral {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf : Measurable f) :
    Measurable (fun z : Rotations n × EuclideanSpace ℝ (Fin m) ↦
      frameLineIntegral v b f z.1 z.2) := by
  have hm : Measurable (fun z : (Rotations n × EuclideanSpace ℝ (Fin m)) × ℝ ↦
      f (Unitary.linearIsometryEquiv z.1.1
        (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (z.1.2, z.2)))) :=
    hf.comp ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).clm_apply
      ((normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b).continuous.comp
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd))).measurable
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem fourier_frameLineIntegral {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : Integrable f)
    (u : Rotations n) (ξ : EuclideanSpace ℝ (Fin m)) :
    𝓕 (frameLineIntegral v b f u) ξ =
      𝓕 f (Unitary.linearIsometryEquiv u (b ξ : EuclideanSpace ℝ (Fin n))) := by
  have hi : Integrable (f ∘ Unitary.linearIsometryEquiv u) :=
    (Unitary.linearIsometryEquiv u).measurePreserving.integrable_comp_of_integrable hf
  have he : frameLineIntegral v b f u =
      (fun y : (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ ↦
        ∫ t : ℝ, (f ∘ Unitary.linearIsometryEquiv u)
          ((y : EuclideanSpace ℝ (Fin n)) + t • (v : EuclideanSpace ℝ (Fin n)))) ∘ b := by
    funext x
    simp only [frameLineIntegral, normalCoordinatesWithBasis_apply, Function.comp_apply]
  rw [he, Real.fourier_comp_linearIsometry, fourier_lineIntegral (norm_eq_of_mem_sphere v) hi,
    Real.fourier_comp_linearIsometry]

theorem exists_schwartz_frameLineIntegral (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (u : Rotations n) :
    ∃ g : 𝓢(EuclideanSpace ℝ (Fin m), ℂ), ∀ x, g x = frameLineIntegral v b f u x := by
  let F := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (Unitary.linearIsometryEquiv u).toContinuousLinearEquiv f
  obtain ⟨g, hg⟩ := exists_schwartz_lineIntegral (norm_eq_of_mem_sphere v) F
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ b.toContinuousLinearEquiv g, ?_⟩
  intro x
  simpa only [F, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    LinearIsometryEquiv.coe_coe, frameLineIntegral, normalCoordinatesWithBasis_apply] using hg (b x)

theorem lintegral_enorm_sq_frameLineIntegral (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (u : Rotations n) :
    (∫⁻ x, ‖frameLineIntegral v b f u x‖ₑ ^ 2) =
      ∫⁻ ξ, ‖𝓕 f (Unitary.linearIsometryEquiv u (b ξ : EuclideanSpace ℝ (Fin n)))‖ₑ ^ 2 := by
  obtain ⟨g, hg⟩ := exists_schwartz_frameLineIntegral v b f u
  have he : (g : EuclideanSpace ℝ (Fin m) → ℂ) = frameLineIntegral v b f u := funext hg
  simpa only [SchwartzMap.fourier_coe, he, fourier_frameLineIntegral v b f.integrable]
    using (lintegral_enorm_sq_fourier g).symm

end NKBesicovitch.XRay
