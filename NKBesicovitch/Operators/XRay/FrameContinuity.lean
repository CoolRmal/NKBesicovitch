/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.FourierFrame

/-!
# Joint continuity of signed frame integrals

Schwartz decay supplies one integrable majorant for every rotation and
transverse displacement. Dominated convergence therefore gives joint
continuity, which will make the weighted plate majorants jointly Borel.
-/

public section

open MeasureTheory Submodule Metric
open scoped SchwartzMap

namespace NKBesicovitch.XRay

variable {n m : ℕ} (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
  (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ)

private lemma norm_frameLineIntegrand_le_aux (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (u : Rotations n) (x : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    ‖f (Unitary.linearIsometryEquiv u
      (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (x, t)))‖ ≤
        (SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ 2 0 f) * (1 + t ^ 2)⁻¹ := by
  let y := Unitary.linearIsometryEquiv u
    (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (x, t))
  have hn : t ^ 2 ≤ ‖y‖ ^ 2 := by
    dsimp only [y]
    rw [LinearIsometryEquiv.norm_map, normalCoordinatesWithBasis_apply]
    have he := norm_normalCoordinates_sq (norm_eq_of_mem_sphere v) (b x) t
    rw [normalCoordinates_apply] at he
    nlinarith [sq_nonneg ‖b x‖]
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)]
  calc
    _ = ‖f y‖ + t ^ 2 * ‖f y‖ := by ring
    _ ≤ _ := add_le_add (f.norm_le_seminorm ℝ y)
      ((mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans (f.norm_pow_mul_le_seminorm ℝ 2 y))

/-- Signed line integrals of Schwartz inputs are jointly continuous in frame and displacement. -/
theorem continuous_frameLineIntegral (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    Continuous (fun z : Rotations n × EuclideanSpace ℝ (Fin m) ↦
      frameLineIntegral v b f z.1 z.2) := by
  apply continuous_of_dominated
    (bound := fun t : ℝ ↦
      (SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ 2 0 f) * (1 + t ^ 2)⁻¹)
  · intro z
    exact (integrable_frameLineIntegrand v b f z.1 z.2).aestronglyMeasurable
  · intro z
    exact ae_of_all _ (norm_frameLineIntegrand_le_aux v b f z.1 z.2)
  · exact integrable_inv_one_add_sq.const_mul _
  · refine ae_of_all _ fun t ↦ f.continuous.comp ?_
    exact (continuous_subtype_val.comp continuous_fst).clm_apply
      ((normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b).continuous.comp
        (continuous_snd.prodMk continuous_const))

end NKBesicovitch.XRay
