/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Induction.PlateIntegral
public import NKBesicovitch.Grassmannian.FlagMeasure
public import NKBesicovitch.Operators.PlateRotation
public import NKBesicovitch.Operators.MixedNorm.MapProd
public import NKBesicovitch.Operators.XRay.Frame

/-!
# The plate-to-X-ray step of the induction

A lower-dimensional plate estimate applied to each frame X-ray transform
controls the higher-dimensional plate norm. The flag probability identity
and upper integral inequalities suffice without a measurability assumption
on either plate supremum. The lower-dimensional inputs remain in a fixed
ball, and the exact frame identity gives the spherical X-ray norm.
-/

public section

open MeasureTheory Set Metric NKBesicovitch.Grassmannian NKBesicovitch.XRay
open scoped ENNReal NNReal

namespace NKBesicovitch.Induction

variable {n m k : ℕ} (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ)

theorem plateMaximal_flagDirection_le {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hf : Measurable f) {δ : ℝ} (hδ : 0 < δ) (u : Rotations n) (V : Grassmannian m k) :
    plateMaximal δ f (flagDirection (norm_eq_of_mem_sphere v) b (u, V)) ≤
      (2 : ℝ≥0∞) ^ m * plateMaximal δ (frameXRay v b f u) V := by
  rw [flagDirection, plateMaximal_rotate]
  exact plateMaximal_normalLift_le (norm_eq_of_mem_sphere v) b V hδ
    (hf.comp (Unitary.linearIsometryEquiv u).continuous.measurable)

theorem eLpNorm_plateMaximal_le_frameXRay (hkn : k + 1 ≤ n) (hkm : k ≤ m)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : Measurable f) {δ : ℝ} (hδ : 0 < δ)
    {q r : ℝ≥0∞} (hq : q ≠ 0) (hqfin : q ≠ ∞) (A : ℝ≥0)
    (hbound : ∀ u : Rotations n, eLpNorm (plateMaximal δ (frameXRay v b f u)) q
      (probability hkm) ≤ A * eLpNorm (frameXRay v b f u) r volume) :
    eLpNorm (plateMaximal δ f) q (probability hkn) ≤
      (((2 : ℝ≥0) ^ m * A : ℝ≥0) : ℝ≥0∞) *
        eLpNorm (fun u ↦ eLpNorm (frameXRay v b f u) r volume) q (Rotations.probability n) := by
  have hmp := measurePreserving_flagDirection hkn hkm (norm_eq_of_mem_sphere v) b
  have hmap : eLpNorm (plateMaximal δ f) q (probability hkn) ≤
      eLpNorm (plateMaximal δ f ∘ flagDirection (norm_eq_of_mem_sphere v) b) q
        ((Rotations.probability n).prod (probability hkm)) := by
    rw [← hmp.map_eq]
    exact eLpNorm_map_le _ _ hq hqfin
  apply hmap.trans ((eLpNorm_prod_le_iterated _ hq hqfin).trans ?_)
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul' (c := (2 : ℝ≥0) ^ m * A)
  apply ae_of_all
  intro u
  simp only [enorm_eq_self, Function.comp_apply]
  have hpoint : ∀ᵐ V ∂probability hkm,
      ‖plateMaximal δ f (flagDirection (norm_eq_of_mem_sphere v) b (u, V))‖ₑ ≤
        (((2 : ℝ≥0) ^ m : ℝ≥0) : ℝ≥0∞) * ‖plateMaximal δ (frameXRay v b f u) V‖ₑ := by
    apply ae_of_all
    intro V
    simpa only [enorm_eq_self, ENNReal.coe_pow, ENNReal.coe_ofNat] using
      plateMaximal_flagDirection_le v b hf hδ u V
  apply (eLpNorm_le_mul_eLpNorm_of_ae_le_mul' hpoint q).trans
  simpa only [ENNReal.coe_mul, mul_assoc] using mul_le_mul_right (hbound u)
    (((2 : ℝ≥0) ^ m : ℝ≥0) : ℝ≥0∞)

include v b in
/-- A uniform lower-dimensional plate bound gives a bound by the spherical X-ray mixed norm. -/
theorem eLpNorm_plateMaximal_le_sphericalXRay (hkn : k + 1 ≤ n) (hkm : k ≤ m)
    {δ R : ℝ} (hδ : 0 < δ) {q r : ℝ≥0∞} (hq : q ≠ 0) (hqfin : q ≠ ∞)
    (hr : r ≠ 0) (hrfin : r ≠ ∞) (A : ℝ≥0)
    (hbound : ∀ g : EuclideanSpace ℝ (Fin m) → ℝ≥0∞, Measurable g →
      Function.support g ⊆ closedBall 0 R →
        eLpNorm (plateMaximal δ g) q (probability hkm) ≤ A * eLpNorm g r volume)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : Measurable f)
    (hs : Function.support f ⊆ closedBall 0 R) :
    eLpNorm (plateMaximal δ f) q (probability hkn) ≤
      (((2 : ℝ≥0) ^ m * A : ℝ≥0) : ℝ≥0∞) *
        ((((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere univ)⁻¹) ^ (1 / q.toReal) *
          sphericalXRayNorm f q r) := by
  have h := eLpNorm_plateMaximal_le_frameXRay v b hkn hkm hf hδ hq hqfin A
    (fun u ↦ hbound _ (measurable_frameXRay v b hf u)
      (support_frameXRay_subset_closedBall v b hs u))
  rwa [eLpNorm_eLpNorm_frameXRay v b hf hr hrfin q] at h

end NKBesicovitch.Induction
