/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Grassmannian.NormalLiftCoordinates
public import NKBesicovitch.Grassmannian.FlagMeasure
public import NKBesicovitch.Operators.XRay.FourierFrame

/-!
# Signed full-plane integration in flag coordinates

Intrinsic volume on a lifted and rotated plane is the product of the original
plane volume and arclength. Schwartz integrability justifies signed Fubini
before any absolute value is taken. The normal component of a translation
disappears from the full line integral.
-/

public section

open MeasureTheory NKBesicovitch.Grassmannian
open scoped SchwartzMap

namespace NKBesicovitch.XRay

variable {n m k : ℕ} (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
  (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ)

/-- Signed integration on a full flag plane equals lower-dimensional integration of the X-ray. -/
theorem integral_flagDirection_eq (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (u : Rotations n) (V : Grassmannian m k) (a : EuclideanSpace ℝ (Fin m) × ℝ) :
    (∫ z : (flagDirection (norm_eq_of_mem_sphere v) b (u, V)).val,
      f (Unitary.linearIsometryEquiv u
        (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b a) + z)) =
      ∫ y : V.val, frameLineIntegral v b f u (a.1 + y) := by
  let W := flagDirection (norm_eq_of_mem_sphere v) b (u, V)
  let i : WithLp 2 (V.val × ℝ) ≃ₗᵢ[ℝ] W.val :=
    (normalLiftCoordinates (norm_eq_of_mem_sphere v) b V).trans
      ((Unitary.linearIsometryEquiv u).submoduleMap
        (normalLift (norm_eq_of_mem_sphere v) b V).val)
  let c : (V.val × ℝ) ≃L[ℝ] W.val :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ V.val ℝ).symm.trans i.toContinuousLinearEquiv
  have hc : MeasurePreserving c volume volume :=
    i.measurePreserving.comp (WithLp.volume_preserving_toLp V.val ℝ)
  let a' := Unitary.linearIsometryEquiv u
    (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b a)
  let F := SchwartzMap.compCLMOfAntilipschitz ℂ (g := fun z : W.val ↦ a' + z)
    ((Function.HasTemperateGrowth.const a').add W.val.subtypeL.hasTemperateGrowth)
    (((IsometryEquiv.addLeft a').isometry.comp W.val.subtypeₗᵢ.isometry).antilipschitz) f
  have hF : Integrable (fun z : W.val ↦ f (a' + z)) volume := F.integrable
  rw [← hc.integral_comp c.toHomeomorph.measurableEmbedding (fun z ↦ f (a' + z)),
    Measure.volume_eq_prod, integral_prod _ (by
      simpa only [Measure.volume_eq_prod, Function.comp_def] using
        hc.integrable_comp_of_integrable hF)]
  apply integral_congr_ae
  filter_upwards with y
  change (∫ t : ℝ, f (Unitary.linearIsometryEquiv u
    (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b a) +
      Unitary.linearIsometryEquiv u
        (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (y, t)))) = _
  simp_rw [← map_add]
  exact integral_add_left_eq_self (fun t : ℝ ↦ f (Unitary.linearIsometryEquiv u
    (normalCoordinatesWithBasis (norm_eq_of_mem_sphere v) b (a.1 + y, t)))) a.2

end NKBesicovitch.XRay
