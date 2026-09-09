/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Induction.TerminalSeries

/-!
# The terminal bound on signed affine-plane integrals

A plate deficit below one yields a measurable majorant of every signed
affine-plane integral in flag coordinates. Its joint `Lᵖ` norm is bounded
uniformly for Schwartz inputs supported in a fixed ball. The input may
be complex-valued; positivity is only needed later for passage to disk averages.
-/

public section

open MeasureTheory Submodule Set Metric NKBesicovitch.Grassmannian
open scoped SchwartzMap ENNReal NNReal

namespace NKBesicovitch.Induction

variable {m k : ℕ} [Nonempty (Fin m)]
  (v : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
  (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin (m + 1))))ᗮ)

/-- A subunit plate deficit yields a uniform measurable majorant for signed full-plane integrals. -/
theorem HasPlateEstimate.exists_affinePlane_majorant
    {hkm : k ≤ m} {α p : ℝ} (h : HasPlateEstimate hkm α p) (hα : α < 1) (hp : 2 ≤ p)
    (R : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ f : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ),
      Function.support (f : EuclideanSpace ℝ (Fin (m + 1)) → ℂ) ⊆ closedBall 0 R →
        ∃ M : Rotations (m + 1) × Grassmannian m k → ℝ≥0∞, Measurable M ∧
          eLpNorm M (ENNReal.ofReal p)
            ((Rotations.probability (m + 1)).prod (Grassmannian.probability hkm)) ≤
              C * eLpNorm f (ENNReal.ofReal p) volume ∧
          ∀ (z : Rotations (m + 1) × Grassmannian m k) (x : EuclideanSpace ℝ (Fin (m + 1))),
            ‖∫ w : (flagDirection (norm_eq_of_mem_sphere v) b z).val, f (x + w)‖ₑ ≤ M z := by
  obtain ⟨φ, hφ, houter, hbound⟩ := exists_lowFrequencyKernel
    (E := EuclideanSpace ℝ (Fin (m + 1)))
  obtain ⟨B, hB⟩ := h.exists_eLpNorm_plateMaximal_frame_series_le v b hα hp φ hφ (k + 1) R
  obtain ⟨D, hD⟩ := XRay.exists_enorm_integral_flag_le_dyadicFrameMajorant v b
    (show k < 2 * (k + 1) by omega) φ hφ houter hbound
  refine ⟨D * B, fun f hs ↦ ⟨fun z ↦ D * XRay.dyadicFrameMajorant v b φ (k + 1) f z,
    measurable_const.mul (XRay.measurable_dyadicFrameMajorant v b φ (k + 1) f), ?_, hD f⟩⟩
  have hm := eLpNorm_le_mul_eLpNorm_of_ae_le_mul' (μ :=
    (Rotations.probability (m + 1)).prod (Grassmannian.probability hkm))
    (f := fun z ↦ D * XRay.dyadicFrameMajorant v b φ (k + 1) f z)
    (g := XRay.dyadicFrameMajorant v b φ (k + 1) f) (c := D)
    (ae_of_all _ fun z ↦ le_rfl) (ENNReal.ofReal p)
  apply hm.trans
  simpa only [ENNReal.coe_mul, mul_assoc] using mul_le_mul_right (hB f hs) (D : ℝ≥0∞)

end NKBesicovitch.Induction
