/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.DiskPlaneBound
public import NKBesicovitch.Operators.DiskMeasurability
public import NKBesicovitch.Grassmannian.FlagMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-!
# Transferring affine-plane majorants to disk norms

For positive Schwartz inputs, the flag probability law transfers a joint
affine-plane majorant to the disk maximal norm on the Grassmannian.
-/

public section

open MeasureTheory Submodule Set Metric NKBesicovitch.Grassmannian
open scoped SchwartzMap ENNReal

namespace NKBesicovitch

variable {n m k : ℕ}

/-- A uniform signed flag-plane majorant bounds every positive Schwartz disk norm. -/
theorem eLpNorm_diskMaximal_le_of_flag_majorant (hkn : k + 1 ≤ n) (hkm : k ≤ m)
    (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℝ)) (hf : ∀ x, 0 ≤ f x)
    (M : Rotations n × Grassmannian m k → ℝ≥0∞)
    (hpoint : ∀ (z : Rotations n × Grassmannian m k) (x : EuclideanSpace ℝ (Fin n)),
      ‖∫ w : (flagDirection (norm_eq_of_mem_sphere v) b z).val, (f (x + w) : ℂ)‖ₑ ≤ M z)
    (p : ℝ≥0∞) :
    eLpNorm (diskMaximal (fun x ↦ ENNReal.ofReal (f x))) p (Grassmannian.probability hkn) ≤
      (volume (closedBall (0 : EuclideanSpace ℝ (Fin (k + 1))) 1))⁻¹ *
        eLpNorm M p ((Rotations.probability n).prod (Grassmannian.probability hkm)) := by
  let d := volume (closedBall (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)
  have hd : d⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr (measure_closedBall_pos volume _ zero_lt_one).ne'
  have hmeas := (lowerSemicontinuous_diskMaximal
    (ENNReal.continuous_ofReal.comp f.continuous).lowerSemicontinuous (k := k + 1)).measurable
  dsimp only [Function.comp_def] at hmeas
  rw [← eLpNorm_comp_measurePreserving (p := p) hmeas.aestronglyMeasurable
    (measurePreserving_flagDirection hkn hkm (norm_eq_of_mem_sphere v) b),
    ← ENNReal.coe_toNNReal hd]
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul'
  refine ae_of_all _ fun z ↦ ?_
  simp only [enorm_eq_self, Function.comp_apply, ENNReal.coe_toNNReal hd]
  apply iSup_le
  intro x
  apply (diskAverage_ofReal_le_enorm_integral f hf _ x).trans
  rw [mul_comm, ← div_eq_mul_inv]
  exact ENNReal.div_le_div_right (hpoint z x) d

end NKBesicovitch
