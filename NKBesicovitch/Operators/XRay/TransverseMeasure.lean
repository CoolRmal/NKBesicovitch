/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.Transverse
public import NKBesicovitch.Operators.MixedNorm.VolumeComparison
public import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Comparing transverse and perpendicular line norms

Projection from a transverse hyperplane to the perpendicular displacement
space preserves each geometric line. Translating its parameter preserves
the full line integral. Since this projection is a contraction, the
perpendicular displacement norm is at most the transverse intercept norm.
This one-sided comparison suffices for transferring the X-ray bound.
-/

public section

open MeasureTheory Submodule
open scoped ENNReal InnerProductSpace

namespace NKBesicovitch.XRay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {v w : E}

theorem lintegral_transverseEquiv (hvw : ⟪v, w⟫_ℝ ≠ 0) (f : E → ℝ≥0∞)
    (x : (ℝ ∙ v)ᗮ) :
    (∫⁻ t : ℝ, f ((transverseEquiv hvw x : E) + t • w)) =
      ∫⁻ t : ℝ, f ((x : E) + t • w) := by
  obtain ⟨c, hc⟩ := mem_span_singleton.mp (sub_transverseEquiv_mem_span hvw x)
  have heq (t : ℝ) : (x : E) + t • w = (transverseEquiv hvw x : E) + (c + t) • w := by
    rw [add_smul, hc]
    abel
  simp_rw [heq]
  exact (lintegral_add_left_eq_self (fun t : ℝ ↦ f ((transverseEquiv hvw x : E) + t • w)) c).symm

variable [MeasurableSpace E] [BorelSpace E]

theorem eLpNorm_perpendicular_le_transverse (hvw : ⟪v, w⟫_ℝ ≠ 0)
    {f : E → ℝ≥0∞} (hf : Measurable f) (p : ℝ≥0∞) :
    eLpNorm (fun y : (ℝ ∙ w)ᗮ ↦ ∫⁻ t : ℝ, f ((y : E) + t • w)) p volume ≤
      eLpNorm (fun x : (ℝ ∙ v)ᗮ ↦ ∫⁻ t : ℝ, f ((x : E) + t • w)) p volume := by
  have hm : Measurable (fun z : (ℝ ∙ w)ᗮ × ℝ ↦ f ((z.1 : E) + z.2 • w)) :=
    hf.comp (by fun_prop)
  have h := eLpNorm_le_comp_of_norm_le (transverseEquiv hvw) (norm_transverseEquiv_le hvw)
    (hm.lintegral_prod_right' (ν := volume)) p
  simpa only [Function.comp_def, lintegral_transverseEquiv] using h

end NKBesicovitch.XRay
