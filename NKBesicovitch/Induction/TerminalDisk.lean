/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Induction.TerminalPlane
public import NKBesicovitch.Operators.DiskFlagBound

/-!
# The terminal disk estimate for positive Schwartz inputs

Positivity bounds each normalized disk integral by the signed full-plane
majorant. The flag probability law transfers the joint bound to the
canonical Grassmannian norm. The constant depends on the fixed support radius.
-/

public section

open MeasureTheory Submodule Set Metric NKBesicovitch.Grassmannian
open scoped SchwartzMap ENNReal NNReal

namespace NKBesicovitch.Induction

variable {m k : ℕ} [Nonempty (Fin m)]

/-- A subunit deficit gives a disk estimate on supported positive Schwartz inputs. -/
theorem HasPlateEstimate.exists_eLpNorm_diskMaximal_schwartz_le
    {hkm : k ≤ m} {α p : ℝ} (h : HasPlateEstimate hkm α p) (hα : α < 1) (hp : 2 ≤ p)
    (R : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ f : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℝ), (∀ x, 0 ≤ f x) →
      Function.support (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) ⊆ closedBall 0 R →
        eLpNorm (diskMaximal (fun x ↦ ENNReal.ofReal (f x))) (ENNReal.ofReal p)
          (Grassmannian.probability (Nat.succ_le_succ hkm)) ≤
            C * eLpNorm f (ENNReal.ofReal p) volume := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) := ⟨by simp⟩
  let v : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
    ⟨EuclideanSpace.single 0 1, by simp⟩
  let b := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) m
    (v := (v : EuclideanSpace ℝ (Fin (m + 1))))
    (norm_pos_iff.mp (by rw [norm_eq_of_mem_sphere v]; norm_num))).repr.symm
  let d := volume (closedBall (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)
  have hd : d ≠ 0 := (measure_closedBall_pos volume _ zero_lt_one).ne'
  have hd' : d⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hd
  obtain ⟨B, hB⟩ := h.exists_affinePlane_majorant v b hα hp R
  refine ⟨d⁻¹.toNNReal * B, fun f hf hs ↦ ?_⟩
  let g := f.postcompCLM Complex.ofRealCLM
  have hg (x) : g x = (f x : ℂ) := rfl
  have hgs : Function.support (g : EuclideanSpace ℝ (Fin (m + 1)) → ℂ) ⊆ closedBall 0 R := by
    intro x hx
    exact hs (fun he ↦ hx (by rw [hg, he, Complex.ofReal_zero]))
  have hnorm : eLpNorm g (ENNReal.ofReal p) volume = eLpNorm f (ENNReal.ofReal p) volume :=
    eLpNorm_congr_norm_ae (ae_of_all _ fun x ↦ by rw [hg, Complex.norm_real])
  obtain ⟨M, -, hM, hpoint⟩ := hB g hgs
  simp only [hg] at hpoint
  have hn := eLpNorm_diskMaximal_le_of_flag_majorant (Nat.succ_le_succ hkm) hkm v b f hf M
    hpoint (ENNReal.ofReal p)
  apply hn.trans
  rw [hnorm] at hM
  simpa only [ENNReal.coe_mul, ENNReal.coe_toNNReal hd', mul_assoc]
    using mul_le_mul_right hM (d⁻¹ : ℝ≥0∞)

end NKBesicovitch.Induction
