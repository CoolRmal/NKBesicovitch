/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.Restricted
public import NKBesicovitch.Operators.XRay.FiberBlocks

/-!
# Restricted mixed norms on families with comparable parallel fibers

The fiber-size powers cancel between the restricted X-ray estimate and
the mixed-norm indicator bound. The resulting estimate is independent of
the fiber scale, including for line families of volume zero.
-/

public section

open MeasureTheory Set Bornology NKBesicovitch.Projection
open scoped ENNReal

namespace NKBesicovitch.XRay

private lemma fiber_scale_cancel {a β : ℝ} (ha : 0 < a) :
    (a / 2) ^ (β - 2) * a ^ (2 - β) = 2 ^ (2 - β) := by
  rw [Real.div_rpow ha.le (by norm_num), div_mul_eq_mul_div, ← Real.rpow_add ha]
  have he : β - 2 + (2 - β) = 0 := by ring
  rw [he, Real.rpow_zero, one_div, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

theorem mixedNorm_fiberBlock_rpow_le_of_restricted {m K : ℕ} {β C V a r : ℝ}
    (hβ : 1 < β) (hβ2 : β ≤ 2) (hK : 0 < K) (hC : 0 ≤ C) (hV : 0 ≤ V)
    {F : Set (Line m)} (hF : MeasurableSet F) (hFb : IsBounded F)
    (ha : 0 < a) (hr : 0 ≤ r)
    (hbound : r ^ K * (volume (fiberBlock F a)).toReal ≤
      C * (parallelMultiplicity (fiberBlock F a)).toReal ^ (2 - β) * V ^ β) :
    ENNReal.ofReal (r ^ K) *
      mixedNorm ((fiberBlock F a).indicator (fun _ ↦ (1 : ℝ≥0∞)))
        (ENNReal.ofReal K) (ENNReal.ofReal ((K : ℝ) / (β - 1))) volume volume ^ (K : ℝ) ≤
          ENNReal.ofReal (2 ^ (2 - β) * C * V ^ β) := by
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
  have hden : 0 < β - 1 := by linarith
  have hquot : (K : ℝ) / ((K : ℝ) / (β - 1)) = β - 1 := by field_simp
  have hnorm := mixedNorm_fiberBlock_rpow_le hF hKr (div_pos hKr hden)
    (by rw [hquot]; linarith) ha
  rw [hquot, show β - 1 - 1 = β - 2 by ring] at hnorm
  have hM : (parallelMultiplicity (fiberBlock F a)).toReal ≤ a := by
    simpa only [ENNReal.toReal_ofReal ha.le] using ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (parallelMultiplicity_fiberBlock_le F a)
  have hmass : r ^ K * (volume (fiberBlock F a)).toReal ≤ C * a ^ (2 - β) * V ^ β :=
    hbound.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow ENNReal.toReal_nonneg hM (by linarith)) hC) (Real.rpow_nonneg hV _))
  have hfin : volume (fiberBlock F a) ≠ ∞ :=
    (hFb.subset (fiberBlock_subset F a)).measure_lt_top.ne
  have hmass' : ENNReal.ofReal (r ^ K) * volume (fiberBlock F a) ≤
      ENNReal.ofReal (C * a ^ (2 - β) * V ^ β) := by
    simpa only [ENNReal.ofReal_mul (pow_nonneg hr K), ENNReal.ofReal_toReal hfin] using
      ENNReal.ofReal_le_ofReal hmass
  calc
    _ ≤ ENNReal.ofReal (r ^ K) *
        (ENNReal.ofReal ((a / 2) ^ (β - 2)) * volume (fiberBlock F a)) :=
      mul_le_mul_right hnorm _
    _ = ENNReal.ofReal ((a / 2) ^ (β - 2)) *
        (ENNReal.ofReal (r ^ K) * volume (fiberBlock F a)) := by ring
    _ ≤ ENNReal.ofReal ((a / 2) ^ (β - 2)) *
        ENNReal.ofReal (C * a ^ (2 - β) * V ^ β) := mul_le_mul_right hmass' _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      calc
        _ = ((a / 2) ^ (β - 2) * a ^ (2 - β)) * C * V ^ β := by ring
        _ = _ := by rw [fiber_scale_cancel ha]

/-- A mixed-norm bound uniform over all parallel-fiber scales. -/
theorem exists_restricted_mixedNorm_fiberBlock_bound (m : ℕ) [Nonempty (Fin m)] {β : ℝ}
    (hβ : projectionExponent < β) (hβ2 : β ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, 2 < K ∧
      ∀ E : Set (EuclideanSpace ℝ (Fin m) × ℝ), MeasurableSet E → volume E ≠ ∞ →
        ∀ F : Set (Line m), MeasurableSet F → IsBounded F → ∀ a r : ℝ,
          0 < a → 0 < r → r ≤ 1 →
          (∀ g ∈ F, ENNReal.ofReal r ≤ localXRay (E.indicator (fun _ ↦ (1 : ℝ≥0∞))) g.2 g.1) →
          ENNReal.ofReal (r ^ K) *
            mixedNorm ((fiberBlock F a).indicator (fun _ ↦ (1 : ℝ≥0∞)))
              (ENNReal.ofReal K) (ENNReal.ofReal ((K : ℝ) / (β - 1))) volume volume ^ (K : ℝ) ≤
                ENNReal.ofReal (C * (volume E).toReal ^ β) := by
  obtain ⟨C, hC, K, hK, hbound⟩ := exists_restricted_bound m hβ hβ2
  refine ⟨2 ^ (2 - β) * C, by positivity, K, hK, ?_⟩
  intro E hE hEfin F hF hFb a r ha hr hr1 hrich
  exact mixedNorm_fiberBlock_rpow_le_of_restricted (projectionExponent_mem.1.trans hβ)
    hβ2 (by omega) hC.le ENNReal.toReal_nonneg hF hFb ha hr.le
    (hbound E hE hEfin (fiberBlock F a) (measurableSet_fiberBlock hF a)
      (hFb.subset (fiberBlock_subset F a)) r hr hr1 (fun g hg ↦ hrich g hg.1))

end NKBesicovitch.XRay
