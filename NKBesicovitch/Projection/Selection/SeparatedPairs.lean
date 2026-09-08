/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic.Finiteness
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Many separated pairs in a measurable time set

Removing a radius-`r` interval around the first time loses at most `2r`
in the second variable. Tonelli gives the lower bound for the surviving
pair measure. At separation `|I|/100`, at least half of `|I|²` remains.
The separation relation is jointly measurable for Borel families of time
sets and measurable, family-dependent separation radii.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection

/-- Ordered pairs of times in `I` at distance at least `r`. -/
def separatedPairs (I : Set ℝ) (r : ℝ) : Set (ℝ × ℝ) :=
  (I ×ˢ I) ∩ {p | r ≤ dist p.1 p.2}

theorem measurableSet_separatedPairs {I : Set ℝ} (hI : MeasurableSet I) (r : ℝ) :
    MeasurableSet (separatedPairs I r) :=
  (hI.prod hI).inter (measurableSet_le measurable_const (by fun_prop))

theorem measurableSet_separatedPairs_family {X : Type*} [MeasurableSpace X]
    {I : Set (X × ℝ)} (hI : MeasurableSet I) {r : X → ℝ} (hr : Measurable r) :
    MeasurableSet {p : X × (ℝ × ℝ) | p.2 ∈ separatedPairs {t | (p.1, t) ∈ I} (r p.1)} :=
  ((hI.preimage (measurable_fst.prodMk measurable_snd.fst)).inter
    (hI.preimage (measurable_fst.prodMk measurable_snd.snd))).inter
      (measurableSet_le (hr.comp measurable_fst) (measurable_snd.fst.dist measurable_snd.snd))

theorem volume_separatedPairs {I : Set ℝ} (hI : MeasurableSet I) (r : ℝ) :
    volume (separatedPairs I r) = ∫⁻ a in I, volume (I \ Metric.ball a r) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_separatedPairs hI r)]
  have h : (fun a ↦ volume (Prod.mk a ⁻¹' separatedPairs I r)) =
      I.indicator (fun a ↦ volume (I \ Metric.ball a r)) := by
    funext a
    by_cases ha : a ∈ I
    · rw [Set.indicator_of_mem ha]
      congr 1
      ext b
      simp only [separatedPairs, mem_preimage, mem_inter_iff, mem_prod, mem_ofPred_eq,
        ha, true_and, mem_sdiff, Metric.mem_ball, not_lt, dist_comm]
    · rw [Set.indicator_of_notMem ha]
      simp [separatedPairs, ha]
  rw [h, lintegral_indicator hI]

theorem volume_separatedPairs_lower {I : Set ℝ} (hI : MeasurableSet I)
    {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal ((volume I).toReal - 2 * r) * volume I ≤ volume (separatedPairs I r) := by
  rw [volume_separatedPairs hI, ← setLIntegral_const]
  apply lintegral_mono
  intro a
  apply ENNReal.ofReal_le_of_le_toReal
  have h := le_measureReal_sdiff (μ := volume) (s₁ := I) (s₂ := Metric.ball a r)
    (by rw [Real.volume_ball]; finiteness)
  simpa only [Real.volume_real_ball hr, measureReal_def] using h

theorem half_square_le_volume_separatedPairs {I : Set ℝ} (hI : MeasurableSet I)
    (hIfin : volume I ≠ ∞) :
    ENNReal.ofReal ((volume I).toReal ^ 2 / 2) ≤
      volume (separatedPairs I ((volume I).toReal / 100)) := by
  have hL : 0 ≤ (volume I).toReal := ENNReal.toReal_nonneg
  refine le_trans ?_ (volume_separatedPairs_lower hI (by positivity))
  conv_rhs => arg 2; rw [← ENNReal.ofReal_toReal hIfin]
  rw [← ENNReal.ofReal_mul (by linarith)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (volume I).toReal])

theorem volume_separatedPairs_le (I : Set ℝ) (r : ℝ) :
    volume (separatedPairs I r) ≤ volume I ^ 2 := by
  calc
    _ ≤ volume (I ×ˢ I) := measure_mono inter_subset_left
    _ = _ := by rw [Measure.volume_eq_prod, Measure.prod_prod, pow_two]

end NKBesicovitch.Projection.Selection
