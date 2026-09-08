/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.SeparatedPairs

/-!
# Removing neighborhoods of finitely many base times

Requiring distance at least `r` from each of `k` specified times removes
at most `2kr` of time measure. The remaining set is jointly measurable
when the time set, base times, and radius vary measurably.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection

variable {ι : Type*}

/-- Times in `I` separated from all the finitely many specified base times. -/
def separatedTimes (I : Set ℝ) (a : ι → ℝ) (F : Finset ι) (r : ℝ) : Set ℝ :=
  I ∩ ⋂ i ∈ F, {t | r ≤ dist t (a i)}

theorem mem_separatedTimes {I : Set ℝ} {a : ι → ℝ} {F : Finset ι} {r t : ℝ} :
    t ∈ separatedTimes I a F r ↔ t ∈ I ∧ ∀ i ∈ F, r ≤ dist t (a i) := by
  simp [separatedTimes]

theorem separatedTimes_eq_sdiff (I : Set ℝ) (a : ι → ℝ) (F : Finset ι) (r : ℝ) :
    separatedTimes I a F r = I \ ⋃ i ∈ F, Metric.ball (a i) r := by
  ext t
  simp [separatedTimes, Metric.mem_ball, not_lt]

theorem measurableSet_separatedTimes {I : Set ℝ} (hI : MeasurableSet I)
    (a : ι → ℝ) (F : Finset ι) (r : ℝ) : MeasurableSet (separatedTimes I a F r) :=
  hI.inter (F.measurableSet_biInter fun _ _ ↦
    measurableSet_le measurable_const (by fun_prop))

theorem measurableSet_separatedTimes_family {X : Type*} [MeasurableSpace X]
    {I : Set (X × ℝ)} (hI : MeasurableSet I) {a : X → ι → ℝ} (F : Finset ι)
    (ha : ∀ i ∈ F, Measurable (fun x ↦ a x i)) {r : X → ℝ} (hr : Measurable r) :
    MeasurableSet {p : X × ℝ | p.2 ∈ separatedTimes {t | (p.1, t) ∈ I} (a p.1) F (r p.1)} := by
  have h : MeasurableSet (I ∩ ⋂ i ∈ F, {p : X × ℝ | r p.1 ≤ dist p.2 (a p.1 i)}) :=
    hI.inter (F.measurableSet_biInter fun i hi ↦ measurableSet_le (hr.comp measurable_fst)
      (measurable_snd.dist ((ha i hi).comp measurable_fst)))
  convert h using 1
  ext p
  simp [separatedTimes]

theorem volume_separatedTimes_lower (I : Set ℝ) (a : ι → ℝ) (F : Finset ι)
    {r : ℝ} (hr : 0 ≤ r) :
    (volume I).toReal - 2 * r * F.card ≤ (volume (separatedTimes I a F r)).toReal := by
  have hbad : volume (⋃ i ∈ F, Metric.ball (a i) r) ≤ F.card * ENNReal.ofReal (2 * r) := by
    simpa only [Real.volume_ball, Finset.sum_const, nsmul_eq_mul] using
      measure_biUnion_finset_le (μ := (volume : Measure ℝ)) F (fun i ↦ Metric.ball (a i) r)
  have hfin : volume (⋃ i ∈ F, Metric.ball (a i) r) ≠ ∞ :=
    ne_top_of_le_ne_top (by finiteness) hbad
  have hbadReal : (volume (⋃ i ∈ F, Metric.ball (a i) r)).toReal ≤ 2 * r * F.card := by
    have h := ENNReal.toReal_mono (by finiteness) hbad
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * r)] at h
    simpa only [mul_comm] using h
  rw [separatedTimes_eq_sdiff]
  exact (sub_le_sub_left hbadReal _).trans (le_measureReal_sdiff hfin)

end NKBesicovitch.Projection.Selection
