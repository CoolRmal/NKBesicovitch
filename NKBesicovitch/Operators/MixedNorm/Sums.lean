/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.MixedNorm.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Countable sums in nonnegative mixed norms

Monotone convergence extends the finite triangle inequality to countable
sums. The statement allows infinite norms and does not need a separate
summability assumption.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace NKBesicovitch

variable {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Countable ι]
    {μ : Measure X} {ν : Measure Y} {p q r : ℝ≥0∞}

theorem eLpNorm_iSup_directed {f : ι → X → ℝ≥0∞} (hf : ∀ i, Measurable (f i))
    (hd : Directed (· ≤ ·) f) (hp : p ≠ 0) (hpfin : p ≠ ∞) :
    eLpNorm (fun x ↦ ⨆ i, f i x) p μ = ⨆ i, eLpNorm (f i) p μ := by
  have hp0 := ENNReal.toReal_pos hp hpfin
  have hpow (x : X) : (⨆ i, f i x) ^ p.toReal = ⨆ i, f i x ^ p.toReal :=
    (ENNReal.orderIsoRpow p.toReal hp0).map_iSup _
  have hd' : Directed (· ≤ ·) (fun i x ↦ f i x ^ p.toReal) := by
    intro i j
    obtain ⟨k, hi, hj⟩ := hd i j
    exact ⟨k, fun x ↦ ENNReal.rpow_le_rpow (hi x) hp0.le,
      fun x ↦ ENNReal.rpow_le_rpow (hj x) hp0.le⟩
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hpfin, enorm_eq_self, hpow]
  rw [lintegral_iSup_directed_of_measurable (fun i ↦ (hf i).pow_const _) hd']
  exact (ENNReal.orderIsoRpow (1 / p.toReal) (one_div_pos.mpr hp0)).map_iSup _

theorem eLpNorm_tsum_le {f : ι → X → ℝ≥0∞} (hf : ∀ i, Measurable (f i))
    (hp : 1 ≤ p) (hpfin : p ≠ ∞) :
    eLpNorm (fun x ↦ ∑' i, f i x) p μ ≤ ∑' i, eLpNorm (f i) p μ := by
  classical
  have hmono : Monotone (fun s : Finset ι ↦ fun x ↦ ∑ i ∈ s, f i x) :=
    fun _ _ h x ↦ Finset.sum_le_sum_of_subset h
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  rw [eLpNorm_iSup_directed (fun s ↦ by fun_prop) hmono.directed_le
    (zero_lt_one.trans_le hp).ne' hpfin]
  apply iSup_le
  intro s
  have hsum := eLpNorm_sum_le (f := f) (s := s) (μ := μ)
    (fun i _ ↦ (hf i).aestronglyMeasurable) hp
  have heq : (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, f i := by
    funext x
    simp only [Finset.sum_apply]
  rw [heq]
  exact hsum.trans (le_iSup (fun t : Finset ι ↦ ∑ i ∈ t, eLpNorm (f i) p μ) s)

theorem mixedNorm_tsum_le [SFinite μ] {f : ι → X × Y → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hqfin : q ≠ ∞) (hrfin : r ≠ ∞) :
    mixedNorm (fun p ↦ ∑' i, f i p) q r μ ν ≤ ∑' i, mixedNorm (f i) q r μ ν := by
  calc
    _ ≤ eLpNorm (fun y ↦ ∑' i, eLpNorm (fun x ↦ f i (x, y)) r μ) q ν := by
      apply eLpNorm_mono_enorm
      intro y
      simp only [enorm_eq_self]
      exact eLpNorm_tsum_le (fun i ↦ (hf i).comp measurable_prodMk_right) hr hrfin
    _ ≤ _ := eLpNorm_tsum_le (fun i ↦ measurable_eLpNorm_fiber (hf i)
      (zero_lt_one.trans_le hr).ne' hrfin) hq hqfin

end NKBesicovitch
