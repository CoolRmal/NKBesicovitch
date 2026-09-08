/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.InputSums
public import NKBesicovitch.Operators.Interpolation.InputDyadic
public import NKBesicovitch.Operators.Interpolation.InputSeries
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Passing from indicator bounds to normalized input bounds

The indicator estimate with measure exponent `e` controls every Borel
input supported in a fixed set of finite measure with `L^p` norm at most
one, provided `p * e > 1`. The two input-level sums are handled together
as a countable weighted decomposition.
-/

public section

open MeasureTheory Set NKBesicovitch.Projection
open scoped ENNReal NNReal

namespace NKBesicovitch.XRay

variable {m : ℕ} {f : EuclideanSpace ℝ (Fin m) × ℝ → ℝ≥0∞}
    {Ξ : Set (EuclideanSpace ℝ (Fin m))} {q r : ℝ≥0∞}

theorem mixedNorm_localXRay_le_superlevel_sums (hf : Measurable f)
    (hΞ : MeasurableSet Ξ) (hq : 1 ≤ q) (hr : 1 ≤ r) (hqfin : q ≠ ∞) (hrfin : r ≠ ∞)
    {C : ℝ≥0∞} {e : ℝ}
    (hbound : ∀ t : ℝ, 0 < t → mixedNorm ((Prod.snd ⁻¹' Ξ).indicator
      (fun g : Line m ↦ localXRay ({z | ENNReal.ofReal t ≤ f z}.indicator
        (fun _ ↦ (1 : ℝ≥0∞))) g.2 g.1)) q r volume volume ≤
          C * volume {z | ENNReal.ofReal t ≤ f z} ^ e) :
    mixedNorm ((Prod.snd ⁻¹' Ξ).indicator
      (fun g : Line m ↦ localXRay f g.2 g.1)) q r volume volume ≤
        C * ((∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j) *
          volume {z | ENNReal.ofReal ((1 / 2 : ℝ) ^ j / 2) ≤ f z} ^ e) +
            ∑' j : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (j + 1)) *
              volume {z | ENNReal.ofReal ((2 : ℝ) ^ j) ≤ f z} ^ e) := by
  let w : ℕ ⊕ ℕ → ℝ≥0 := Sum.elim
    (fun j ↦ Real.toNNReal ((1 / 2 : ℝ) ^ j)) (fun j ↦ Real.toNNReal ((2 : ℝ) ^ (j + 1)))
  let t : ℕ ⊕ ℕ → ℝ := Sum.elim (fun j ↦ (1 / 2 : ℝ) ^ j / 2) (fun j ↦ (2 : ℝ) ^ j)
  have ht (i : ℕ ⊕ ℕ) : 0 < t i := by cases i <;> dsimp [t] <;> positivity
  have hcover (z : EuclideanSpace ℝ (Fin m) × ℝ) : f z ≤ ∑' i, (w i : ℝ≥0∞) *
      {z | ENNReal.ofReal (t i) ≤ f z}.indicator (fun _ ↦ (1 : ℝ≥0∞)) z := by
    rw [ENNReal.summable.tsum_sum ENNReal.summable]
    exact le_dyadic_superlevel_sums f z
  apply (mixedNorm_localXRay_le_tsum (fun i ↦ measurable_const.indicator
    (measurableSet_le measurable_const hf)) w hcover hΞ hq hr hqfin hrfin).trans
  calc
    _ ≤ ∑' i, C * ((w i : ℝ≥0∞) * volume {z | ENNReal.ofReal (t i) ≤ f z} ^ e) := by
      apply ENNReal.tsum_le_tsum
      intro i
      rw [mul_left_comm]
      exact mul_le_mul_right (hbound (t i) (ht i)) _
    _ = _ := by
      rw [ENNReal.tsum_mul_left, ENNReal.summable.tsum_sum ENNReal.summable]
      rfl

theorem exists_normalized_bound_of_indicator {K : Set (EuclideanSpace ℝ (Fin m) × ℝ)}
    (hKfin : volume K ≠ ∞) (hΞ : MeasurableSet Ξ)
    (hq : 1 ≤ q) (hr : 1 ≤ r) (hqfin : q ≠ ∞) (hrfin : r ≠ ∞)
    {C p e : ℝ} (hC : 0 < C) (hp : 0 < p) (he : 0 < e) (hpe : 1 < p * e)
    (hbound : ∀ E : Set (EuclideanSpace ℝ (Fin m) × ℝ), MeasurableSet E → E ⊆ K →
      mixedNorm ((Prod.snd ⁻¹' Ξ).indicator
        (fun g : Line m ↦ localXRay (E.indicator (fun _ ↦ (1 : ℝ≥0∞))) g.2 g.1))
          q r volume volume ≤ ENNReal.ofReal C * volume E ^ e) :
    ∃ D : ℝ, 0 < D ∧ ∀ f : EuclideanSpace ℝ (Fin m) × ℝ → ℝ≥0∞,
      Measurable f → Function.support f ⊆ K → eLpNorm f (ENNReal.ofReal p) volume ≤ 1 →
        mixedNorm ((Prod.snd ⁻¹' Ξ).indicator
          (fun g : Line m ↦ localXRay f g.2 g.1)) q r volume volume ≤ ENNReal.ofReal D := by
  obtain ⟨D, hD, hsum⟩ := exists_input_level_sum_constant hKfin hp he hpe
  refine ⟨C * D, mul_pos hC hD, fun f hf hsupport hnorm ↦ ?_⟩
  have hlevel (t : ℝ) (ht : 0 < t) : {z | ENNReal.ofReal t ≤ f z} ⊆ K := by
    intro z hz
    exact hsupport ((ENNReal.ofReal_pos.mpr ht).trans_le hz).ne'
  have h := mixedNorm_localXRay_le_superlevel_sums hf hΞ hq hr hqfin hrfin
    (fun t ht ↦ hbound _ (measurableSet_le measurable_const hf) (hlevel t ht))
  exact h.trans ((mul_le_mul_right (hsum f hf hsupport hnorm) _).trans_eq
    (ENNReal.ofReal_mul hC.le).symm)

end NKBesicovitch.XRay
