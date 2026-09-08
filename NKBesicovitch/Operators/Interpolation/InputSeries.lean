/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.Interpolation.NormalizedLevels
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Summing the input superlevel measures

Small levels use only the measure of the fixed support. Large levels use
the normalized `L^p` bound. Their weighted `e`th powers are summable when
`p * e > 1`, the strict inequality used in strongification.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ≥0∞}

theorem sum_small_superlevel_measures_le {K : Set X} (hK : Function.support f ⊆ K)
    {e : ℝ} (he : 0 ≤ e) :
    (∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j) *
      μ {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ j / 2) ≤ f x} ^ e) ≤ 2 * μ K ^ e := by
  have hsub (j : ℕ) : {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ j / 2) ≤ f x} ⊆ K := by
    intro x hx
    apply hK
    exact ((by positivity : (0 : ℝ≥0∞) < ENNReal.ofReal ((1 / 2 : ℝ) ^ j / 2)).trans_le hx).ne'
  calc
    _ ≤ ∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j) * μ K ^ e :=
      ENNReal.tsum_le_tsum (fun j ↦
        mul_le_mul_right (ENNReal.rpow_le_rpow (measure_mono (hsub j)) he) _)
    _ = _ := by
      rw [ENNReal.tsum_mul_right]
      have hh : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num [one_div]
      simp_rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2), hh]
      rw [ENNReal.tsum_geometric_two]

private lemma large_dyadic_weight_eq (p e : ℝ) (j : ℕ) :
    ENNReal.ofReal ((2 : ℝ) ^ (j + 1)) * ENNReal.ofReal ((2 : ℝ) ^ j) ^ (-p * e) =
      2 * ((2 : ℝ≥0∞) ^ (1 - p * e)) ^ j := by
  have hcomm : ((2 : ℝ≥0∞) ^ j) ^ (-p * e) = ((2 : ℝ≥0∞) ^ (-p * e)) ^ j := by
    rw [← ENNReal.rpow_natCast_mul, ← ENNReal.rpow_mul_natCast]
    congr 1
    ring
  have hbase : (2 : ℝ≥0∞) * 2 ^ (-p * e) = 2 ^ (1 - p * e) := by
    calc
      _ = (2 : ℝ≥0∞) ^ (1 : ℝ) * 2 ^ (-p * e) := by rw [ENNReal.rpow_one]
      _ = 2 ^ (1 + -p * e) := (ENNReal.rpow_add _ _ (by norm_num) (by norm_num)).symm
      _ = _ := by congr 1; ring
  simp only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  rw [pow_succ, hcomm]
  calc
    _ = 2 * ((2 : ℝ≥0∞) ^ j * (2 ^ (-p * e)) ^ j) := by ring
    _ = _ := by rw [← mul_pow, hbase]

theorem sum_large_superlevel_measures_le (hf : Measurable f) {p e : ℝ}
    (hp : 0 < p) (he : 0 ≤ e) (hnorm : eLpNorm f (ENNReal.ofReal p) μ ≤ 1) :
    (∑' j : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (j + 1)) *
      μ {x | ENNReal.ofReal ((2 : ℝ) ^ j) ≤ f x} ^ e) ≤
        2 * ∑' j : ℕ, ((2 : ℝ≥0∞) ^ (1 - p * e)) ^ j := by
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro j
  have hm := measure_superlevel_le_of_normalized_eLpNorm hf hp
    (by positivity : 0 < (2 : ℝ) ^ j) hnorm
  have hpow := ENNReal.rpow_le_rpow hm he
  rw [← ENNReal.rpow_mul] at hpow
  exact (mul_le_mul_right hpow (ENNReal.ofReal ((2 : ℝ) ^ (j + 1)))).trans_eq
    (large_dyadic_weight_eq p e j)

theorem exists_input_level_sum_constant {K : Set X} (hKfin : μ K ≠ ∞) {p e : ℝ}
    (hp : 0 < p) (he : 0 < e) (hpe : 1 < p * e) :
    ∃ D : ℝ, 0 < D ∧ ∀ f : X → ℝ≥0∞, Measurable f → Function.support f ⊆ K →
      eLpNorm f (ENNReal.ofReal p) μ ≤ 1 →
      (∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j) *
        μ {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ j / 2) ≤ f x} ^ e) +
          (∑' j : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (j + 1)) *
            μ {x | ENNReal.ofReal ((2 : ℝ) ^ j) ≤ f x} ^ e) ≤ ENNReal.ofReal D := by
  let A := 2 * μ K ^ e + 2 * ∑' j : ℕ, ((2 : ℝ≥0∞) ^ (1 - p * e)) ^ j
  have hseries : (∑' j : ℕ, ((2 : ℝ≥0∞) ^ (1 - p * e)) ^ j) ≠ ∞ :=
    (tsum_geometric_lt_top.mpr
      (ENNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))).ne
  have hA : A ≠ ∞ := ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top (by norm_num) (ENNReal.rpow_ne_top_of_nonneg he.le hKfin),
      ENNReal.mul_ne_top (by norm_num) hseries⟩
  refine ⟨A.toReal + 1, by positivity, fun f hf hsupport hnorm ↦ ?_⟩
  have hbound : _ ≤ A := add_le_add (sum_small_superlevel_measures_le hsupport he.le)
    (sum_large_superlevel_measures_le hf hp he.le hnorm)
  apply hbound.trans
  conv_lhs => rw [← ENNReal.ofReal_toReal hA]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end NKBesicovitch
