/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.DualPairs
public import NKBesicovitch.Projection.Selection.DualScalar

/-!
# Polynomial bounds for the dual scalar and its Jacobian

On the separated time-pair domain, the dual scalar stays between
`δ |I| / 100` and `(100/|I|)²` in absolute value. The absolute Jacobian
of the second-time change of variables is at least `δ |I| / 100`.
Here the base times belong to `[0,1]` and are separated by at least `δ`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection

theorem dualScalar_bounds {I : Set ℝ} (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I)
    {a b δ : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (hab : δ ≤ dist a b) {p : ℝ × ℝ} (hp : p ∈ dualPairParameters I a b) :
    δ * ((volume I).toReal / 100) ≤ |dualScalar a b p.1 p.2| ∧
      |dualScalar a b p.1 p.2| ≤ (100 / (volume I).toReal) ^ 2 ∧
      δ * ((volume I).toReal / 100) ≤
        |-((b - a) * (p.1 - a) / (p.1 - b)) / (p.2 - a) ^ 2| := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  have hr : 0 < (volume I).toReal / 100 := by positivity
  obtain ⟨ht, hu, hta, htb, hua, _, _⟩ := dualPairParameters_spec hp
  have hunit {x y : ℝ} (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) : |x - y| ≤ 1 := by
    exact Real.dist_le_of_mem_Icc_01 hx hy
  rw [Real.dist_eq, abs_sub_comm a b] at hab
  simp only [Real.dist_eq] at hta htb hua
  have hta₁ := hunit (hIunit ht) ha
  have htb₁ := hunit (hIunit ht) hb
  have hua₁ := hunit (hIunit hu) ha
  have hab₁ := hunit hb ha
  have hnum : δ * ((volume I).toReal / 100) ≤ |b - a| * |p.1 - a| :=
    mul_le_mul hab hta hr.le (abs_nonneg _)
  have hnum₁ : |b - a| * |p.1 - a| ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hab₁ hta₁ (abs_nonneg _) zero_le_one
  have hden : 0 < |p.1 - b| := hr.trans_le htb
  have huapos : 0 < |p.2 - a| := hr.trans_le hua
  have hquot : δ * ((volume I).toReal / 100) ≤ |b - a| * |p.1 - a| / |p.1 - b| :=
    hnum.trans (le_div_self (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hden htb₁)
  simp only [dualScalar, abs_div, abs_mul, abs_neg, abs_pow]
  refine ⟨hquot.trans (le_div_self (by positivity) huapos hua₁), ?_, ?_⟩
  · have h := div_le_div₀ (by norm_num : (0 : ℝ) ≤ 1)
      hnum₁ (by positivity : 0 < ((volume I).toReal / 100) ^ 2)
      (by nlinarith [mul_le_mul htb hua hr.le hden.le] :
        ((volume I).toReal / 100) ^ 2 ≤ |p.1 - b| * |p.2 - a|)
    simpa only [div_div, one_div, ← inv_pow, inv_div] using h
  · exact hquot.trans (le_div_self (by positivity) (by positivity)
      (by nlinarith [mul_self_le_mul_self (abs_nonneg (p.2 - a)) hua₁]))

end NKBesicovitch.Projection.Selection
