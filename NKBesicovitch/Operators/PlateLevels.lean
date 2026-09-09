/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.PlateAlgebra
public import NKBesicovitch.Operators.Interpolation.ScaledLevels
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# A superlevel cover for plate maxima

At each positive output height, the constant half-height contributes at most
half that height. A summable allocation of the remaining half gives a countable
cover by superlevels of plate maxima of input indicators. This is the pointwise
step in restricted-weak to strong interpolation.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace NKBesicovitch

variable {n k : ℕ} {δ : ℝ} {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}

theorem plateMaximal_le_half_add_dyadic (hδ : 0 < δ) (hf : Measurable f)
    (t : ℝ≥0) (ht : 0 < t) (V : Grassmannian n k) :
    plateMaximal δ f V ≤ (t : ℝ≥0∞) / 2 +
      ∑' j : ℕ, (t : ℝ≥0∞) * (2 : ℝ≥0∞) ^ j * plateMaximal δ
        ({x | (t : ℝ≥0∞) * (2 : ℝ≥0∞) ^ j / 2 ≤ f x}.indicator (fun _ ↦ (1 : ℝ≥0∞))) V := by
  let g (j : ℕ) :=
    {x | (t : ℝ≥0∞) * (2 : ℝ≥0∞) ^ j / 2 ≤ f x}.indicator (fun _ ↦ (1 : ℝ≥0∞))
  have hg (j) : Measurable (g j) :=
    measurable_const.indicator (measurableSet_le measurable_const hf)
  have h := plateMaximal_mono (fun x ↦ le_half_add_dyadic_superlevels f t ht x) V (δ := δ)
  apply h.trans
  apply (plateMaximal_add_le measurable_const V).trans
  rw [plateMaximal_const hδ]
  apply add_le_add_right
  have hs := plateMaximal_tsum_le (F := fun j x ↦ (t : ℝ≥0∞) * (2 : ℝ≥0∞) ^ j * g j x)
    (fun j ↦ measurable_const.mul (hg j)) V (δ := δ)
  simpa only [plateMaximal_const_mul _ (hg _), g] using hs

/-- Summable level thresholds cover every positive superlevel of the plate maximal function. -/
theorem plateMaximal_superlevel_subset_iUnion (hδ : 0 < δ) (hf : Measurable f)
    (t : ℝ≥0) (ht : 0 < t) (a : ℕ → ℝ≥0∞)
    (ha : (∑' j : ℕ, (2 : ℝ≥0∞) ^ j * a j) ≤ (2 : ℝ≥0∞)⁻¹) :
    {V : Grassmannian n k | (t : ℝ≥0∞) < plateMaximal δ f V} ⊆
      ⋃ j : ℕ, {V : Grassmannian n k | a j < plateMaximal δ
        ({x | (t : ℝ≥0∞) * (2 : ℝ≥0∞) ^ j / 2 ≤ f x}.indicator (fun _ ↦ (1 : ℝ≥0∞))) V} := by
  intro V hV
  by_contra hnot
  simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_lt] at hnot
  have hs := ENNReal.tsum_le_tsum fun j ↦ mul_le_mul_right (hnot j)
    ((t : ℝ≥0∞) * (2 : ℝ≥0∞) ^ j)
  have hb : (∑' j : ℕ, (t : ℝ≥0∞) * (2 : ℝ≥0∞) ^ j * a j) ≤ (t : ℝ≥0∞) / 2 := by
    simpa only [mul_assoc, ENNReal.tsum_mul_left, div_eq_mul_inv] using
      mul_le_mul_right ha (t : ℝ≥0∞)
  have h := (plateMaximal_le_half_add_dyadic hδ hf t ht V).trans
    (add_le_add_right (hs.trans hb) _)
  have he : (t : ℝ≥0∞) / 2 + (t : ℝ≥0∞) / 2 = t := by
    rw [← ENNReal.add_div, ← two_mul, mul_comm (2 : ℝ≥0∞),
      ENNReal.mul_div_cancel_right (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)]
  exact (not_le_of_gt hV) (h.trans_eq he)

end NKBesicovitch
