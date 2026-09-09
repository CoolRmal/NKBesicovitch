/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Hausdorff.ScaleNorm
public import NKBesicovitch.Hausdorff.CoverNorm

/-!
# Summing the covering scales

Classifying positive radii by successive powers of one half gives a
countable open cover. Below dimension `n-α`, the maximal norms are bounded
by a convergent geometric series times the total covering cost.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace NKBesicovitch.Hausdorff

theorem dyadic_rpow_tsum_ne_top {t : ℝ} (ht : 0 < t) :
    (∑' j : ℕ, (((1 / 2 : ℝ≥0) ^ j : ℝ≥0) : ℝ≥0∞) ^ t) ≠ ∞ := by
  have he (j : ℕ) : (((1 / 2 : ℝ≥0) ^ j : ℝ≥0) : ℝ≥0∞) ^ t =
      (((1 / 2 : ℝ≥0) : ℝ≥0∞) ^ t) ^ j := by
    rw [ENNReal.coe_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
      mul_comm (j : ℝ) t, ENNReal.rpow_mul_natCast]
  simp_rw [he]
  exact (tsum_geometric_lt_top.mpr (ENNReal.rpow_lt_one (by norm_num) ht)).ne

theorem exists_dyadic_cover {n : ℕ} (x : ℕ → EuclideanSpace ℝ (Fin n))
    (r : ℕ → ℝ≥0) (hr : ∀ i, 0 < r i ∧ r i ≤ 1) :
    ∃ I : ℕ → Set ℕ, (∀ j i, i ∈ I j → (1 / 2 : ℝ≥0) ^ j / 2 ≤ r i ∧
        r i ≤ (1 / 2 : ℝ≥0) ^ j) ∧
      (⋃ i, ball (x i) (r i)) ⊆ ⋃ j, ⋃ i ∈ I j, ball (x i) (r i) := by
  choose J hJ using fun i ↦ exists_nat_pow_near_of_lt_one (hr i).1 (hr i).2
    (by norm_num : (0 : ℝ≥0) < 1 / 2) (by norm_num : (1 / 2 : ℝ≥0) < 1)
  refine ⟨fun j ↦ {i | J i = j}, ?_, ?_⟩
  · intro j i hi
    change J i = j at hi
    subst j
    constructor
    · simpa only [pow_succ, div_eq_mul_inv, one_mul] using (hJ i).1.le
    · exact (hJ i).2
  · intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨J i, mem_iUnion₂.mpr ⟨i, rfl, hi⟩⟩

/-- A plate estimate forces a positive cost for every ball cover of a Besicovitch set. -/
theorem exists_ball_cover_cost_bound {n k : ℕ} {hkn : k ≤ n} {α p s : ℝ}
    (hp : 1 ≤ p) (hs : 0 ≤ s) (hgap : s < (n : ℝ) - α)
    (h : Induction.HasPlateEstimate hkn α p) :
    ∃ C : ℝ≥0, ∀ {E : Set (EuclideanSpace ℝ (Fin n))}, IsBesicovitch k E →
      ∀ (x : ℕ → EuclideanSpace ℝ (Fin n)) (r : ℕ → ℝ≥0),
        (∀ i, 0 < r i ∧ r i ≤ 1) → E ⊆ ⋃ i, ball (x i) (r i) →
          1 ≤ (C : ℝ≥0∞) * (∑' i, (r i : ℝ≥0∞) ^ s) ^ (1 / p) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have ht : 0 < ((n : ℝ) - s - α) / p := div_pos (by linarith) hp0
  obtain ⟨B, hB⟩ := exists_scale_norm_bound hp0 hs h
  let δ := fun j : ℕ ↦ (1 / 2 : ℝ≥0) ^ j
  let S : ℝ≥0∞ := ∑' j, (δ j : ℝ≥0∞) ^ (((n : ℝ) - s - α) / p)
  have hSf : S ≠ ∞ := dyadic_rpow_tsum_ne_top ht
  have hCf : (2 : ℝ≥0∞) ^ k * B * S ≠ ∞ := by finiteness
  refine ⟨((2 : ℝ≥0∞) ^ k * B * S).toNNReal, ?_⟩
  intro E hE x r hr hcover
  obtain ⟨I, hI, hcover'⟩ := exists_dyadic_cover x r hr
  let U := fun j ↦ ⋃ i ∈ I j, ball (x i) (r i)
  have hU (j) : MeasurableSet (U j) :=
    (isOpen_iUnion fun i ↦ isOpen_iUnion fun _ ↦ isOpen_ball).measurableSet
  have hδ (j) : 0 < δ j ∧ δ j ≤ 1 :=
    ⟨pow_pos (by norm_num) _, pow_le_one₀ (by positivity) (by norm_num)⟩
  have hpos := one_le_tsum_plate_norm_of_cover hkn
    (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)
    ENNReal.ofReal_ne_top
    U hU δ hδ hE (hcover.trans hcover')
  let T := (∑' i, (r i : ℝ≥0∞) ^ s) ^ (1 / p)
  have hsum : (∑' j, eLpNorm (plateMaximal (δ j)
      ((thickening (δ j) (U j)).indicator (fun _ ↦ (1 : ℝ≥0∞))))
        (ENNReal.ofReal p) (Grassmannian.probability hkn)) ≤ B * S * T := by
    calc
      _ ≤ ∑' j, (B : ℝ≥0∞) * (δ j : ℝ≥0∞) ^ (((n : ℝ) - s - α) / p) * T :=
        ENNReal.tsum_le_tsum fun j ↦ hB x r (I j) (δ j) (hδ j).1 (hδ j).2 (hI j)
      _ = _ := by rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
  rw [ENNReal.coe_toNNReal hCf]
  exact hpos.trans ((mul_le_mul_right hsum _).trans_eq (by dsimp only [T]; ac_rfl))

end NKBesicovitch.Hausdorff
