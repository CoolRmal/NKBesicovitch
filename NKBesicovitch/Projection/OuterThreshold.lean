/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.SimultaneousCorners
public import Mathlib.Tactic.Finiteness

/-!
# Choosing the outer-density threshold

Each outer-data image lies in the product of a first-line projection and
an inner-code image. A common bound for those images determines a positive
threshold spending at most half the original corner mass.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ} {ι : Type*}

/-- The half-mass threshold for `r` outer-data images of measure at most `N * R`. -/
noncomputable def cornerThreshold (v N R : ℝ≥0∞) (r : ℕ) : ℝ≥0∞ :=
  (v / 2) / (r * N * R)

theorem cornerThreshold_budget (v : ℝ≥0∞) {N R : ℝ≥0∞}
    (hN₀ : N ≠ 0) (hN : N ≠ ∞) (hR₀ : R ≠ 0) (hR : R ≠ ∞) {r : ℕ} (hr : r ≠ 0) :
    r * cornerThreshold v N R r * N * R = v / 2 := by
  calc
    _ = ((v / 2) / (r * N * R)) * (r * N * R) := by unfold cornerThreshold; ac_rfl
    _ = _ := ENNReal.div_mul_cancel
      (mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr hr) hN₀) hR₀) (by finiteness)

theorem cornerThreshold_toReal_pos {v N R : ℝ≥0∞}
    (hv₀ : v ≠ 0) (hv : v ≠ ∞) (hN₀ : N ≠ 0) (hN : N ≠ ∞)
    (hR₀ : R ≠ 0) (hR : R ≠ ∞) {r : ℕ} (hr : r ≠ 0) :
    0 < (cornerThreshold v N R r).toReal := by
  have hv' := ENNReal.toReal_pos hv₀ hv
  have hN' := ENNReal.toReal_pos hN₀ hN
  have hR' := ENNReal.toReal_pos hR₀ hR
  have hr' : (0 : ℝ) < r := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hr)
  simp only [cornerThreshold, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  positivity

theorem cornerThreshold_toReal (v N R : ℝ≥0∞) (r : ℕ) :
    (cornerThreshold v N R r).toReal = v.toReal / (2 * r * N.toReal * R.toReal) := by
  simp only [cornerThreshold, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  simp only [div_div, mul_assoc]

theorem cornerOuterData_image_subset_prod (a b c κ u : ℝ)
    {D : Set (CornerCoordinates m)} {G : Set (Line m)} (hDG : D ⊆ cornerFamily a b G)
    {E : Set (PairCoordinates m)} (hE : ∀ p ∈ D, cornerInner b p ∈ E) :
    cornerOuterData a b c κ u '' D ⊆ (atHeight u '' G) ×ˢ
      (pairCode b a (cornerInnerCoefficient a c κ u) '' E) := by
  rintro yz ⟨p, hp, rfl⟩
  exact ⟨⟨cornerFirst a p, (hDG hp).1, rfl⟩, ⟨cornerInner b p, hE p hp, rfl⟩⟩

theorem sum_cornerThreshold_mul_volume_le (v : ℝ≥0∞) {N R : ℝ≥0∞}
    (hN₀ : N ≠ 0) (hN : N ≠ ∞) (hR₀ : R ≠ 0) (hR : R ≠ ∞)
    (I : Finset ι) (hI : I.Nonempty) (S : ι → Set (Line m))
    (hS : ∀ i ∈ I, volume (S i) ≤ N * R) :
    ∑ i ∈ I, cornerThreshold v N R I.card * volume (S i) ≤ v / 2 := by
  calc
    _ ≤ ∑ _i ∈ I, cornerThreshold v N R I.card * (N * R) :=
      Finset.sum_le_sum fun i hi ↦ mul_le_mul le_rfl (hS i hi) bot_le bot_le
    _ = I.card * cornerThreshold v N R I.card * N * R := by
      simp [nsmul_eq_mul, mul_assoc]
    _ = _ := cornerThreshold_budget v hN₀ hN hR₀ hR hI.card_ne_zero

end NKBesicovitch.Projection
