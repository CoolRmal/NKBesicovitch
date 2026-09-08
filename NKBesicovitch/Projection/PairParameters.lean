/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.PairWitness
public import NKBesicovitch.Projection.Estimates
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Choosing the pair-density threshold

The threshold spends exactly half the pair mass across the selected heights.
Cauchy–Schwarz then gives the line-mass lower bound needed for amplification.
-/

@[expose] public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- The half-mass deletion threshold for `r` selected projections of size at most `N`. -/
noncomputable def pairThreshold (v N : ℝ≥0∞) (r : ℕ) : ℝ≥0∞ := (v / 2) / (r * N ^ 2)

theorem pairThreshold_budget (v : ℝ≥0∞) {N : ℝ≥0∞} (hN0 : N ≠ 0) (hN : N ≠ ∞)
    {r : ℕ} (hr : r ≠ 0) : r * pairThreshold v N r * N ^ 2 = v / 2 := by
  calc
    _ = ((v / 2) / (r * N ^ 2)) * (r * N ^ 2) := by unfold pairThreshold; ac_rfl
    _ = _ := ENNReal.div_mul_cancel
      (mul_ne_zero (Nat.cast_ne_zero.mpr hr) (pow_ne_zero _ hN0))
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top r) (ENNReal.pow_ne_top hN))

theorem pairThreshold_toReal_pos {v N : ℝ≥0∞} (hv0 : v ≠ 0) (hv : v ≠ ∞)
    (hN0 : N ≠ 0) (hN : N ≠ ∞) {r : ℕ} (hr : r ≠ 0) :
    0 < (pairThreshold v N r).toReal := by
  have hv' := ENNReal.toReal_pos hv0 hv
  have hN' := ENNReal.toReal_pos hN0 hN
  have hr' : 0 < (r : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hr)
  simp only [pairThreshold, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  positivity

theorem sq_volume_le_pairThreshold (a : ℝ) {G : Set (Line m)} (hG : MeasurableSet G)
    (hGb : IsBounded G) {N : ℝ≥0∞} (hN0 : N ≠ 0) (hN : N ≠ ∞)
    (haN : volume (atHeight a '' G) ≤ N) {r : ℕ} (hr : r ≠ 0) :
    (volume G).toReal ^ 2 ≤ (2 * r) *
      (pairThreshold (volume (pairFamily a G)) N r).toReal * N.toReal ^ 3 := by
  have h := (sq_volume_le_projection_mul_pairMass a hG).trans
    (mul_le_mul haN le_rfl bot_le bot_le)
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hN (volume_pairFamily_ne_top a hGb)) h
  simp only [ENNReal.toReal_pow, ENNReal.toReal_mul] at hreal
  have hb := congrArg ENNReal.toReal (pairThreshold_budget (volume (pairFamily a G)) hN0 hN hr)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, ENNReal.toReal_ofNat] at hb
  calc
    _ ≤ N.toReal * (volume (pairFamily a G)).toReal := hreal
    _ = _ := by
      rw [← (eq_div_iff (two_ne_zero : (2 : ℝ) ≠ 0)).mp hb]
      ring

theorem exists_uniform_pairJacobian {a b c : ℝ} (hab : a ≠ b) (hc : c ≠ 0)
    {Γ : Finset ℝ} (hΓ : Γ.Nonempty) (hta : ∀ t ∈ Γ, t ≠ a) (htb : ∀ t ∈ Γ, t ≠ b) :
    ∃ q : ℝ, 0 < q ∧ ∀ t ∈ Γ, q ≤
      (ENNReal.ofReal |(((b - a) / (dualTime a b c t - a)) ^ m)⁻¹|).toReal := by
  let f : ℝ → ℝ := fun t ↦
    (ENNReal.ofReal |(((b - a) / (dualTime a b c t - a)) ^ m)⁻¹|).toReal
  refine ⟨Γ.inf' hΓ f, ?_, fun t ht ↦ Finset.inf'_le f ht⟩
  apply (Finset.lt_inf'_iff hΓ).mpr
  intro t ht
  have hd := sub_ne_zero.mpr (dualTime_ne_base hab hc (hta t ht) (htb t ht))
  dsimp [f]
  rw [ENNReal.toReal_ofReal (abs_nonneg _)]
  exact abs_pos.mpr (inv_ne_zero (pow_ne_zero _ (div_ne_zero (sub_ne_zero.mpr hab.symm) hd)))

end NKBesicovitch.Projection
