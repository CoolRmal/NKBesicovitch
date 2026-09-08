/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.ControlledCoefficients
public import NKBesicovitch.Projection.PatternBound

/-!
# One explicit stopping constant for all controlled patterns

The common inner and outer coefficient and the upper bound on the outer
label count determine a stopping-node constant. The pattern itself does
not occur in this formula, so it applies at every controlled tree node.
-/

@[expose] public section

open MeasureTheory Set

namespace NKBesicovitch.Projection

/-- The stopping constant expressed using common quantitative data. -/
noncomputable def controlledStoppingConstant (m L : ℕ) (β r C c₀ c₁ d : ℝ) : ℝ :=
  let q := β / (β - 1)
  let B := controlCoefficient m β r C
  let A := (c₀ * d / 2) / (2 * L * (B * c₀ ^ (1 - q)))
  (B * c₁ / A ^ q) ^ (1 / (q + 2 * q ^ 2 - 2))

theorem controlledStoppingConstant_pos (m : ℕ) {L : ℕ} (hL : 0 < L) (β : ℝ)
    {r C c₀ c₁ d : ℝ} (hr : 0 < r) (hC : 0 < C) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hd : 0 < d) : 0 < controlledStoppingConstant m L β r C c₀ c₁ d := by
  have hB := controlCoefficient_pos m β hr hC
  unfold controlledStoppingConstant
  positivity

namespace CornerPattern.IsControlled

variable {m L : ℕ} {β r C : ℝ} {P : CornerPattern m β}

theorem stoppingNodeBound (h : P.IsControlled r C L) (hβ : 1 < β) (hβ2 : β ≤ 2)
    {c₀ c₁ d : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hd : 0 < d) :
    P.StoppingNodeBound c₀ c₁ d (controlledStoppingConstant m L β r C c₀ c₁ d) := by
  let q := β / (β - 1)
  let B := controlCoefficient m β r C
  have hB : 0 < B :=
    controlCoefficient_pos m β h.radius_pos (zero_lt_one.trans_le h.one_le_constant)
  have hq : 1 < q := (lt_div_iff₀ (sub_pos.mpr hβ)).mpr (by linarith)
  have he := corner_power_exponent_pos hq
  have hcount : 0 < (P.outer.card : ℝ) := Nat.cast_pos.mpr P.outer_nonempty.card_pos
  have hcountL : (P.outer.card : ℝ) ≤ L := Nat.cast_le.mpr h.outer_card
  have hL : 0 < (L : ℝ) := hcount.trans_le hcountL
  have hcorners := P.stoppingCornerBounds_of_bounds hB
    (P.refinementBound_of_codeImageBound (h.codeImageBound_controlCoefficient hβ hβ2))
    (h.outerBound_controlCoefficient hβ hβ2)
  apply (P.stoppingNodeBound_of_cornerBounds hβ hc₀ hc₁ hd hB hB hcorners).mono
  change (B * c₁ / ((c₀ * d / 2) / (2 * P.outer.card * (B * c₀ ^ (1 - q)))) ^ q) ^
      (1 / (q + 2 * q ^ 2 - 2)) ≤
    (B * c₁ / ((c₀ * d / 2) / (2 * L * (B * c₀ ^ (1 - q)))) ^ q) ^
      (1 / (q + 2 * q ^ 2 - 2))
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  apply Real.rpow_le_rpow (by positivity) _ (zero_lt_one.trans hq).le
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcountL (by norm_num)) (by positivity)

end CornerPattern.IsControlled

end NKBesicovitch.Projection
