/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.PatternControl
public import NKBesicovitch.Projection.TreeThreshold
public import NKBesicovitch.Projection.ControlPolynomial

/-!
# Uniform stopping thresholds for controlled trees

Separation and label-count bounds give one explicit threshold for every
tree with those bounds. When the separation is `x/100`, the threshold
grows at most polynomially in `1/x`.
-/

@[expose] public section

namespace NKBesicovitch.Projection

/-- A common threshold for the root density and all child pruning budgets. -/
noncomputable def controlledStoppingThreshold (m L J : ℕ) (r H : ℝ) : ℝ :=
  max 1 (max ((r⁻¹ ^ (2 * m) + 1) / (1 / (4 * H)))
    ((max 1 (4 * (1 + 2 * (L : ℝ)) * (L * L))) ^ (J : ℝ) ^ 2))

theorem CornerTree.stopping_threshold_of_controlled {m L J : ℕ} {β r C H N : ℝ}
    (T : CornerTree m β J) (hJ : 0 < J) (hH : 0 < H)
    (hcontrol : ∀ v h, (T.pattern v h).IsControlled r C L)
    (hN : controlledStoppingThreshold m L J r H ≤ N) :
    1 ≤ N ∧
    (pairJacobian m (T.a T.root) (T.b T.root) (T.c T.root)).toReal <
      (1 / (4 * H)) * N ^ (96 : ℝ) ∧
    ∀ v h, 4 * (1 + 2 * ((T.pattern v h).outer.card : ℝ)) *
      (T.pattern v h).children.card ≤ N ^ (1 / (J : ℝ) ^ 2) := by
  have hN₁ : 1 ≤ N := (le_max_left _ _).trans hN
  have hroot : T.level T.root < J := T.root_level ▸ hJ
  have hj := (hcontrol T.root hroot).pairJacobian_le
  rw [T.pattern_a, T.pattern_b, T.pattern_c] at hj
  refine ⟨hN₁, ?_, fun v hv ↦ ?_⟩
  · apply hj.trans_lt (root_threshold (by positivity) hN₁ ?_)
    exact (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  · have houter : ((T.pattern v hv).outer.card : ℝ) ≤ L :=
      Nat.cast_le.mpr (hcontrol v hv).outer_card
    have hchildren : ((T.pattern v hv).children.card : ℝ) ≤ (L : ℝ) * L := by
      exact_mod_cast (hcontrol v hv).children_card
    have hfactor : 4 * (1 + 2 * ((T.pattern v hv).outer.card : ℝ)) ≤
        4 * (1 + 2 * (L : ℝ)) := by linarith
    exact (mul_le_mul hfactor hchildren (by positivity) (by positivity)).trans
      (child_pruning_threshold hJ ((le_max_right _ _).trans ((le_max_right _ _).trans hN)))

theorem exists_polynomial_bound_controlledStoppingThreshold (m L J : ℕ) {H : ℝ}
    (hH : 0 < H) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ, 0 < B ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      controlledStoppingThreshold m L J (x / 100) H ≤ C * x⁻¹ ^ B := by
  let A := (max 1 (4 * (1 + 2 * (L : ℝ)) * (L * L))) ^ (J : ℝ) ^ 2
  let K := max 1 (max (8 * H) A)
  have hK₁ : 1 ≤ K := le_max_left _ _
  have hK : 0 < K := zero_lt_one.trans_le hK₁
  obtain ⟨C, hC, B, hB, hbound⟩ := exists_integer_power_bound_monomial hK ((2 * m : ℕ) : ℝ)
  refine ⟨C, hC, B, hB, fun x hx hx₁ ↦ ?_⟩
  have hs : 1 ≤ 100 / x := (le_div_iff₀ hx).mpr (by linarith)
  have hpow : 1 ≤ (100 / x) ^ (2 * m) := one_le_pow₀ hs
  have hKpow : K ≤ K * (100 / x) ^ (2 * m) := le_mul_of_one_le_right hK.le hpow
  have hroot : ((x / 100)⁻¹ ^ (2 * m) + 1) / (1 / (4 * H)) ≤
      K * (100 / x) ^ (2 * m) := by
    rw [inv_div, div_div_eq_mul_div, div_one]
    calc
      _ ≤ ((100 / x) ^ (2 * m) + (100 / x) ^ (2 * m)) * (4 * H) :=
        mul_le_mul_of_nonneg_right (add_le_add_right hpow _) (by positivity)
      _ = (8 * H) * (100 / x) ^ (2 * m) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_right _ _)) (by positivity)
  have hthreshold : controlledStoppingThreshold m L J (x / 100) H ≤
      K * (100 / x) ^ (2 * m) :=
    max_le (hK₁.trans hKpow) (max_le hroot
      (((le_max_right _ _).trans (le_max_right _ _)).trans hKpow))
  have hbound' := hbound x hx hx₁
  rw [Real.rpow_natCast] at hbound'
  exact hthreshold.trans hbound'

end NKBesicovitch.Projection
