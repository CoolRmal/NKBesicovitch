/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.PlateWeakMoments
public import NKBesicovitch.Operators.Interpolation.LevelWeights
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

/-!
# Restricted weak estimates imply strong plate estimates

A restricted weak estimate with exponent `P > 0` gives a strong estimate at
every finite exponent `p > P`. The conversion constant depends only on the
exponents, and a restricted weak coefficient `A` contributes `A^(1/p)`.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace NKBesicovitch

variable {n k : ℕ} {P p : ℝ}

/-- The restricted weak coefficient controls every higher moment with a uniform finite cost. -/
theorem exists_plateMaximal_moment_bound (hP : 0 < P) (hPp : P < p) :
    ∃ D : ℝ≥0, ∀ (ν : Measure (Grassmannian n k)) (δ : ℝ) (A : ℝ≥0∞), 0 < δ →
      (∀ E : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet E → volume E ≠ ∞ →
        ∀ s : ℝ≥0, 0 < s → ν {V | (s : ℝ≥0∞) <
          plateMaximal δ (E.indicator (fun _ ↦ (1 : ℝ≥0∞))) V} ≤
            A * (s : ℝ≥0∞) ^ (-P) * volume E) →
      ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞), Measurable f →
      ∀ K : Set (EuclideanSpace ℝ (Fin n)), volume K ≠ ∞ → Function.support f ⊆ K →
        (∫⁻ V, plateMaximal δ f V ^ p ∂ν) ≤ A * (D : ℝ≥0∞) * ∫⁻ x, f x ^ p := by
  have hpdiv : 1 < p / P := (lt_div_iff₀ hP).mpr (by simpa using hPp)
  obtain ⟨q, hq, hqp⟩ := exists_between hpdiv
  obtain ⟨a, ha, hasum, hcost⟩ := exists_dyadic_level_allocation hq
    ((lt_div_iff₀ hP).mp hqp)
  let D := ∑' j : ℕ, (a j : ℝ≥0∞) ^ (-P) * ENNReal.ofReal ((2 : ℝ) ^ j / 2) ^ (-p)
  refine ⟨D.toNNReal, fun ν δ A hδ hweak f hf K hK hs ↦ ?_⟩
  rw [ENNReal.coe_toNNReal hcost]
  exact lintegral_plateMaximal_rpow_le_level_sum ν hδ hweak (hP.trans hPp) hf hK hs
    a ha hasum.le

/-- Restricted weak plate estimates give strong bounds for arbitrary nonnegative Borel inputs. -/
theorem exists_plateMaximal_eLpNorm_bound (hP : 0 < P) (hPp : P < p) :
    ∃ C : ℝ≥0, ∀ (ν : Measure (Grassmannian n k)) (δ : ℝ) (A : ℝ≥0∞), 0 < δ →
      (∀ E : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet E → volume E ≠ ∞ →
        ∀ s : ℝ≥0, 0 < s → ν {V | (s : ℝ≥0∞) <
          plateMaximal δ (E.indicator (fun _ ↦ (1 : ℝ≥0∞))) V} ≤
            A * (s : ℝ≥0∞) ^ (-P) * volume E) →
      ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞), Measurable f →
      ∀ K : Set (EuclideanSpace ℝ (Fin n)), volume K ≠ ∞ → Function.support f ⊆ K →
        eLpNorm (plateMaximal δ f) (ENNReal.ofReal p) ν ≤
          (C : ℝ≥0∞) * A ^ (1 / p) * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨D, hD⟩ := exists_plateMaximal_moment_bound (n := n) (k := k) hP hPp
  have hp := hP.trans hPp
  have hi := (one_div_pos.mpr hp).le
  refine ⟨D ^ (1 / p), fun ν δ A hδ hweak f hf K hK hs ↦ ?_⟩
  have h := ENNReal.rpow_le_rpow (hD ν δ A hδ hweak f hf K hK hs) hi
  simp only [ENNReal.mul_rpow_of_nonneg _ _ hi] at h
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp).ne'
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le, enorm_eq_self,
    ENNReal.coe_rpow_of_nonneg _ hi]
  simpa only [mul_comm (A ^ (1 / p))] using h

end NKBesicovitch
