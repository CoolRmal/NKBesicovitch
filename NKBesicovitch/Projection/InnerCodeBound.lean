/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.FiberProjection
public import NKBesicovitch.Projection.FiberSelection
public import NKBesicovitch.Projection.CodeBound
public import NKBesicovitch.Projection.Estimates
public import NKBesicovitch.Projection.PairAlgebra

/-!
# Applying the input projection estimate on retained inner-code fibers

A positive code fiber retaining half its original density has enough line
mass to apply the input estimate. Lower double-projection densities bound
all its selected projections, forcing a uniform lower bound on code density.
-/

public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem pair_threshold_le_codeDensity_power {a b c β C M : ℝ}
    (hab : a ≠ b) (hc : c ≠ 0) (hβ : 1 < β) (hβ2 : β ≤ 2) (hC : 0 < C)
    (Γ : Finset ℝ)
    (hOld : ∀ F : Set (Line m), MeasurableSet F → IsBounded F → (volume F).toReal ≤
      C * (parallelMultiplicity F).toReal ^ (2 - β) * (sliceSize Γ F).toReal ^ β)
    (hta : ∀ t ∈ Γ, t ≠ a) (htb : ∀ t ∈ Γ, t ≠ b)
    {G : Set (Line m)} (hGb : IsBounded G) (hM : (parallelMultiplicity G).toReal ≤ M)
    {W E₀ E₁ : Set (PairCoordinates m)} (hW : MeasurableSet W)
    (hE₀ : MeasurableSet E₀) (hE₁ : MeasurableSet E₁)
    (hWG : W ⊆ pairFamily a G) (hE₀W : E₀ ⊆ W) (hE₁W : E₁ ⊆ W)
    (ℓ : ℝ≥0∞) (hℓ : 0 < ℓ.toReal) (q : ℝ) (hq : 0 < q)
    (hqt : ∀ t ∈ Γ, q ≤
      (ENNReal.ofReal |(((b - a) / (dualTime a b c t - a)) ^ m)⁻¹|).toReal)
    (hdense : ∀ t ∈ Γ, ∀ p ∈ E₁, ℓ ≤ pairDensity a t (dualTime a b c t) E₀
      (pairProjections a t (dualTime a b c t) p))
    (z : EuclideanSpace ℝ (Fin m)) (hz : 0 < codeDensity a b c W z)
    (hratio : codeDensity a b c W z ≤ 2 * codeDensity a b c E₁ z) :
    (q * ℓ.toReal) ^ β ≤ (2 * (codeJacobian m a b).toReal * C) * M ^ (2 - β) *
      (codeDensity a b c W z).toReal ^ (β - 1) := by
  let F := pairFiber a b c E₁ z
  let H := (codeDensity a b c W z).toReal
  have hF : MeasurableSet F := measurableSet_pairFiber a b c hE₁ z
  have hFG : F ⊆ G := pairFiber_subset a b c (hE₁W.trans hWG) z
  have hFb := hGb.subset hFG
  have hHfin := codeDensity_ne_top hab hc hW hWG hGb z
  have hH : 0 < H := ENNReal.toReal_pos hz.ne' hHfin
  have hHF : H ≤ 2 * (codeJacobian m a b).toReal * (volume F).toReal := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (codeDensity_ne_top hab hc hE₁ (hE₁W.trans hWG) hGb z)) hratio
    simpa only [H, F, codeDensity, ENNReal.toReal_mul, ENNReal.toReal_ofNat, mul_assoc] using h
  have hNf : (sliceSize Γ F).toReal ≤ H / (q * ℓ.toReal) := by
    apply sliceSize_toReal_le hFb (div_nonneg hH.le (mul_pos hq hℓ).le)
    intro t ht
    have hp := (mul_volume_projection_pairFiber_le hab hc (hta t ht) (htb t ht)
      hE₀ ℓ (hdense t ht) z).trans (codeDensity_mono a b c hE₀W z)
    have hr := ENNReal.toReal_mono hHfin hp
    simp only [ENNReal.toReal_mul] at hr
    apply (le_div_iff₀ (mul_pos hq hℓ)).mpr
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hqt t ht)
      ENNReal.toReal_nonneg) ENNReal.toReal_nonneg).trans hr
  have hMf := (ENNReal.toReal_mono (parallelMultiplicity_ne_top hGb)
    (parallelMultiplicity_mono hFG)).trans hM
  have hOldF := (hOld F hF hFb).trans (mul_le_mul
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow ENNReal.toReal_nonneg hMf (sub_nonneg.mpr hβ2)) hC.le)
    (Real.rpow_le_rpow ENNReal.toReal_nonneg hNf (lt_trans zero_lt_one hβ).le)
    (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    (mul_nonneg hC.le (Real.rpow_nonneg (ENNReal.toReal_nonneg.trans hM) _)))
  apply pair_threshold_bound hH hq hℓ
  simpa only [mul_assoc] using
    hHF.trans (mul_le_mul_of_nonneg_left hOldF (by positivity))

end NKBesicovitch.Projection
