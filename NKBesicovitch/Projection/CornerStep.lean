/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerWitness
public import NKBesicovitch.Projection.CornerAlgebra
public import NKBesicovitch.Projection.Estimates

/-!
# Applying the input projection estimate to a selected corner fiber

The second use of the input estimate bounds the outer-density threshold in
terms of the parent density and the original projection size. This step
retains the full dependence on parallel multiplicity before normalization.
-/

public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem corner_threshold_le_parent_bound {a b c κ β C M N : ℝ}
    (hab : a ≠ b) (hca : c ≠ a) (hκ : κ ≠ 0)
    (hβ : 1 < β) (hβ2 : β ≤ 2) (hC : 0 < C) (hMpos : 0 < M) (Γ : Finset ℝ)
    (hOld : ∀ F : Set (Line m), MeasurableSet F → IsBounded F → (volume F).toReal ≤
      C * (parallelMultiplicity F).toReal ^ (2 - β) * (sliceSize Γ F).toReal ^ β)
    (hua : ∀ t ∈ Γ, t ≠ a) {G : Set (Line m)} (hGb : IsBounded G)
    (hM : (parallelMultiplicity G).toReal ≤ M) (hN : (volume (atHeight c '' G)).toReal ≤ N)
    {D : Set (CornerCoordinates m)} (hD : MeasurableSet D)
    (hDG : D ⊆ cornerFamily a b G) (hpos : 0 < volume D)
    {W : Set (PairCoordinates m)} (hDW : ∀ p ∈ D, cornerParent a p ∈ W)
    (Q₀ : ℝ≥0∞) (hQ₀ : Q₀ ≠ ∞)
    (hQ : ∀ p ∈ D, pairDensity a b c W (pairProjections a b c (cornerParent a p)) ≤ Q₀)
    (τ : ℝ≥0∞) (hτ : 0 < τ.toReal) (S : ℝ → Set (Line m))
    (hS : ∀ t ∈ Γ, cornerOuterData a b c κ t '' D ⊆ S t)
    (hbudget : ∑ t ∈ Γ, τ * volume (S t) ≤ volume D / 2) :
    τ.toReal ^ β ≤ (2 * (codeJacobian m a b).toReal ^ 2 * C) *
      (codeJacobian m a b).toReal ^ (β - 1) * M ^ 2 * (N * Q₀.toReal) ^ (β - 1) := by
  obtain ⟨F, H, hF, hFG, hH, hHF, hHQ, hproj⟩ := exists_corner_witness hab hca hκ id Γ hua
    hGb hD hDG hpos hDW Q₀ hQ₀ hQ τ S hS hbudget
  have hFb := hGb.subset hFG
  have hNf : (sliceSize Γ F).toReal ≤ H / τ.toReal := by
    apply sliceSize_toReal_le hFb (div_nonneg hH.le hτ.le)
    intro t ht
    exact (le_div_iff₀ hτ).mpr (by simpa only [id_eq, mul_comm] using hproj t ht)
  have hMf := (ENNReal.toReal_mono (parallelMultiplicity_ne_top hGb)
    (parallelMultiplicity_mono hFG)).trans hM
  have hOldF := (hOld F hF hFb).trans (mul_le_mul
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow ENNReal.toReal_nonneg hMf (sub_nonneg.mpr hβ2)) hC.le)
    (Real.rpow_le_rpow ENNReal.toReal_nonneg hNf (lt_trans zero_lt_one hβ).le)
    (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    (mul_nonneg hC.le (Real.rpow_nonneg hMpos.le _)))
  have hMpow : M * M ^ (2 - β) = M ^ (3 - β) := by
    conv_lhs => lhs; rw [← Real.rpow_one M]
    rw [← Real.rpow_add hMpos]
    congr 1
    ring
  have hseed : H ≤ (2 * (codeJacobian m a b).toReal ^ 2 * C) *
      M ^ (3 - β) * (H / τ.toReal) ^ β := by
    have h := hHF.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul hM hOldF ENNReal.toReal_nonneg hMpos.le) (by positivity))
    calc
      _ ≤ 2 * (codeJacobian m a b).toReal ^ 2 *
          (M * (C * M ^ (2 - β) * (H / τ.toReal) ^ β)) := h
      _ = _ := by rw [show M * (C * M ^ (2 - β) * (H / τ.toReal) ^ β) =
          C * (M * M ^ (2 - β)) * (H / τ.toReal) ^ β by ring, hMpow]; ring
  apply corner_threshold_bound_of_code_bound hβ (by positivity) ENNReal.toReal_nonneg hMpos
    (ENNReal.toReal_nonneg.trans hN) ENNReal.toReal_nonneg hH hτ hseed
  have h := hHQ.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (mul_le_mul hM hN ENNReal.toReal_nonneg hMpos.le)
      ENNReal.toReal_nonneg) ENNReal.toReal_nonneg)
  simpa only [mul_assoc] using h

end NKBesicovitch.Projection
