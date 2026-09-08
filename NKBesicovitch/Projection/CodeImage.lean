/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.InnerCodeBound

/-!
# Code-image bounds from a density lower bound

The code image can be nonmeasurable. Its outer measure is controlled by a
measurable density superlevel set. A positive lower bound and finite original
pair mass force finite image measure before any conversion to real numbers.
-/

public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem mul_volume_pairCode_image_le {a b : ℝ} (hab : a ≠ b) (c : ℝ)
    {W : Set (PairCoordinates m)} (hW : MeasurableSet W) (E : Set (PairCoordinates m))
    (R : ℝ) (hR : ∀ z ∈ pairCode a b c '' E, R ≤ (codeDensity a b c W z).toReal) :
    ENNReal.ofReal R * volume (pairCode a b c '' E) ≤ volume W := by
  have hsub : pairCode a b c '' E ⊆ {z | ENNReal.ofReal R ≤ codeDensity a b c W z} :=
    fun z hz ↦ ENNReal.ofReal_le_of_le_toReal (hR z hz)
  calc
    _ ≤ ENNReal.ofReal R * volume {z | ENNReal.ofReal R ≤ codeDensity a b c W z} :=
      mul_le_mul le_rfl (measure_mono hsub) bot_le bot_le
    _ ≤ ∫⁻ z, codeDensity a b c W z :=
      mul_meas_ge_le_lintegral (measurable_codeDensity a b c hW) (ENNReal.ofReal R)
    _ = _ := lintegral_codeDensity hab c hW

theorem volume_pairCode_image_ne_top_of_density_lower_bound {a b : ℝ} (hab : a ≠ b) (c : ℝ)
    {W : Set (PairCoordinates m)} (hW : MeasurableSet W) (hWfin : volume W ≠ ∞)
    (E : Set (PairCoordinates m)) {R : ℝ} (hRpos : 0 < R)
    (hR : ∀ z ∈ pairCode a b c '' E, R ≤ (codeDensity a b c W z).toReal) :
    volume (pairCode a b c '' E) ≠ ∞ := by
  have h := ne_top_of_le_ne_top hWfin (mul_volume_pairCode_image_le hab c hW E R hR)
  intro he
  exact h (ENNReal.mul_eq_top.mpr (Or.inl ⟨(ENNReal.ofReal_pos.mpr hRpos).ne', he⟩))

theorem volume_pairCode_image_toReal_le {a b : ℝ} (hab : a ≠ b) (c : ℝ)
    {W : Set (PairCoordinates m)} (hW : MeasurableSet W) (hWfin : volume W ≠ ∞)
    (E : Set (PairCoordinates m)) {R : ℝ} (hRpos : 0 < R)
    (hR : ∀ z ∈ pairCode a b c '' E, R ≤ (codeDensity a b c W z).toReal) :
    (volume (pairCode a b c '' E)).toReal ≤ (volume W).toReal / R := by
  have h := ENNReal.toReal_mono hWfin (mul_volume_pairCode_image_le hab c hW E R hR)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hRpos.le] at h
  exact (le_div_iff₀ hRpos).mpr (by simpa only [mul_comm] using h)

/-- The code-image estimate from the first application of the old projection bound. -/
theorem volume_pairCode_image_le_of_retained_density {a b c β C M : ℝ}
    (hab : a ≠ b) (hc : c ≠ 0) (hβ : 1 < β) (hβ2 : β ≤ 2) (hC : 0 < C) (hMpos : 0 < M)
    (Γ : Finset ℝ)
    (hOld : ∀ F : Set (Line m), MeasurableSet F → IsBounded F → (volume F).toReal ≤
      C * (parallelMultiplicity F).toReal ^ (2 - β) * (sliceSize Γ F).toReal ^ β)
    (hta : ∀ t ∈ Γ, t ≠ a) (htb : ∀ t ∈ Γ, t ≠ b)
    {G : Set (Line m)} (hGb : IsBounded G) (hM : (parallelMultiplicity G).toReal ≤ M)
    {W E₀ E₁ E₂ : Set (PairCoordinates m)} (hW : MeasurableSet W)
    (hE₀ : MeasurableSet E₀) (hE₁ : MeasurableSet E₁)
    (hWG : W ⊆ pairFamily a G) (hE₀W : E₀ ⊆ W) (hE₁W : E₁ ⊆ W)
    (ℓ : ℝ≥0∞) (hℓ : 0 < ℓ.toReal) (q : ℝ) (hq : 0 < q)
    (hqt : ∀ t ∈ Γ, q ≤
      (ENNReal.ofReal |(((b - a) / (dualTime a b c t - a)) ^ m)⁻¹|).toReal)
    (hdense : ∀ t ∈ Γ, ∀ p ∈ E₁, ℓ ≤ pairDensity a t (dualTime a b c t) E₀
      (pairProjections a t (dualTime a b c t) p))
    (hretain : ∀ p ∈ E₂, 0 < codeDensity a b c W (pairCode a b c p) ∧
      codeDensity a b c W (pairCode a b c p) ≤ 2 * codeDensity a b c E₁ (pairCode a b c p)) :
    let R := ((q * ℓ.toReal) ^ β /
      ((2 * (codeJacobian m a b).toReal * C) * M ^ (2 - β))) ^ (1 / (β - 1))
    0 < R ∧ volume (pairCode a b c '' E₂) ≠ ∞ ∧
      (volume (pairCode a b c '' E₂)).toReal ≤ (volume W).toReal / R := by
  let R := ((q * ℓ.toReal) ^ β /
    ((2 * (codeJacobian m a b).toReal * C) * M ^ (2 - β))) ^ (1 / (β - 1))
  have hj := ENNReal.toReal_pos (codeJacobian_pos (m := m) hab).ne' (codeJacobian_ne_top m a b)
  have hA : 0 < (2 * (codeJacobian m a b).toReal * C) * M ^ (2 - β) := by positivity
  have hRpos : 0 < R := Real.rpow_pos_of_pos
    (div_pos (Real.rpow_pos_of_pos (mul_pos hq hℓ) β) hA) _
  have hR : ∀ z ∈ pairCode a b c '' E₂, R ≤ (codeDensity a b c W z).toReal := by
    rintro z ⟨p, hp, rfl⟩
    have h := hretain p hp
    exact lower_bound_of_density_power hβ hA (Real.rpow_nonneg (mul_pos hq hℓ).le _)
      ENNReal.toReal_nonneg (pair_threshold_le_codeDensity_power hab hc hβ hβ2 hC Γ hOld
        hta htb hGb hM hW hE₀ hE₁ hWG hE₀W hE₁W ℓ hℓ q hq hqt hdense _ h.1 h.2)
  have hWfin : volume W ≠ ∞ := ((isBounded_pairFamily a hGb).subset hWG).measure_lt_top.ne
  exact ⟨hRpos, volume_pairCode_image_ne_top_of_density_lower_bound hab c hW hWfin E₂ hRpos hR,
    volume_pairCode_image_toReal_le hab c hW hWfin E₂ hRpos hR⟩

end NKBesicovitch.Projection
