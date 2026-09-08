/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.PairWitness
public import NKBesicovitch.Projection.PairAlgebra
public import NKBesicovitch.Projection.Estimates

/-!
# The basic pair improvement with explicit parameters

Apply the old projection estimate to the selected first-line family, then
combine its density lower bound with the parallel-multiplicity upper bound.
-/

public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem volume_le_pair_step {a b c β C : ℝ} (hab : a ≠ b) (hc : c ≠ 0)
    (hβ : 1 < β) (hβ2 : β ≤ 2) (hC : 0 < C) (Γ : Finset ℝ)
    (hOld : ∀ F : Set (Line m), MeasurableSet F → IsBounded F → (volume F).toReal ≤
      C * (parallelMultiplicity F).toReal ^ (2 - β) * (sliceSize Γ F).toReal ^ β)
    (hta : ∀ t ∈ Γ, t ≠ a) (htb : ∀ t ∈ Γ, t ≠ b) {G : Set (Line m)}
    (hG : MeasurableSet G) (hGb : IsBounded G) (hGpos : 0 < volume G)
    (ℓ N : ℝ≥0∞) (hℓ : 0 < ℓ.toReal) (hN : N ≠ ∞) (hNpos : 0 < N.toReal)
    (hbN : volume (atHeight b '' G) ≤ N) (htN : ∀ t ∈ Γ, volume (atHeight t '' G) ≤ N)
    (hdN : ∀ t ∈ Γ, volume (atHeight (dualTime a b c t) '' G) ≤ N)
    (hbudget : Γ.card * ℓ * N ^ 2 ≤ volume (pairFamily a G) / 2)
    (R q : ℝ) (hR : 0 < R) (hq : 0 < q) (hqt : ∀ t ∈ Γ, q ≤
      (ENNReal.ofReal |(((b - a) / (dualTime a b c t - a)) ^ m)⁻¹|).toReal)
    (hmass : (volume G).toReal ^ 2 ≤ R * ℓ.toReal * N.toReal ^ 3) :
    (volume G).toReal ≤
      (((2 * (codeJacobian m a b).toReal * C) * ((codeJacobian m a b).toReal ^ 2) ^ (β - 1)) *
        (R / q) ^ β) ^ (1 / (2 * β)) * (parallelMultiplicity G).toReal ^ (1 / (2 * β)) *
        N.toReal ^ (2 - 1 / (2 * β)) := by
  obtain ⟨F, H, hF, hFG, hH, hHF, hHM, hproj⟩ :=
    exists_pair_witness hab hc Γ hta htb hG hGb hGpos ℓ N hN hbN htN hdN hbudget q hqt
  have hFb := hGb.subset hFG
  have hβ0 : 0 ≤ β := (lt_trans zero_lt_one hβ).le
  have hMf := ENNReal.toReal_mono (parallelMultiplicity_ne_top hGb) (parallelMultiplicity_mono hFG)
  have hNf : (sliceSize Γ F).toReal ≤ H / (q * ℓ.toReal) := by
    apply sliceSize_toReal_le hFb (div_nonneg hH.le (mul_pos hq hℓ).le)
    intro t ht
    exact (le_div_iff₀ (mul_pos hq hℓ)).mpr (by simpa only [mul_comm] using hproj t ht)
  have hMpow := Real.rpow_le_rpow ENNReal.toReal_nonneg hMf (sub_nonneg.mpr hβ2)
  have hNpow := Real.rpow_le_rpow ENNReal.toReal_nonneg hNf hβ0
  have hOldF := (hOld F hF hFb).trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hMpow hC.le) hNpow (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    (mul_nonneg hC.le (Real.rpow_nonneg ENNReal.toReal_nonneg _)))
  have hseed : H ≤ (2 * (codeJacobian m a b).toReal * C) *
      (parallelMultiplicity G).toReal ^ (2 - β) * (H / (q * ℓ.toReal)) ^ β := by
    simpa only [mul_assoc] using hHF.trans
      (mul_le_mul_of_nonneg_left hOldF (by positivity))
  apply pair_amplification hβ (by positivity) (sq_nonneg _) ENNReal.toReal_nonneg
    (ENNReal.toReal_pos (parallelMultiplicity_pos hG hGpos).ne' (parallelMultiplicity_ne_top hGb))
    hNpos hH hR hq hℓ hseed
  · simpa only [mul_assoc] using hHM
  · exact hmass

end NKBesicovitch.Projection
