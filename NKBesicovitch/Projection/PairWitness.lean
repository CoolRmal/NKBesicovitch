/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.PairSelection
public import NKBesicovitch.Projection.CodeBound
public import NKBesicovitch.Projection.PairMass

/-!
# Finite numerical data for a pair improvement

Combine simultaneous selection with the parallel-multiplicity upper bound.
Every conversion to real numbers has its required finite-mass justification.
-/

public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem exists_pair_witness {a b c : ℝ} (hab : a ≠ b) (hc : c ≠ 0) (Γ : Finset ℝ)
    (hta : ∀ t ∈ Γ, t ≠ a) (htb : ∀ t ∈ Γ, t ≠ b) {G : Set (Line m)}
    (hG : MeasurableSet G) (hGb : IsBounded G) (hGpos : 0 < volume G)
    (ℓ N : ℝ≥0∞) (hN : N ≠ ∞) (hbN : volume (atHeight b '' G) ≤ N)
    (htN : ∀ t ∈ Γ, volume (atHeight t '' G) ≤ N)
    (hdN : ∀ t ∈ Γ, volume (atHeight (dualTime a b c t) '' G) ≤ N)
    (hbudget : Γ.card * ℓ * N ^ 2 ≤ volume (pairFamily a G) / 2)
    (q : ℝ) (hq : ∀ t ∈ Γ, q ≤ (ENNReal.ofReal |(((b - a) /
      (dualTime a b c t - a)) ^ m)⁻¹|).toReal) :
    ∃ (F : Set (Line m)) (H : ℝ), MeasurableSet F ∧ F ⊆ G ∧ 0 < H ∧
      H ≤ 2 * (codeJacobian m a b).toReal * (volume F).toReal ∧
      H ≤ (codeJacobian m a b).toReal ^ 2 * ((parallelMultiplicity G).toReal * N.toReal) ∧
      ∀ t ∈ Γ, q * ℓ.toReal * (volume (atHeight t '' F)).toReal ≤ H := by
  let W := pairFamily a G
  let W' := densePairs a id (dualTime a b c) Γ W ℓ
  have hW : MeasurableSet W := measurableSet_pairFamily a hG
  have hW' : MeasurableSet W' := measurableSet_densePairs _ _ _ _ hW ℓ
  have hsub : W' ⊆ W := densePairs_subset _ _ _ _ _ _
  obtain ⟨z, hz, hratio, hproj⟩ := exists_densePair_code hab hc id Γ hta htb hW
    Subset.rfl (volume_pairFamily_pos a hG hGpos) (volume_pairFamily_ne_top a hGb)
    ℓ N htN hdN hbudget
  let F := pairFiber a b c W' z
  have hF : MeasurableSet F := measurableSet_pairFiber a b c hW' z
  have hFG : F ⊆ G := pairFiber_subset a b c hsub z
  have hHfin := codeDensity_ne_top hab hc hW Subset.rfl hGb z
  refine ⟨F, (codeDensity a b c W z).toReal, hF, hFG,
    ENNReal.toReal_pos hz.ne' hHfin, ?_, ?_, fun t ht ↦ ?_⟩
  · have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (codeDensity_ne_top hab hc hW' hsub hGb z)) hratio
    change _ ≤ (2 * (codeJacobian m a b * volume F)).toReal at h
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, mul_assoc] using h
  · have hu := (codeDensity_le_parallelMultiplicity hab hc hW Subset.rfl z).trans
      (mul_le_mul le_rfl (mul_le_mul le_rfl hbN bot_le bot_le) bot_le bot_le)
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top (codeJacobian_ne_top m a b))
        (ENNReal.mul_ne_top (parallelMultiplicity_ne_top hGb) hN)) hu
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow] using h
  · have h := ENNReal.toReal_mono hHfin (hproj t ht)
    simp only [ENNReal.toReal_mul] at h
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hq t ht) ENNReal.toReal_nonneg) ENNReal.toReal_nonneg).trans h

end NKBesicovitch.Projection
