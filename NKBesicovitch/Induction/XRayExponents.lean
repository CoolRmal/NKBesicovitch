/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Induction.Parameters
public import NKBesicovitch.Operators.XRay.ScaledBound

/-!
# Compatible X-ray exponents at any prescribed gain ratio

Every `2 < ρ < criticalExponent` admits a strong spherical X-ray estimate
whose displacement/input ratio is exactly `ρ`. Its input exponent is at
least two, its direction exponent lies between the input and displacement
exponents, and the displacement exponent can exceed any prescribed bound.
-/

public section

open MeasureTheory Set Metric NKBesicovitch.XRay
open scoped ENNReal NNReal

namespace NKBesicovitch.Induction

private theorem xray_ratio_parameters {Q β ρ : ℝ} (hQ : 0 < Q) (hβ : 1 < β)
    (hβ2 : β ≤ 2) (hlo : 1 < ρ * (β - 1)) (hhi : ρ * (β - 1) < β) :
    let p := Q / (ρ * (β - 1))
    0 < p ∧ Q / β < p ∧ p ≤ Q ∧ Q ≤ ρ * p ∧ ρ * p = Q / (β - 1) := by
  dsimp only
  have hd := zero_lt_one.trans hlo
  have hβ1 := sub_pos.mpr hβ
  have hρ : 0 < ρ := (mul_pos_iff_of_pos_right hβ1).mp hd
  have he : ρ * (Q / (ρ * (β - 1))) = Q / (β - 1) := by field_simp
  refine ⟨div_pos hQ hd, (div_lt_div_iff₀ (zero_lt_one.trans hβ) hd).2 ?_,
    (div_le_iff₀ hd).2 ?_, ?_, he⟩
  · nlinarith [mul_pos hQ (sub_pos.mpr hhi)]
  · nlinarith [mul_pos hQ (sub_pos.mpr hlo)]
  · rw [he, le_div_iff₀ hβ1]
    nlinarith

private theorem exists_xray_scale {p ρ : ℝ} (hp : 0 < p) (hρ : 0 < ρ) (a : ℝ) :
    ∃ s : ℝ, 1 ≤ s ∧ 2 ≤ s * p ∧ a ≤ ρ * (s * p) := by
  let s := max 1 (max (2 / p) (a / (ρ * p)))
  have htwo : 2 / p ≤ s := (le_max_left _ _).trans (le_max_right _ _)
  have ha : a / (ρ * p) ≤ s := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨s, le_max_left _ _, (div_le_iff₀ hp).mp htwo, ?_⟩
  simpa only [mul_left_comm] using (div_le_iff₀ (mul_pos hρ hp)).mp ha

/-- A fixed subcritical gain ratio is available beyond every required displacement exponent. -/
theorem exists_sphericalXRayNorm_bound_ratio {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m : ℕ) [Nonempty (Fin m)] [Fact (Module.finrank ℝ E = m + 1)]
    {ρ : ℝ} (hρ : ρ ∈ Ioo 2 criticalExponent) (a : ℝ) :
    ∃ p q : ℝ, 2 ≤ p ∧ p ≤ q ∧ q ≤ ρ * p ∧ a ≤ ρ * p ∧
      ∀ R : ℝ≥0, ∃ B : ℝ≥0, ∀ f : E → ℝ≥0∞, Measurable f →
        Function.support f ⊆ closedBall 0 (R : ℝ) →
          sphericalXRayNorm f (ENNReal.ofReal q) (ENNReal.ofReal (ρ * p)) ≤
            B * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨β, hβ, hlo, hhi⟩ := exists_projectionExponent_for_ratio hρ
  obtain ⟨Q, hQ, hx⟩ := exists_sphericalXRayNorm_bound_scaled (E := E) m hβ.1 hβ.2.le
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  let p₀ := (Q : ℝ) / (ρ * (β - 1))
  obtain ⟨hp₀, hbase, hpQ, hQr, hr⟩ :=
    xray_ratio_parameters hQ0 (projectionExponent_mem.1.trans hβ.1) hβ.2.le hlo hhi
  obtain ⟨s, hs, htwo, ha⟩ := exists_xray_scale (ρ := ρ) hp₀ (by linarith [hρ.1]) a
  have hs0 := zero_le_one.trans hs
  refine ⟨s * p₀, s * Q, htwo, mul_le_mul_of_nonneg_left hpQ hs0, ?_, ha, ?_⟩
  · simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left hQr hs0
  · intro R
    obtain ⟨B, hb⟩ := hx p₀ hbase s hs R
    refine ⟨B, fun f hf hsupport ↦ ?_⟩
    have he : s * ((Q : ℝ) / (β - 1)) = ρ * (s * p₀) := by rw [← hr]; ring
    simpa only [he] using hb f hf hsupport

end NKBesicovitch.Induction
