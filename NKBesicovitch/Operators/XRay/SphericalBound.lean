/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Geometry.DirectionCover
public import NKBesicovitch.Operators.MixedNorm.FiniteCover
public import NKBesicovitch.Operators.XRay.Spherical
public import NKBesicovitch.Operators.XRay.FullLineBound

/-!
# Strong spherical X-ray estimates

Volume-preserving normal coordinates transfer the model estimate to each
bounded slope cap. A finite cover of the sphere then gives the geometric
mixed-norm estimate with the same exponents. Its constant depends on the
bounded support and the exponents, but is uniform over all Borel inputs.
-/

public section

open MeasureTheory Submodule Set Metric Bornology NKBesicovitch.Projection
open scoped ENNReal InnerProductSpace

namespace NKBesicovitch.XRay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {m : ℕ}
    {p q r : ℝ≥0∞}

theorem exists_cap_bound_of_chart
    (hmodel : ∀ K : Set (EuclideanSpace ℝ (Fin m) × ℝ), IsBounded K →
      ∀ Ξ : Set (EuclideanSpace ℝ (Fin m)), MeasurableSet Ξ → IsBounded Ξ →
        ∃ C : ℝ, 0 < C ∧ ∀ f : EuclideanSpace ℝ (Fin m) × ℝ → ℝ≥0∞,
          Measurable f → Function.support f ⊆ K →
            mixedNorm ((Prod.snd ⁻¹' Ξ).indicator (fun g : Line m ↦ chartXRay f g.2 g.1))
              q r volume volume ≤ ENNReal.ofReal C * eLpNorm f p volume)
    {K : Set E} (hK : IsBounded K) {v : E} (hv : ‖v‖ = 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : E → ℝ≥0∞, Measurable f → Function.support f ⊆ K →
      eLpNorm (directionXRayNorm f r) q ((volume : Measure E).toSphere.restrict
        (normalDirection hv '' {ξ | (1 / 2 : ℝ) ≤ ⟪v, (normalDirection hv ξ : E)⟫_ℝ})) ≤
          ENNReal.ofReal C * eLpNorm f p volume := by
  let A : Set (ℝ ∙ v)ᗮ := {ξ | (1 / 2 : ℝ) ≤ ⟪v, (normalDirection hv ξ : E)⟫_ℝ}
  let e := normalCoordinatesWithBasis hv b
  have hA : MeasurableSet A := measurableSet_normalSlopes hv _
  have hAb : IsBounded A := isBounded_normalSlopes hv (by norm_num)
  obtain ⟨C, _, hbound⟩ := hmodel (e ⁻¹' K) (e.antilipschitz.isBounded_preimage hK)
    (b ⁻¹' A) (hA.preimage b.continuous.measurable) (b.antilipschitz.isBounded_preimage hAb)
  let D : ℝ≥0∞ := (Module.finrank ℝ E : ℝ≥0∞) ^ (1 / q.toReal) * 2 * ENNReal.ofReal C
  have hD : D ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by simp)) (by simp))
      ENNReal.ofReal_ne_top
  refine ⟨D.toReal + 1, by positivity, fun f hf hs ↦ ?_⟩
  have hg : Measurable (f ∘ e) := hf.comp e.continuous.measurable
  have hgs : Function.support (f ∘ e) ⊆ e ⁻¹' K := fun _ hz ↦ hs hz
  have hnorm : eLpNorm (f ∘ e) p volume = eLpNorm f p volume :=
    eLpNorm_comp_measurePreserving hf.aestronglyMeasurable
      (measurePreserving_normalCoordinatesWithBasis hv b)
  have hcap := eLpNorm_directionXRayNorm_cap_le hv b hA (by norm_num : (0 : ℝ) < 1 / 2)
    (fun _ hξ ↦ hξ) hf q r
  norm_num only [one_div_div, div_one, ENNReal.ofReal_ofNat] at hcap
  apply hcap.trans
  calc
    _ ≤ D * eLpNorm f p volume := by
      simpa only [hnorm, mul_assoc, D] using
        mul_le_mul_right (hbound (f ∘ e) hg hgs)
          ((Module.finrank ℝ E : ℝ≥0∞) ^ (1 / q.toReal) * 2)
    _ ≤ _ := mul_le_mul_left (calc
      D = ENNReal.ofReal D.toReal := (ENNReal.ofReal_toReal hD).symm
      _ ≤ ENNReal.ofReal (D.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)) _

theorem exists_spherical_bound_of_chart [Fact (Module.finrank ℝ E = m + 1)]
    (hmodel : ∀ K : Set (EuclideanSpace ℝ (Fin m) × ℝ), IsBounded K →
      ∀ Ξ : Set (EuclideanSpace ℝ (Fin m)), MeasurableSet Ξ → IsBounded Ξ →
        ∃ C : ℝ, 0 < C ∧ ∀ f : EuclideanSpace ℝ (Fin m) × ℝ → ℝ≥0∞,
          Measurable f → Function.support f ⊆ K →
            mixedNorm ((Prod.snd ⁻¹' Ξ).indicator (fun g : Line m ↦ chartXRay f g.2 g.1))
              q r volume volume ≤ ENNReal.ofReal C * eLpNorm f p volume)
    (hq : 1 ≤ q) (hqfin : q ≠ ∞) {K : Set E} (hK : IsBounded K) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : E → ℝ≥0∞, Measurable f → Function.support f ⊆ K →
      sphericalXRayNorm f q r ≤ ENNReal.ofReal C * eLpNorm f p volume := by
  classical
  let A (v : sphere (0 : E) 1) : Set (ℝ ∙ (v : E))ᗮ :=
    {ξ | (1 / 2 : ℝ) ≤ ⟪(v : E), (normalDirection (norm_eq_of_mem_sphere v) ξ : E)⟫_ℝ}
  let cap (v : sphere (0 : E) 1) := normalDirection (norm_eq_of_mem_sphere v) '' A v
  have hlocal (v : sphere (0 : E) 1) : ∃ C : ℝ, 0 < C ∧
      ∀ f : E → ℝ≥0∞, Measurable f → Function.support f ⊆ K →
        eLpNorm (directionXRayNorm f r) q ((volume : Measure E).toSphere.restrict (cap v)) ≤
          ENNReal.ofReal C * eLpNorm f p volume := by
    let b := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) m (v := (v : E))
      (norm_pos_iff.mp (by rw [norm_eq_of_mem_sphere v]; norm_num))).repr.symm
    exact exists_cap_bound_of_chart hmodel hK (norm_eq_of_mem_sphere v) b
  choose C hC hbound using hlocal
  obtain ⟨s, hs⟩ := exists_finite_bounded_slope_cover (E := E)
  have hcover : ∀ w, ∃ v ∈ s, w ∈ cap v := by
    intro w
    obtain ⟨v, hv, ξ, hξ, heq⟩ := hs w
    exact ⟨v, hv, ξ, hξ, heq⟩
  have hsum : 0 ≤ ∑ v ∈ s, C v := Finset.sum_nonneg (fun v _ ↦ (hC v).le)
  refine ⟨(∑ v ∈ s, C v) + 1, by linarith, fun f hf hsupport ↦ ?_⟩
  apply (eLpNorm_le_sum_restrict (directionXRayNorm f r) s cap hcover hq hqfin).trans
  calc
    _ ≤ ∑ v ∈ s, ENNReal.ofReal (C v) * eLpNorm f p volume :=
      Finset.sum_le_sum (fun v _ ↦ hbound v f hf hsupport)
    _ = ENNReal.ofReal (∑ v ∈ s, C v) * eLpNorm f p volume := by
      rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun v _ ↦ (hC v).le)]
    _ ≤ _ := mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith)) _

/-- The strong geometric X-ray estimate at every strictly supercritical projection exponent. -/
theorem exists_sphericalXRayNorm_bound (m : ℕ) [Nonempty (Fin m)]
    [Fact (Module.finrank ℝ E = m + 1)] {β : ℝ}
    (hβ : projectionExponent < β) (hβ2 : β ≤ 2) :
    ∃ Q : ℕ, 2 < Q ∧ ∀ K : Set E, IsBounded K → ∀ p : ℝ, (Q : ℝ) / β < p →
      ∃ C : ℝ, 0 < C ∧ ∀ f : E → ℝ≥0∞, Measurable f → Function.support f ⊆ K →
        sphericalXRayNorm f (ENNReal.ofReal Q) (ENNReal.ofReal ((Q : ℝ) / (β - 1))) ≤
          ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨Q, hQ, hmodel⟩ := exists_chartXRay_mixedNorm_bound m hβ hβ2
  refine ⟨Q, hQ, fun K hK p hp ↦ ?_⟩
  have hq : 1 ≤ ENNReal.ofReal (Q : ℝ) := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    exact_mod_cast (by omega : 1 ≤ Q)
  exact exists_spherical_bound_of_chart (fun L hL Ξ hΞ hΞb ↦ hmodel L hL Ξ hΞ hΞb p hp)
    hq ENNReal.ofReal_ne_top hK

end NKBesicovitch.XRay
