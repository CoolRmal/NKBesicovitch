/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.FullLine
public import NKBesicovitch.Operators.XRay.Strong

/-!
# Strong estimates for full lines on bounded supports

The model estimate on `[0,1]` extends to the full line integral with the
same input and output exponents. A finite cover of the vertical support
introduces only a support-dependent constant. This is the full-line
slope-coordinate estimate used in the change to geometric directions.
-/

public section

open MeasureTheory Set Bornology NKBesicovitch.Projection
open scoped ENNReal

namespace NKBesicovitch.XRay

variable {m : ℕ}

theorem exists_unitInterval_bound_of_local
    {Ξ : Set (EuclideanSpace ℝ (Fin m))} {p q r : ℝ≥0∞}
    (hlocal : ∀ K : Set (EuclideanSpace ℝ (Fin m) × ℝ), IsBounded K →
      ∃ C : ℝ, 0 < C ∧ ∀ f : EuclideanSpace ℝ (Fin m) × ℝ → ℝ≥0∞,
        Measurable f → Function.support f ⊆ K → mixedNorm ((Prod.snd ⁻¹' Ξ).indicator
          (fun g : Line m ↦ localXRay f g.2 g.1)) q r volume volume ≤
            ENNReal.ofReal C * eLpNorm f p volume)
    {K : Set (EuclideanSpace ℝ (Fin m) × ℝ)} (hK : IsBounded K) (a : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : EuclideanSpace ℝ (Fin m) × ℝ → ℝ≥0∞,
      Measurable f → Function.support f ⊆ K → mixedNorm ((Prod.snd ⁻¹' Ξ).indicator
        (fun g : Line m ↦ ∫⁻ t in Icc a (a + 1), f (g.1 + t • g.2, t))) q r volume volume ≤
          ENNReal.ofReal C * eLpNorm f p volume := by
  let K' := (fun z : EuclideanSpace ℝ (Fin m) × ℝ ↦ z + (0, -a)) '' K
  have hK' : IsBounded K' := (isometry_add_right ((0 : EuclideanSpace ℝ (Fin m)), -a)).lipschitz
    |>.isBounded_image hK
  obtain ⟨C, hC, hbound⟩ := hlocal K' hK'
  refine ⟨C, hC, fun f hf hsupport ↦ ?_⟩
  have hm : Measurable (fun z : EuclideanSpace ℝ (Fin m) × ℝ ↦ f (z.1, a + z.2)) :=
    hf.comp (by fun_prop)
  have hs : Function.support (fun z : EuclideanSpace ℝ (Fin m) × ℝ ↦ f (z.1, a + z.2)) ⊆ K' := by
    intro z hz
    refine ⟨(z.1, a + z.2), hsupport hz, ?_⟩
    ext <;> simp [add_assoc]
  rw [mixedNorm_unitInterval_eq_localXRay hf a]
  simpa only [eLpNorm_vertical_translate hf a] using hbound _ hm hs

theorem exists_chartXRay_mixedNorm_bound (m : ℕ) [Nonempty (Fin m)] {β : ℝ}
    (hβ : projectionExponent < β) (hβ2 : β ≤ 2) :
    ∃ Q : ℕ, 2 < Q ∧ ∀ K : Set (EuclideanSpace ℝ (Fin m) × ℝ), IsBounded K →
      ∀ Ξ : Set (EuclideanSpace ℝ (Fin m)), MeasurableSet Ξ → IsBounded Ξ →
        ∀ p : ℝ, (Q : ℝ) / β < p → ∃ C : ℝ, 0 < C ∧
          ∀ f : EuclideanSpace ℝ (Fin m) × ℝ → ℝ≥0∞, Measurable f →
            Function.support f ⊆ K →
              mixedNorm ((Prod.snd ⁻¹' Ξ).indicator
                (fun g : Line m ↦ chartXRay f g.2 g.1)) (ENNReal.ofReal Q)
                  (ENNReal.ofReal ((Q : ℝ) / (β - 1))) volume volume ≤
                    ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
  classical
  obtain ⟨Q, hQ, hlocal⟩ := exists_strong_mixedNorm_bound m hβ hβ2
  refine ⟨Q, hQ, fun K hK Ξ hΞ hΞb p hp ↦ ?_⟩
  obtain ⟨s, hcover⟩ := exists_finite_unitInterval_cover hK
  choose C hC hbound using fun a : ℝ ↦ exists_unitInterval_bound_of_local
    (fun L hL ↦ hlocal L hL Ξ hΞ hΞb p hp) hK a
  have hsum : 0 ≤ ∑ a ∈ s, C a := Finset.sum_nonneg (fun a _ ↦ (hC a).le)
  refine ⟨(∑ a ∈ s, C a) + 1, by linarith, fun f hf hsupport ↦ ?_⟩
  have hQreal : (2 : ℝ) < Q := by exact_mod_cast hQ
  have hβ1 : 1 < β := projectionExponent_mem.1.trans hβ
  have hq : 1 ≤ ENNReal.ofReal (Q : ℝ) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hr : 1 ≤ ENNReal.ofReal ((Q : ℝ) / (β - 1)) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((le_div_iff₀ (by linarith : 0 < β - 1)).mpr (by linarith))
  apply (mixedNorm_chartXRay_le_sum_unitIntervals hf hsupport hcover hΞ hq hr
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top).trans
  calc
    _ ≤ ∑ a ∈ s, ENNReal.ofReal (C a) * eLpNorm f (ENNReal.ofReal p) volume :=
      Finset.sum_le_sum (fun a _ ↦ hbound a f hf hsupport)
    _ = ENNReal.ofReal (∑ a ∈ s, C a) * eLpNorm f (ENNReal.ofReal p) volume := by
      rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun a _ ↦ (hC a).le)]
    _ ≤ _ := mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith)) _

end NKBesicovitch.XRay
