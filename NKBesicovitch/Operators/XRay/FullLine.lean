/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.XRay.TimeTranslation
public import NKBesicovitch.Operators.MixedNorm.Sums
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Tactic.Linarith

/-!
# Full lines in slope-intercept coordinates

Bounded vertical support lies in finitely many unit intervals. Positivity
and the finite mixed-norm triangle inequality reduce the full line integral
to the corresponding shifted unit-interval integrals. No measurable or
pointwise finite choice of line integrals is needed.
-/

@[expose] public section

open MeasureTheory Set Bornology NKBesicovitch.Projection
open scoped ENNReal

namespace NKBesicovitch.XRay

variable {m : ℕ}

/-- The full line integral with vertical parameter and horizontal intercept. -/
noncomputable def chartXRay (f : EuclideanSpace ℝ (Fin m) × ℝ → ℝ≥0∞)
    (ξ x : EuclideanSpace ℝ (Fin m)) : ℝ≥0∞ := ∫⁻ t, f (x + t • ξ, t)

theorem measurable_chartXRay {f : EuclideanSpace ℝ (Fin m) × ℝ → ℝ≥0∞}
    (hf : Measurable f) : Measurable (fun g : Line m ↦ chartXRay f g.2 g.1) := by
  have h : Measurable (fun p : Line m × ℝ ↦ f (p.1.1 + p.2 • p.1.2, p.2)) :=
    hf.comp (by fun_prop)
  exact h.lintegral_prod_right'

theorem exists_finite_unitInterval_cover {K : Set (EuclideanSpace ℝ (Fin m) × ℝ)}
    (hK : IsBounded K) :
    ∃ s : Finset ℝ, ∀ z ∈ K, ∃ a ∈ s, z.2 ∈ Icc a (a + 1) := by
  have hcover : closure (Prod.snd '' K) ⊆ ⋃ a : ℝ, Ioo a (a + 1) := by
    intro t _
    exact mem_iUnion.mpr ⟨t - 1 / 2, by constructor <;> linarith⟩
  obtain ⟨s, hs⟩ := hK.image_snd.isCompact_closure.elim_finite_subcover
    (fun a : ℝ ↦ Ioo a (a + 1)) (fun _ ↦ isOpen_Ioo) hcover
  refine ⟨s, fun z hz ↦ ?_⟩
  obtain ⟨a, ha⟩ := mem_iUnion.mp (hs (subset_closure (mem_image_of_mem Prod.snd hz)))
  obtain ⟨has, hat⟩ := mem_iUnion.mp ha
  exact ⟨a, has, hat.1.le, hat.2.le⟩

theorem chartXRay_le_sum_unitIntervals {K : Set (EuclideanSpace ℝ (Fin m) × ℝ)}
    {f : EuclideanSpace ℝ (Fin m) × ℝ → ℝ≥0∞} (hsupport : Function.support f ⊆ K)
    {s : Finset ℝ} (hcover : ∀ z ∈ K, ∃ a ∈ s, z.2 ∈ Icc a (a + 1))
    (ξ x : EuclideanSpace ℝ (Fin m)) :
    chartXRay f ξ x ≤ ∑ a ∈ s, ∫⁻ t in Icc a (a + 1), f (x + t • ξ, t) := by
  have hsub : Function.support (fun t : ℝ ↦ f (x + t • ξ, t)) ⊆
      ⋃ a : s, Icc (a : ℝ) (a + 1) := by
    intro t ht
    obtain ⟨a, ha, hat⟩ := hcover (x + t • ξ, t) (hsupport ht)
    exact mem_iUnion.mpr ⟨⟨a, ha⟩, hat⟩
  unfold chartXRay
  rw [← setLIntegral_eq_of_support_subset hsub]
  apply (lintegral_iUnion_le (μ := volume) (fun a : s ↦ Icc (a : ℝ) (a + 1))
    (fun t ↦ f (x + t • ξ, t))).trans_eq
  rw [tsum_fintype]
  exact Finset.sum_coe_sort s (fun a ↦ ∫⁻ t in Icc a (a + 1), f (x + t • ξ, t))

theorem mixedNorm_chartXRay_le_sum_unitIntervals
    {K : Set (EuclideanSpace ℝ (Fin m) × ℝ)}
    {f : EuclideanSpace ℝ (Fin m) × ℝ → ℝ≥0∞} (hf : Measurable f)
    (hsupport : Function.support f ⊆ K) {s : Finset ℝ}
    (hcover : ∀ z ∈ K, ∃ a ∈ s, z.2 ∈ Icc a (a + 1))
    {Ξ : Set (EuclideanSpace ℝ (Fin m))} (hΞ : MeasurableSet Ξ)
    {q r : ℝ≥0∞} (hq : 1 ≤ q) (hr : 1 ≤ r) (hqfin : q ≠ ∞) (hrfin : r ≠ ∞) :
    mixedNorm ((Prod.snd ⁻¹' Ξ).indicator
      (fun g : Line m ↦ chartXRay f g.2 g.1)) q r volume volume ≤
        ∑ a ∈ s, mixedNorm ((Prod.snd ⁻¹' Ξ).indicator
          (fun g : Line m ↦ ∫⁻ t in Icc a (a + 1), f (g.1 + t • g.2, t)))
            q r volume volume := by
  have hpoint (g : Line m) : (Prod.snd ⁻¹' Ξ).indicator
      (fun g : Line m ↦ chartXRay f g.2 g.1) g ≤
        ∑ a ∈ s, (Prod.snd ⁻¹' Ξ).indicator
          (fun g : Line m ↦ ∫⁻ t in Icc a (a + 1), f (g.1 + t • g.2, t)) g := by
    by_cases hg : g ∈ Prod.snd ⁻¹' Ξ
    · simp only [indicator_of_mem hg]
      exact chartXRay_le_sum_unitIntervals hsupport hcover g.2 g.1
    · simp only [indicator_of_notMem hg]
      exact zero_le
  apply (mixedNorm_mono hpoint).trans
  apply mixedNorm_sum_le s ?_ hq hr hqfin hrfin
  intro a _
  have h : Measurable (fun p : Line m × ℝ ↦ f (p.1.1 + p.2 • p.1.2, p.2)) :=
    hf.comp (by fun_prop)
  exact (h.lintegral_prod_right' (ν := volume.restrict (Icc a (a + 1)))).indicator
    (hΞ.preimage measurable_snd)

end NKBesicovitch.XRay
