/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CodeDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Selecting a code fiber after refinement

A refinement retaining a fixed fraction of the total pair mass retains at
least that fraction on some code fiber of positive density. The finite-mass
assumption is explicit, so the averaging argument cannot compare two infinities.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem exists_pos_le_mul_of_lintegral_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f g : X → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hfg : f ≤ g) (hpos : 0 < ∫⁻ x, g x ∂μ) (hfin : (∫⁻ x, g x ∂μ) ≠ ∞)
    (c : ℝ≥0∞) (havg : (∫⁻ x, g x ∂μ) ≤ c * ∫⁻ x, f x ∂μ) :
    ∃ x, 0 < g x ∧ g x ≤ c * f x := by
  by_contra h
  have hlt (x : X) (hx : 0 < g x) : c * f x < g x :=
    lt_of_not_ge (fun hle ↦ h ⟨x, hx, hle⟩)
  have hle (x : X) : c * f x ≤ g x := by
    rcases eq_or_lt_of_le (bot_le : 0 ≤ g x) with hx | hx
    · have hf0 : f x = 0 := le_antisymm ((hfg x).trans_eq hx.symm) bot_le
      simp [hf0, ← hx]
    · exact (hlt x hx).le
  have hfi : (∫⁻ x, c * f x ∂μ) ≠ ∞ :=
    ne_top_of_le_ne_top hfin (lintegral_mono hle)
  have hs : μ (Function.support g) ≠ 0 := (lintegral_pos_iff_support hg).mp hpos |>.ne'
  have hi := lintegral_strict_mono_of_ae_le_of_ae_lt_on hg.aemeasurable hfi
    (ae_of_all _ hle) hs (ae_of_all _ fun x hx ↦ hlt x (pos_iff_ne_zero.mpr hx))
  rw [lintegral_const_mul c hf] at hi
  exact (not_lt_of_ge havg) hi

theorem pairFiber_mono (a b c : ℝ) {W₀ W₁ : Set (PairCoordinates m)}
    (hW : W₁ ⊆ W₀) (z : Space m) : pairFiber a b c W₁ z ⊆ pairFiber a b c W₀ z :=
  fun _ hg ↦ hW hg

theorem codeDensity_mono (a b c : ℝ) {W₀ W₁ : Set (PairCoordinates m)}
    (hW : W₁ ⊆ W₀) : codeDensity a b c W₁ ≤ codeDensity a b c W₀ := by
  intro z
  exact mul_le_mul le_rfl (measure_mono (pairFiber_mono a b c hW z)) bot_le bot_le

/-- Retaining half the pair mass retains half the density on some positive code fiber. -/
theorem exists_good_code {a b : ℝ} (hab : a ≠ b) (c : ℝ)
    {W₀ W₁ : Set (PairCoordinates m)} (hW₀ : MeasurableSet W₀) (hW₁ : MeasurableSet W₁)
    (hW : W₁ ⊆ W₀) (hpos : 0 < volume W₀) (hfin : volume W₀ ≠ ∞)
    (hmass : volume W₀ ≤ 2 * volume W₁) :
    ∃ z, 0 < codeDensity a b c W₀ z ∧ codeDensity a b c W₀ z ≤ 2 * codeDensity a b c W₁ z := by
  apply exists_pos_le_mul_of_lintegral_le (measurable_codeDensity a b c hW₁)
    (measurable_codeDensity a b c hW₀) (codeDensity_mono a b c hW)
  · rwa [lintegral_codeDensity hab c hW₀]
  · rwa [lintegral_codeDensity hab c hW₀]
  · simpa only [lintegral_codeDensity hab c hW₀, lintegral_codeDensity hab c hW₁] using hmass

end NKBesicovitch.Projection
