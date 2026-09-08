/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Smooth decomposition by amplitude

A compactly supported Schwartz function splits at any positive threshold
into two Schwartz functions with no increase in spatial support. The low
part is bounded by twice the threshold. The high part vanishes below the
threshold and is bounded in norm by the original function. This allows
endpoint interpolation without leaving the Schwartz domain of an operator.
-/

public section

open Function Set Metric
open scoped SchwartzMap

namespace NKBesicovitch

private theorem norm_cutoff_smul_le (θ : ContDiffBump (0 : ℂ)) (z : ℂ) :
    ‖θ z • z‖ ≤ θ.rOut := by
  by_cases hz : ‖z‖ < θ.rOut
  · calc
      ‖θ z • z‖ = θ z * ‖z‖ := by
        rw [norm_smul, Real.norm_of_nonneg θ.nonneg]
      _ ≤ ‖z‖ := mul_le_of_le_one_left (norm_nonneg _) θ.le_one
      _ ≤ θ.rOut := hz.le
  · rw [θ.zero_of_le_dist (by simpa only [dist_zero_right] using le_of_not_gt hz),
      zero_smul, norm_zero]
    exact θ.rOut_pos.le

private theorem norm_sub_cutoff_smul_le (θ : ContDiffBump (0 : ℂ)) (z : ℂ) :
    ‖z - θ z • z‖ ≤ ‖z‖ := by
  calc
    ‖z - θ z • z‖ = ‖(1 - θ z) • z‖ := by rw [sub_smul, one_smul]
    _ = (1 - θ z) * ‖z‖ := by
      rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr θ.le_one)]
    _ ≤ ‖z‖ := mul_le_of_le_one_left (norm_nonneg _) (by linarith [θ.nonneg' z])

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Smooth amplitude truncation preserves support and separates the high-amplitude tail. -/
theorem exists_schwartz_amplitude_decomposition (f : 𝓢(E, ℂ))
    (hf : HasCompactSupport (f : E → ℂ)) {t : ℝ} (ht : 0 < t) :
    ∃ g h : 𝓢(E, ℂ), f = g + h ∧ support (g : E → ℂ) ⊆ support (f : E → ℂ) ∧
      support (h : E → ℂ) ⊆ support (f : E → ℂ) ∧ (∀ x, ‖g x‖ ≤ 2 * t) ∧
      (∀ x, ‖h x‖ ≤ ‖f x‖) ∧ ∀ x, ‖f x‖ ≤ t → h x = 0 := by
  let θ : ContDiffBump (0 : ℂ) := ⟨t, 2 * t, ht, by linarith⟩
  let g : 𝓢(E, ℂ) := (hf.smul_left (f := fun x ↦ θ (f x))).toSchwartzMap
    ((θ.contDiff.comp (f.smooth ⊤)).smul (f.smooth ⊤))
  have hg (x : E) : g x = θ (f x) • f x := rfl
  have hs : support (g : E → ℂ) ⊆ support (f : E → ℂ) :=
    support_smul_subset_right _ _
  refine ⟨g, f - g, by abel, hs, ?_, ?_, ?_, ?_⟩
  · intro x hx hzero
    apply hx
    simp only [sub_apply, hg, hzero, smul_zero, sub_self]
  · intro x
    rw [hg]
    exact norm_cutoff_smul_le θ (f x)
  · intro x
    simpa only [sub_apply, hg] using norm_sub_cutoff_smul_le θ (f x)
  · intro x hx
    simp only [sub_apply, hg,
      θ.one_of_mem_closedBall (by simpa only [mem_closedBall_zero_iff, θ] using hx),
      one_smul, sub_self]

end NKBesicovitch
