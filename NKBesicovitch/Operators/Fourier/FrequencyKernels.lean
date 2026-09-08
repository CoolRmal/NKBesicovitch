/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.Fourier.Dilation
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Smooth low-frequency and annular kernels

A smooth cutoff equal to one on the unit ball and zero outside the radius-two
ball supplies a Schwartz low-frequency kernel. The difference of successive
dilations supplies an annular kernel with a unit Fourier gap.
-/

public section

open MeasureTheory Set Metric FourierTransform
open scoped SchwartzMap FourierTransform

namespace NKBesicovitch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A Schwartz kernel with Fourier transform one on the unit ball and zero outside radius two. -/
theorem exists_lowFrequencyKernel : ∃ φ : 𝓢(E, ℂ),
    (∀ ξ : E, ‖ξ‖ ≤ 1 → 𝓕 φ ξ = 1) ∧ (∀ ξ : E, 2 ≤ ‖ξ‖ → 𝓕 φ ξ = 0) ∧
      ∀ ξ : E, ‖𝓕 φ ξ‖ ≤ 1 := by
  let θ : ContDiffBump (0 : E) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let χ : 𝓢(E, ℂ) := (θ.hasCompactSupport.smul_right (f' := fun _ ↦ (1 : ℂ))).toSchwartzMap
    (θ.contDiff.smul contDiff_const)
  refine ⟨𝓕⁻ χ, ?_, ?_, ?_⟩
  · intro ξ hξ
    rw [fourier_fourierInv_eq]
    change θ ξ • (1 : ℂ) = 1
    rw [θ.one_of_mem_closedBall (by simpa only [mem_closedBall_zero_iff] using hξ), one_smul]
  · intro ξ hξ
    rw [fourier_fourierInv_eq]
    change θ ξ • (1 : ℂ) = 0
    rw [θ.zero_of_le_dist (by simpa only [dist_zero_right] using hξ), zero_smul]
  · intro ξ
    rw [fourier_fourierInv_eq]
    change ‖θ ξ • (1 : ℂ)‖ ≤ 1
    simpa only [norm_smul, norm_one, mul_one, Real.norm_of_nonneg θ.nonneg] using θ.le_one

/-- The difference of two successive kernel dilations vanishes at frequencies below one. -/
theorem fourier_dilation_sub_eq_zero_of_norm_lt (φ : 𝓢(E, ℂ))
    (hφ : ∀ ξ : E, ‖ξ‖ ≤ 1 → 𝓕 φ ξ = 1) {ξ : E} (hξ : ‖ξ‖ < 1) :
    𝓕 (normalizedDilation 2 two_pos φ - φ) ξ = 0 := by
  have he : 𝓕 (normalizedDilation 2 two_pos φ - φ) =
      (𝓕 (normalizedDilation 2 two_pos φ) : 𝓢(E, ℂ)) - 𝓕 φ :=
    (fourierCLM ℂ 𝓢(E, ℂ)).map_sub _ _
  rw [he, sub_apply, fourier_normalizedDilation, hφ ξ hξ.le, hφ _ ?_, sub_self]
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  linarith [norm_nonneg ξ]

/-- The same annular kernel has no frequencies of norm at least four. -/
theorem fourier_dilation_sub_eq_zero_of_le_norm (φ : 𝓢(E, ℂ))
    (hφ : ∀ ξ : E, 2 ≤ ‖ξ‖ → 𝓕 φ ξ = 0) {ξ : E} (hξ : 4 ≤ ‖ξ‖) :
    𝓕 (normalizedDilation 2 two_pos φ - φ) ξ = 0 := by
  have he : 𝓕 (normalizedDilation 2 two_pos φ - φ) =
      (𝓕 (normalizedDilation 2 two_pos φ) : 𝓢(E, ℂ)) - 𝓕 φ :=
    (fourierCLM ℂ 𝓢(E, ℂ)).map_sub _ _
  rw [he, sub_apply, fourier_normalizedDilation, hφ ξ (by linarith), hφ _ ?_, sub_self]
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  linarith

/-- A dilated kernel has its closed Fourier support inside the correspondingly dilated ball. -/
theorem tsupport_fourier_normalizedDilation_subset (ψ : 𝓢(E, ℂ)) {R : ℝ}
    (hψ : ∀ ξ : E, R ≤ ‖ξ‖ → 𝓕 ψ ξ = 0) (a : ℝ) (ha : 0 < a) :
    tsupport (𝓕 (normalizedDilation a ha ψ) : 𝓢(E, ℂ)) ⊆ closedBall 0 (a * R) := by
  apply closure_minimal ?_ isClosed_closedBall
  intro ξ hξ
  rw [mem_closedBall_zero_iff]
  by_contra hn
  have hnorm : R ≤ ‖a⁻¹ • ξ‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), ← div_eq_inv_mul]
    exact (le_div_iff₀ ha).mpr (by nlinarith [lt_of_not_ge hn])
  apply hξ
  change 𝓕 (normalizedDilation a ha ψ) ξ = 0
  rw [fourier_normalizedDilation, hψ _ hnorm]

end NKBesicovitch
