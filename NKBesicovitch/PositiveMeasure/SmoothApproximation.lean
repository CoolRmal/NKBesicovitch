/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Smooth approximations from inside an open set

Choose a smooth function `g` in `[0,1]` with support exactly the open set.
The functions `1 - (1 - g)^j`, multiplied by expanding compact cutoffs,
are positive Schwartz functions dominated by the indicator and converging
pointwise to it. Monotonicity of the cutoffs is not needed.
-/

public section

open Set Metric Filter
open scoped SchwartzMap Topology

namespace NKBesicovitch

private lemma tendsto_bump_mul_one_sub_pow_aux {n : ℕ}
    (θ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (hθ : ∀ j : ℕ, (j : ℝ) ≤ (θ j).rIn) (x : EuclideanSpace ℝ (Fin n))
    {t : ℝ} (ht : t ∈ Ioc 0 1) :
    Tendsto (fun j ↦ θ j x * (1 - (1 - t) ^ j)) atTop (𝓝 1) := by
  have hb : Tendsto (fun j ↦ θ j x) atTop (𝓝 1) := by
    obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with j hj
    symm
    apply (θ j).one_of_mem_closedBall
    exact mem_closedBall_zero_iff.mpr (hN.trans ((by exact_mod_cast hj : (N : ℝ) ≤ j).trans
      (hθ j)))
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr ht.2)
    (show 1 - t < 1 by linarith [ht.1])
  simpa only [sub_zero, mul_one] using hb.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hp)

/-- Every open indicator is a pointwise limit of dominated positive Schwartz functions. -/
theorem exists_schwartz_tendsto_indicator {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) :
    ∃ f : ℕ → 𝓢(EuclideanSpace ℝ (Fin n), ℝ),
      (∀ j x, 0 ≤ f j x ∧ f j x ≤ U.indicator (fun _ ↦ (1 : ℝ)) x) ∧
      ∀ x, Tendsto (fun j ↦ f j x) atTop (𝓝 (U.indicator (fun _ ↦ (1 : ℝ)) x)) := by
  obtain ⟨g, hgs, hgc, hg⟩ := hU.exists_contDiff_support_eq (n := ⊤)
  have hg' (x) : g x ∈ Icc 0 1 := hg (mem_range_self x)
  let θ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨j + 1, j + 2, by positivity, by linarith⟩
  let f (j : ℕ) : 𝓢(EuclideanSpace ℝ (Fin n), ℝ) :=
    ((θ j).hasCompactSupport.mul_right (f' := fun x ↦ 1 - (1 - g x) ^ j)).toSchwartzMap
      ((θ j).contDiff.mul (contDiff_const.sub ((contDiff_const.sub hgc).pow j)))
  have hf (j x) : f j x = θ j x * (1 - (1 - g x) ^ j) := rfl
  have hout {x} (hx : x ∉ U) : g x = 0 := by simpa [← hgs, Function.mem_support] using hx
  refine ⟨f, ?_, ?_⟩
  · intro j x
    have hp : (1 - g x) ^ j ∈ Icc 0 1 :=
      ⟨pow_nonneg (sub_nonneg.mpr (hg' x).2) _,
        pow_le_one₀ (sub_nonneg.mpr (hg' x).2) (by linarith [(hg' x).1])⟩
    rw [hf]
    refine ⟨mul_nonneg (θ j).nonneg (sub_nonneg.mpr hp.2), ?_⟩
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx]
      exact mul_le_one₀ (θ j).le_one (sub_nonneg.mpr hp.2) (by linarith [hp.1])
    · simp only [hout hx, sub_zero, one_pow, sub_self, mul_zero, indicator_of_notMem hx, le_refl]
  · intro x
    by_cases hx : x ∈ U
    · have hpos : 0 < g x := lt_of_le_of_ne (hg' x).1 (by
        simpa only [← hgs, Function.mem_support, ne_comm] using hx)
      simpa only [hf, indicator_of_mem hx] using tendsto_bump_mul_one_sub_pow_aux θ
        (fun j ↦ by dsimp [θ]; linarith) x ⟨hpos, (hg' x).2⟩
    · simpa only [hf, hout hx, sub_zero, one_pow, sub_self, mul_zero,
        indicator_of_notMem hx] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ))
          atTop (𝓝 0))

end NKBesicovitch
