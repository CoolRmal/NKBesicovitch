/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Exponents
public import Mathlib.Tactic.Ring

/-!
# Strict margins for the mixed-norm induction

The target dimension inequality can be preserved while moving the X-ray ratio
strictly below the critical value. Equivalently, a projection exponent strictly
above its endpoint suffices; no endpoint projection estimate is needed.
-/

public section

open Set
open scoped Topology

namespace NKBesicovitch.Induction

theorem exists_ratio_lt_criticalExponent {n k : ℕ}
    (h : (n : ℝ) < criticalExponent ^ (k - 1) + (k : ℝ)) :
    ∃ ρ ∈ Ioo 2 criticalExponent, (n : ℝ) < ρ ^ (k - 1) + (k : ℝ) := by
  have hc : Continuous (fun ρ : ℝ ↦ ρ ^ (k - 1) + (k : ℝ)) := by fun_prop
  obtain ⟨l, u, hlu, hs⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp ((isOpen_lt continuous_const hc).mem_nhds h)
  have hp : 2 < criticalExponent := by linarith [criticalExponent_bounds.1]
  obtain ⟨ρ, hlρ, hρp⟩ := exists_between (max_lt hp hlu.1)
  exact ⟨ρ, ⟨(le_max_left 2 l).trans_lt hlρ, hρp⟩,
    hs ⟨(le_max_right 2 l).trans_lt hlρ, hρp.trans hlu.2⟩⟩

/-- A strictly supercritical projection exponent already suffices for every target dimension. -/
theorem exists_projectionExponent_for_dimension {n k : ℕ}
    (h : (n : ℝ) < criticalExponent ^ (k - 1) + (k : ℝ)) :
    ∃ β ∈ Ioo projectionExponent 2,
      (n : ℝ) < (β / (β - 1)) ^ (k - 1) + (k : ℝ) := by
  obtain ⟨ρ, hρ, hn⟩ := exists_ratio_lt_criticalExponent h
  have hd : 0 < ρ - 1 := by linarith [hρ.1]
  have hp : 0 < criticalExponent - 1 := by linarith [criticalExponent_bounds.1]
  have hβ : projectionExponent < ρ / (ρ - 1) := by
    rw [projectionExponent, div_lt_div_iff₀ hp hd]
    nlinarith [hρ.2]
  have hi : ρ / (ρ - 1) / (ρ / (ρ - 1) - 1) = ρ := by
    field_simp
    ring
  refine ⟨ρ / (ρ - 1), ⟨hβ, (div_lt_iff₀ hd).2 (by linarith [hρ.1])⟩, ?_⟩
  rwa [hi]

end NKBesicovitch.Induction
