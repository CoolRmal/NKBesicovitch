/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Geometry.DirectionChart
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# A finite cover by bounded slope charts

Compactness gives finitely many caps with normal component at least
`1/2`. Each cap is parametrized by a Borel slope set inside the ball of
radius two. This cover uses arbitrary unit normals, so no exceptional
coordinate directions or orientation choices are needed.
-/

public section

open MeasureTheory Set Submodule Metric Bornology
open scoped InnerProductSpace

namespace NKBesicovitch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_finite_normal_cap_cover [FiniteDimensional ℝ E] :
    ∃ s : Finset (sphere (0 : E) 1), ∀ w : sphere (0 : E) 1,
      ∃ v ∈ s, (1 / 2 : ℝ) < ⟪(v : E), (w : E)⟫_ℝ := by
  let : CompactSpace (sphere (0 : E) 1) := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  have hopen (v : sphere (0 : E) 1) :
      IsOpen {w : sphere (0 : E) 1 | (1 / 2 : ℝ) < ⟪(v : E), (w : E)⟫_ℝ} :=
    isOpen_lt continuous_const (continuous_const.inner continuous_subtype_val)
  have hcover : (univ : Set (sphere (0 : E) 1)) ⊆
      ⋃ v : sphere (0 : E) 1, {w | (1 / 2 : ℝ) < ⟪(v : E), (w : E)⟫_ℝ} := by
    intro w _
    apply mem_iUnion.mpr
    refine ⟨w, ?_⟩
    simp only [mem_ofPred_eq, real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere w]
    norm_num
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover _ hopen hcover
  refine ⟨s, fun w ↦ ?_⟩
  obtain ⟨v, hv⟩ := mem_iUnion.mp (hs (mem_univ w))
  obtain ⟨hvs, hvw⟩ := mem_iUnion.mp hv
  exact ⟨v, hvs, hvw⟩

theorem measurableSet_normalSlopes [MeasurableSpace E] [BorelSpace E]
    {v : E} (hv : ‖v‖ = 1) (c : ℝ) :
    MeasurableSet {ξ : (ℝ ∙ v)ᗮ | c ≤ ⟪v, (normalDirection hv ξ : E)⟫_ℝ} := by
  apply measurableSet_le measurable_const
  exact (continuous_const.inner (continuous_subtype_val.comp
    (continuous_normalDirection hv))).measurable

theorem isBounded_normalSlopes {v : E} (hv : ‖v‖ = 1) {c : ℝ} (hc : 0 < c) :
    IsBounded {ξ : (ℝ ∙ v)ᗮ | c ≤ ⟪v, (normalDirection hv ξ : E)⟫_ℝ} := by
  apply isBounded_closedBall.subset (t := closedBall (0 : (ℝ ∙ v)ᗮ) (1 / c))
  intro ξ hξ
  simpa only [mem_closedBall, dist_zero_right] using norm_slope_le_of_inner_lower hv hc hξ

theorem exists_finite_bounded_slope_cover [FiniteDimensional ℝ E] :
    ∃ s : Finset (sphere (0 : E) 1), ∀ w : sphere (0 : E) 1,
      ∃ v ∈ s, ∃ ξ : (ℝ ∙ (v : E))ᗮ,
        (1 / 2 : ℝ) ≤ ⟪(v : E), (normalDirection (norm_eq_of_mem_sphere v) ξ : E)⟫_ℝ ∧
          normalDirection (norm_eq_of_mem_sphere v) ξ = w := by
  obtain ⟨s, hs⟩ := exists_finite_normal_cap_cover (E := E)
  refine ⟨s, fun w ↦ ?_⟩
  obtain ⟨v, hv, hvw⟩ := hs w
  have hpos : 0 < ⟪(v : E), (w : E)⟫_ℝ := lt_trans (by norm_num) hvw
  have heq := normalDirection_slope (norm_eq_of_mem_sphere v) w hpos
  refine ⟨v, hv, _, ?_, heq⟩
  rw [heq]
  exact hvw.le

end NKBesicovitch
