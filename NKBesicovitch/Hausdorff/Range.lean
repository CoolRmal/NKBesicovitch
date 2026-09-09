/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Hausdorff.Transfer
public import NKBesicovitch.Induction.Iteration

/-!
# Hausdorff dimension at the critical exponent

Finite plate induction gives the dimension bound for every ratio strictly
below the critical exponent. Continuity gives the endpoint dimension
inequality without asserting an endpoint maximal estimate.
-/

public section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace NKBesicovitch.Hausdorff

theorem dimH_eq_of_isBesicovitch_self {n : ℕ} {E : Set (EuclideanSpace ℝ (Fin n))}
    (hB : IsBesicovitch n E) : dimH E = n := by
  obtain ⟨a, ha⟩ := hB ⊤ (by simp)
  have hball : ball a 1 ⊆ E := by
    intro x hx
    have hn : ‖x - a‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hx
    simpa using ha (x - a) (Submodule.mem_top) hn.le
  simpa using Real.dimH_of_mem_nhds (mem_of_superset (ball_mem_nhds a zero_lt_one) hball)

theorem le_dimH_of_subcritical_ratio {n k : ℕ} (hkn : k < n)
    {ρ : ℝ} (hρ : ρ ∈ Ioo 2 criticalExponent) {E : Set (EuclideanSpace ℝ (Fin n))}
    (hB : IsBesicovitch k E) :
    ENNReal.ofReal ((n : ℝ) - ((n : ℝ) - k) / ρ ^ k) ≤ dimH E := by
  obtain ⟨p, hp, hplate⟩ := Induction.exists_hasPlateEstimate_codimension (n - k) k
    (by omega) hρ
  have hn : n - k + k = n := Nat.sub_add_cancel hkn.le
  have hplate' : Induction.HasPlateEstimate hkn.le (((n : ℝ) - k) / ρ ^ k) p := by
    simpa only [hn, Nat.cast_sub hkn.le] using hplate
  exact hplate'.le_dimH (by linarith) hB

/-- The critical exponent gives the Hausdorff lower bound in every admissible dimension. -/
theorem le_dimH_of_isBesicovitch {n k : ℕ} (_hk : 1 ≤ k) (hkn : k ≤ n)
    {E : Set (EuclideanSpace ℝ (Fin n))} (hB : IsBesicovitch k E) :
    ENNReal.ofReal ((n : ℝ) - ((n : ℝ) - k) / criticalExponent ^ k) ≤ dimH E := by
  obtain rfl | hkn := eq_or_lt_of_le hkn
  · simp [dimH_eq_of_isBesicovitch_self hB]
  · have hpc : 2 < criticalExponent := by linarith [criticalExponent_bounds.1]
    have hpc0 : criticalExponent ≠ 0 := (zero_lt_two.trans hpc).ne'
    have hc : ContinuousAt (fun ρ : ℝ ↦ (n : ℝ) - ((n : ℝ) - k) / ρ ^ k)
        criticalExponent :=
      continuousAt_const.sub (continuousAt_const.div (continuousAt_id.pow k) (pow_ne_zero k hpc0))
    apply le_of_tendsto ((ENNReal.continuous_ofReal.continuousAt.comp hc).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[<] criticalExponent ≤ 𝓝 criticalExponent))
    filter_upwards [Ioo_mem_nhdsLT hpc] with ρ hρ
    exact le_dimH_of_subcritical_ratio hkn hρ hB

end NKBesicovitch.Hausdorff
