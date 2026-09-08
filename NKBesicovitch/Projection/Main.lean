/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerImprovement
public import NKBesicovitch.Projection.IterationBounds
public import Mathlib.Topology.Order.Monotone

/-!
# Projection estimates above the critical exponent

Every exponent strictly above `projectionExponent ≈ 1.675130871` admits
a finite nonempty height set and a uniform estimate for bounded Borel
line families. The infimum of the attainable exponents is the critical
root: continuity and the strict corner improvement exclude any larger
infimum. The theorem makes no endpoint assertion.

Quantitative selection of the heights inside a prescribed measurable set,
needed for the mixed-norm X-ray transfer, is a further result.
-/

public section

open MeasureTheory Set
open scoped Topology

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem exists_hasProjectionEstimate [Nonempty (Fin m)] {β : ℝ} (hβ : projectionExponent < β) :
    ∃ Γ : Finset ℝ, Γ.Nonempty ∧ HasProjectionEstimate m β Γ := by
  classical
  let S : Set ℝ := {γ | projectionExponent < γ ∧ γ ≤ 2 ∧
    ∃ Γ : Finset ℝ, Γ.Nonempty ∧ HasProjectionEstimate m γ Γ}
  have htwo : (2 : ℝ) ∈ S := ⟨projectionExponent_mem.2, le_rfl,
    {0, 1}, by simp, hasProjectionEstimate_twoSlice (by norm_num)⟩
  have hS : S.Nonempty := ⟨2, htwo⟩
  have hbelow : BddBelow S := ⟨projectionExponent, fun γ hγ ↦ hγ.1.le⟩
  have hInf : sInf S = projectionExponent := by
    apply le_antisymm _ (le_csInf hS (fun γ hγ ↦ hγ.1.le))
    by_contra! hroot
    have hneigh : {γ | cornerUpdate γ < sInf S} ∈ 𝓝 (sInf S) :=
      (continuousAt_cornerUpdate (projectionExponent_mem.1.trans hroot)).eventually_lt_const
        (cornerUpdate_lt_self_of_gt hroot)
    obtain ⟨γ, hγupdate, hγ⟩ := mem_closure_iff_nhds.mp (csInf_mem_closure hS hbelow) _ hneigh
    obtain ⟨γ', hγ'lower, hγ'upper⟩ := exists_between (max_lt hroot hγupdate)
    obtain ⟨Γ, hΓ, hEstimate⟩ := hγ.2.2
    obtain ⟨Δ, hΔ, hImproved⟩ := hEstimate.corner_improvement hΓ
      (projectionExponent_mem.1.trans hγ.1) hγ.2.1 ((le_max_right _ _).trans_lt hγ'lower)
    have hγ'S : γ' ∈ S := ⟨(le_max_left _ _).trans_lt hγ'lower,
      hγ'upper.le.trans (csInf_le hbelow htwo), Δ, hΔ, hImproved⟩
    exact (not_lt_of_ge (csInf_le hbelow hγ'S)) hγ'upper
  obtain ⟨γ, hγ, hγβ⟩ := exists_lt_of_csInf_lt hS (hInf.symm ▸ hβ)
  obtain ⟨Γ, hΓ, hEstimate⟩ := hγ.2.2
  exact hEstimate.corner_improvement hΓ (projectionExponent_mem.1.trans hγ.1) hγ.2.1
    ((cornerUpdate_lt_self_of_gt hγ.1).trans hγβ)

end NKBesicovitch.Projection
