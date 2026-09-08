/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.IterationBounds
public import Mathlib.Topology.Order.Monotone

/-!
# Approximation to the critical exponent by corner improvement

Any property available at exponent two and preserved by the strict corner
improvement holds at every exponent above the critical root. The argument
applies both to finite-height estimates and to selectable schemes.
-/

public section

open Set
open scoped Topology

namespace NKBesicovitch.Projection

theorem of_corner_improvement {P : ℝ → Prop} (htwo : P 2)
    (himprove : ∀ {β γ : ℝ}, 1 < β → β ≤ 2 → P β → cornerUpdate β < γ → P γ)
    {β : ℝ} (hβ : projectionExponent < β) : P β := by
  let S : Set ℝ := {γ | projectionExponent < γ ∧ γ ≤ 2 ∧ P γ}
  have htwoS : (2 : ℝ) ∈ S := ⟨projectionExponent_mem.2, le_rfl, htwo⟩
  have hS : S.Nonempty := ⟨2, htwoS⟩
  have hbelow : BddBelow S := ⟨projectionExponent, fun γ hγ ↦ hγ.1.le⟩
  have hInf : sInf S = projectionExponent := by
    apply le_antisymm _ (le_csInf hS (fun γ hγ ↦ hγ.1.le))
    by_contra! hroot
    have hneigh : {γ | cornerUpdate γ < sInf S} ∈ 𝓝 (sInf S) :=
      (continuousAt_cornerUpdate (projectionExponent_mem.1.trans hroot)).eventually_lt_const
        (cornerUpdate_lt_self_of_gt hroot)
    obtain ⟨γ, hγupdate, hγ⟩ := mem_closure_iff_nhds.mp (csInf_mem_closure hS hbelow) _ hneigh
    obtain ⟨γ', hγ'lower, hγ'upper⟩ := exists_between (max_lt hroot hγupdate)
    have hγ'S : γ' ∈ S := ⟨(le_max_left _ _).trans_lt hγ'lower,
      hγ'upper.le.trans (csInf_le hbelow htwoS),
      himprove (projectionExponent_mem.1.trans hγ.1) hγ.2.1 hγ.2.2
        ((le_max_right _ _).trans_lt hγ'lower)⟩
    exact (not_lt_of_ge (csInf_le hbelow hγ'S)) hγ'upper
  obtain ⟨γ, hγ, hγβ⟩ := exists_lt_of_csInf_lt hS (hInf.symm ▸ hβ)
  exact himprove (projectionExponent_mem.1.trans hγ.1) hγ.2.1 hγ.2.2
    ((cornerUpdate_lt_self_of_gt hγ.1).trans hγβ)

end NKBesicovitch.Projection
