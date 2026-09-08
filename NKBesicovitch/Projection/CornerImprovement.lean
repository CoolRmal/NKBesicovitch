/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerNormalizedImprovement
public import NKBesicovitch.Projection.Normalization

/-!
# The full corner improvement of projection estimates

An input estimate at `1 < β ≤ 2` yields every strict exponent above the
corner update on a new finite nonempty set of heights. All constants and
heights are independent of the bounded Borel line family. Spatial dilation
restores the exact parallel-multiplicity factor in the general estimate.
-/

public section

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem HasProjectionEstimate.corner_improvement [Nonempty (Fin m)]
    {β β' : ℝ} {Γ : Finset ℝ} (hEstimate : HasProjectionEstimate m β Γ)
    (hΓ : Γ.Nonempty) (hβ : 1 < β) (hβ2 : β ≤ 2) (hgap : cornerUpdate β < β') :
    ∃ Δ : Finset ℝ, Δ.Nonempty ∧ HasProjectionEstimate m β' Δ := by
  obtain ⟨Δ, hΔ, C, hC, hbound⟩ := exists_normalized_corner_improvement hβ hβ2 hgap hΓ hEstimate
  exact ⟨Δ, hΔ, hasProjectionEstimate_of_normalized hΔ hC hbound⟩

end NKBesicovitch.Projection
