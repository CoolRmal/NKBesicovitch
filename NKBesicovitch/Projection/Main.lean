/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerImprovement
public import NKBesicovitch.Projection.IterationPrinciple

/-!
# Projection estimates above the critical exponent

Every exponent strictly above `projectionExponent ≈ 1.675130871` admits
a finite nonempty height set and a uniform estimate for bounded Borel
line families. The infimum of the attainable exponents is the critical
root: continuity and the strict corner improvement exclude any larger
infimum. The theorem makes no endpoint assertion.

The stronger quantitative selection inside a prescribed measurable time
set is proved in `Projection.Selection.Main`.
-/

public section

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem exists_hasProjectionEstimate [Nonempty (Fin m)] {β : ℝ} (hβ : projectionExponent < β) :
    ∃ Γ : Finset ℝ, Γ.Nonempty ∧ HasProjectionEstimate m β Γ := by
  apply of_corner_improvement
    (P := fun γ ↦ ∃ Γ : Finset ℝ, Γ.Nonempty ∧ HasProjectionEstimate m γ Γ)
    ⟨{0, 1}, by simp, hasProjectionEstimate_twoSlice (by norm_num)⟩ _ hβ
  rintro γ γ' hγ hγ2 ⟨Γ, hΓ, hEstimate⟩ hgap
  exact hEstimate.corner_improvement hΓ hγ hγ2 hgap

end NKBesicovitch.Projection
