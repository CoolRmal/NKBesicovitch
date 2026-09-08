/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.SeedScheme
public import NKBesicovitch.Projection.Selection.TreeScheme
public import NKBesicovitch.Projection.IterationPrinciple

/-!
# Selectable projection estimates above the critical exponent

In every positive slope dimension, every exponent strictly above
`projectionExponent` admits a polynomially controlled selectable scheme.
The finite numbers of coordinates and labels are chosen before the time
set and line family. No assertion is made at the critical endpoint.
-/

public section

namespace NKBesicovitch.Projection.Selection

theorem exists_selectableProjectionScheme (m : ℕ) [Nonempty (Fin m)]
    {β : ℝ} (hβ : projectionExponent < β) :
    ∃ D L : ℕ, Nonempty (SelectableProjectionScheme m β D L) := by
  apply of_corner_improvement (P := fun γ ↦ ∃ D L, Nonempty (SelectableProjectionScheme m γ D L))
    ⟨2, 2, ⟨twoSliceScheme m⟩⟩ _ hβ
  rintro γ γ' hγ hγ2 ⟨D, L, ⟨S⟩⟩ hgap
  exact S.corner_improvement hγ hγ2 hgap

end NKBesicovitch.Projection.Selection
