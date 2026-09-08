/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Defs
public import Mathlib.MeasureTheory.Group.Prod

/-!
# Parallel multiplicity and projection sizes

Every parallel fiber translates into each projection image. Thus its essential
supremum is bounded by every slice size. Tonelli identifies the zero-multiplicity
case with zero line-family mass, before any normalization by multiplicity.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem parallelMultiplicity_mono {F G : Set (Line m)} (hFG : F ⊆ G) :
    parallelMultiplicity F ≤ parallelMultiplicity G := by
  exact essSup_mono_ae (ae_of_all _ fun _ ↦ measure_mono fun _ hx ↦ hFG hx)

theorem parallelMultiplicity_le_projection (G : Set (Line m)) (t : ℝ) :
    parallelMultiplicity G ≤ volume (atHeight t '' G) := by
  refine essSup_le_of_ae_le _ ?_
  apply ae_of_all
  intro ξ
  calc
    volume {x : Space m | (x, ξ) ∈ G} ≤
        volume ((fun x : Space m ↦ x + t • ξ) ⁻¹' (atHeight t '' G)) :=
      measure_mono fun x hx ↦ ⟨(x, ξ), hx, rfl⟩
    _ = volume (atHeight t '' G) := measure_preimage_add_right volume (t • ξ) _

theorem parallelMultiplicity_eq_zero_iff {G : Set (Line m)} (hG : MeasurableSet G) :
    parallelMultiplicity G = 0 ↔ volume G = 0 := by
  rw [parallelMultiplicity, ENNReal.essSup_eq_zero_iff, Measure.volume_eq_prod,
    Measure.prod_apply_symm hG, lintegral_eq_zero_iff (measurable_measure_prodMk_right hG)]
  rfl

theorem parallelMultiplicity_pos {G : Set (Line m)} (hG : MeasurableSet G)
    (hpos : 0 < volume G) : 0 < parallelMultiplicity G := by
  exact pos_iff_ne_zero.mpr fun hz ↦ hpos.ne' ((parallelMultiplicity_eq_zero_iff hG).mp hz)

end NKBesicovitch.Projection
