/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Incidence
public import NKBesicovitch.Projection.Parallel
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Finite masses of bounded line families

The projection estimate is stated for bounded Borel line families. Boundedness
also controls projection images and intrinsic incidence pairs, justifying the
finite real quantities and divisions in the amplification argument.
-/

public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem isBounded_projection (t : ℝ) {G : Set (Line m)} (hG : IsBounded G) :
    IsBounded (atHeight t '' G) := by
  let f : Line m →L[ℝ] Space m := ContinuousLinearMap.fst ℝ (Space m) (Space m) +
    t • ContinuousLinearMap.snd ℝ (Space m) (Space m)
  exact f.lipschitz.isBounded_image hG

theorem isBounded_pairFamily (a : ℝ) {G : Set (Line m)} (hG : IsBounded G) :
    IsBounded (pairFamily a G) := by
  apply ((isBounded_projection a hG).prod (hG.image_snd.prod hG.image_snd)).subset
  intro p hp
  refine ⟨⟨lineAt a p.1 p.2.1, hp.1, ?_⟩,
    ⟨lineAt a p.1 p.2.1, hp.1, rfl⟩, ⟨lineAt a p.1 p.2.2, hp.2, rfl⟩⟩
  simp [atHeight_lineAt]

theorem volume_projection_ne_top (t : ℝ) {G : Set (Line m)} (hG : IsBounded G) :
    volume (atHeight t '' G) ≠ ∞ := (isBounded_projection t hG).measure_lt_top.ne

theorem volume_pairFamily_ne_top (a : ℝ) {G : Set (Line m)} (hG : IsBounded G) :
    volume (pairFamily a G) ≠ ∞ := (isBounded_pairFamily a hG).measure_lt_top.ne

theorem parallelMultiplicity_ne_top {G : Set (Line m)} (hG : IsBounded G) :
    parallelMultiplicity G ≠ ∞ :=
  ne_top_of_le_ne_top (volume_projection_ne_top 0 hG) (parallelMultiplicity_le_projection G 0)

theorem sliceSize_ne_top (Γ : Finset ℝ) {G : Set (Line m)} (hG : IsBounded G) :
    sliceSize Γ G ≠ ∞ := by
  simpa only [sliceSize, iSup_subtype] using
    (iSup_ne_top fun t : Γ ↦ volume_projection_ne_top t hG)

end NKBesicovitch.Projection
