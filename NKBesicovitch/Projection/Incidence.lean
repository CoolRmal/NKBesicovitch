/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Defs
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Tactic.FunProp

/-!
# Slice multiplicities and intrinsic pair incidence

At height `a`, a line is encoded by its position `w` and slope. Pairs with a
common position use `(w, ξ₁, ξ₂)` and the product measure in these coordinates,
not the ambient measure on two copies of line space.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- The line at position `w` at height `a`, with slope `ξ`. -/
def lineAt (a : ℝ) (w ξ : Space m) : Line m := (w - a • ξ, ξ)

theorem atHeight_lineAt (a t : ℝ) (w ξ : Space m) :
    atHeight t (lineAt a w ξ) = w + (t - a) • ξ := by
  simp [atHeight, lineAt, sub_smul, sub_add_eq_add_sub, add_sub_assoc]

theorem lineAt_atHeight (a : ℝ) (g : Line m) : lineAt a (atHeight a g) g.2 = g := by
  simp [lineAt, atHeight]

/-- The volume-preserving change from position-slope coordinates to intercept-slope coordinates. -/
noncomputable def lineCoordinates (a : ℝ) : Line m ≃L[ℝ] Line m :=
  (ContinuousLinearEquiv.prodComm ℝ (Space m) (Space m)).trans
    (((ContinuousLinearEquiv.refl ℝ (Space m)).skewProd
      (ContinuousLinearEquiv.refl ℝ (Space m)) (-a • ContinuousLinearMap.id ℝ (Space m))).trans
        (ContinuousLinearEquiv.prodComm ℝ (Space m) (Space m)))

theorem lineCoordinates_apply (a : ℝ) (p : Line m) :
    lineCoordinates a p = lineAt a p.1 p.2 := by
  simp [lineCoordinates, lineAt, sub_eq_add_neg]

theorem measurePreserving_lineCoordinates (a : ℝ) :
    MeasurePreserving (lineCoordinates (m := m) a) volume volume := by
  change MeasurePreserving (fun p : Line m ↦ (p.1 + (-a) • p.2, p.2))
    (volume.prod volume) (volume.prod volume)
  have hs : MeasurePreserving (fun p : Line m ↦ (p.1, p.2 + (-a) • p.1))
      (volume.prod volume) (volume.prod volume) :=
    (MeasurePreserving.id (volume : Measure (Space m))).skew_product
      (by fun_prop)
      (ae_of_all _ fun ξ ↦ map_add_right_eq_self volume ((-a) • ξ))
  simpa [Function.comp_def] using
    Measure.measurePreserving_swap.comp (hs.comp Measure.measurePreserving_swap)

/-- Mass of the lines in a family passing through a specified point of a slice. -/
noncomputable def sliceMultiplicity (a : ℝ) (G : Set (Line m)) (w : Space m) : ℝ≥0∞ :=
  volume ((lineAt a w) ⁻¹' G)

theorem measurable_sliceMultiplicity (a : ℝ) {G : Set (Line m)} (hG : MeasurableSet G) :
    Measurable (sliceMultiplicity a G) := by
  change Measurable (fun w : Space m ↦ volume ((lineAt a w) ⁻¹' G))
  have hm := measurable_measure_prodMk_left
    (ν := (volume : Measure (Space m)))
    (hG.preimage (lineCoordinates a).continuous.measurable)
  have hc : ⇑(lineCoordinates (m := m) a) = fun p ↦ lineAt a p.1 p.2 :=
    funext (lineCoordinates_apply a)
  simpa only [hc, Set.preimage_preimage, Function.comp_def] using hm

theorem lintegral_sliceMultiplicity (a : ℝ) {G : Set (Line m)} (hG : MeasurableSet G) :
    (∫⁻ w, sliceMultiplicity a G w) = volume G := by
  have he := Measure.prod_apply (μ := (volume : Measure (Space m))) (ν := volume)
    (hG.preimage (lineCoordinates a).continuous.measurable)
  have hc : ⇑(lineCoordinates (m := m) a) = fun p ↦ lineAt a p.1 p.2 :=
    funext (lineCoordinates_apply a)
  calc
    (∫⁻ w, sliceMultiplicity a G w) = volume (lineCoordinates a ⁻¹' G) := by
      simpa only [sliceMultiplicity, hc, Set.preimage_preimage, Function.comp_def,
        Measure.volume_eq_prod] using he.symm
    _ = volume G := (measurePreserving_lineCoordinates a).measure_preimage hG.nullMeasurableSet

/-- Coordinates of two lines sharing a point at one height. -/
abbrev PairCoordinates (m : ℕ) := Space m × (Space m × Space m)

/-- The intrinsic incidence family of ordered pairs from `G` meeting at height `a`. -/
def pairFamily (a : ℝ) (G : Set (Line m)) : Set (PairCoordinates m) :=
  {p | lineAt a p.1 p.2.1 ∈ G ∧ lineAt a p.1 p.2.2 ∈ G}

theorem measurableSet_pairFamily (a : ℝ) {G : Set (Line m)} (hG : MeasurableSet G) :
    MeasurableSet (pairFamily a G) := by
  have h₁ : Measurable (fun p : PairCoordinates m ↦ lineAt a p.1 p.2.1) := by
    unfold lineAt
    fun_prop
  have h₂ : Measurable (fun p : PairCoordinates m ↦ lineAt a p.1 p.2.2) := by
    unfold lineAt
    fun_prop
  exact (hG.preimage h₁).inter (hG.preimage h₂)

theorem volume_pairFamily (a : ℝ) {G : Set (Line m)} (hG : MeasurableSet G) :
    volume (pairFamily a G) = ∫⁻ w, sliceMultiplicity a G w ^ 2 := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_pairFamily a hG)]
  apply lintegral_congr
  intro w
  change volume (((lineAt a w) ⁻¹' G) ×ˢ ((lineAt a w) ⁻¹' G)) = _
  rw [Measure.volume_eq_prod, Measure.prod_prod, pow_two]
  rfl

end NKBesicovitch.Projection
