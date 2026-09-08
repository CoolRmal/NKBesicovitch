/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Estimates
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Polynomially selectable projection schemes

A scheme has finitely many real coordinates and measurable labeled times.
Inside each positive-measure Borel subset of `[0,1]`, its parameter selection
has a polynomial measure lower bound. Both the parameter coordinates and
the projection-estimate constant have a uniform polynomial upper bound.
The selection is jointly Borel for measurable families of time sets.

The exponent bounds are natural numbers. The constructions use integer
powers, and allowing larger integer exponents preserves all requirements
on time sets of measure at most one.
-/

@[expose] public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection

/-- A finite-coordinate projection estimate with polynomially controlled measurable selection. -/
structure SelectableProjectionScheme (m : ℕ) (β : ℝ) (D L : ℕ) where
  label_pos : 0 < L
  time : (Fin D → ℝ) → Fin L → ℝ
  measurable_time : ∀ i, Measurable (fun σ ↦ time σ i)
  select : Set ℝ → Set (Fin D → ℝ)
  measurable_select : ∀ {X : Type} [MeasurableSpace X] (I : X → Set ℝ),
    MeasurableSet {p : X × ℝ | p.2 ∈ I p.1} →
      MeasurableSet {p : X × (Fin D → ℝ) | p.2 ∈ select (I p.1)}
  volumeExponent : ℕ
  volumeExponent_pos : 0 < volumeExponent
  boundExponent : ℕ
  boundExponent_pos : 0 < boundExponent
  lowerConstant : ℝ
  lowerConstant_pos : 0 < lowerConstant
  upperConstant : ℝ
  one_le_upperConstant : 1 ≤ upperConstant
  volume_lower : ∀ (I : Set ℝ), MeasurableSet I → I ⊆ Icc 0 1 → 0 < volume I →
    ENNReal.ofReal (lowerConstant * (volume I).toReal ^ volumeExponent) ≤ volume (select I)
  coordinates_bound : ∀ (I : Set ℝ), MeasurableSet I → I ⊆ Icc 0 1 → 0 < volume I →
    ∀ σ ∈ select I, ∀ j, |σ j| ≤ upperConstant * ((volume I).toReal⁻¹) ^ boundExponent
  time_mem : ∀ (I : Set ℝ), MeasurableSet I → I ⊆ Icc 0 1 → 0 < volume I →
    ∀ σ ∈ select I, ∀ i, time σ i ∈ I
  estimate : ∀ (I : Set ℝ), MeasurableSet I → I ⊆ Icc 0 1 → 0 < volume I →
    ∀ σ ∈ select I, ∀ G : Set (Line m), MeasurableSet G → IsBounded G →
      (volume G).toReal ≤ (upperConstant * ((volume I).toReal⁻¹) ^ boundExponent) *
        (parallelMultiplicity G).toReal ^ (2 - β) *
        (sliceSize (Finset.univ.image (time σ)) G).toReal ^ β

namespace SelectableProjectionScheme

variable {m D L : ℕ} {β : ℝ} (S : SelectableProjectionScheme m β D L)

theorem measurableSet_mem_select {X : Type} [MeasurableSpace X] {I : X → Set ℝ}
    (hI : MeasurableSet {p : X × ℝ | p.2 ∈ I p.1}) {σ : X → (Fin D → ℝ)}
    (hσ : Measurable σ) : MeasurableSet {x | σ x ∈ S.select (I x)} :=
  (S.measurable_select I hI).preimage (f := fun x ↦ (x, σ x)) (measurable_id.prodMk hσ)

theorem measurableSet_select {I : Set ℝ} (hI : MeasurableSet I) :
    MeasurableSet (S.select I) := by
  have h : MeasurableSet {p : Unit × (Fin D → ℝ) | p.2 ∈ S.select I} :=
    S.measurable_select (fun _ : Unit ↦ I) (hI.preimage measurable_snd)
  exact h.preimage (f := fun σ ↦ ((), σ)) (by fun_prop)

theorem select_nonempty {I : Set ℝ} (hI : MeasurableSet I) (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) : (S.select I).Nonempty := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  have hc := S.lowerConstant_pos
  apply nonempty_of_measure_ne_zero
  exact ((ENNReal.ofReal_pos.mpr (by positivity)).trans_le
    (S.volume_lower I hI hIunit hIpos)).ne'

theorem times_nonempty (σ : Fin D → ℝ) : (Finset.univ.image (S.time σ)).Nonempty := by
  exact ⟨S.time σ ⟨0, S.label_pos⟩, Finset.mem_image.mpr ⟨⟨0, S.label_pos⟩,
    Finset.mem_univ _, rfl⟩⟩

theorem hasProjectionEstimate {I : Set ℝ} (hI : MeasurableSet I) (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) {σ : Fin D → ℝ} (hσ : σ ∈ S.select I) :
    HasProjectionEstimate m β (Finset.univ.image (S.time σ)) := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  have hC := zero_lt_one.trans_le S.one_le_upperConstant
  exact ⟨S.upperConstant * ((volume I).toReal⁻¹) ^ S.boundExponent, by positivity,
    S.estimate I hI hIunit hIpos σ hσ⟩

end SelectableProjectionScheme

end NKBesicovitch.Projection.Selection
