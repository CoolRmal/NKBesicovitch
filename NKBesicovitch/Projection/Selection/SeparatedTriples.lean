/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.SeparatedTimes
public import Mathlib.Tactic.Ring

/-!
# Selecting separated root triples

Choose a separated pair and then a third time away from both pair
coordinates. At separation `|I|/100`, the available triple measure is
at least `|I|³/4`. The relation is jointly Borel in measurable families
of time sets and separation radii.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection

/-- Three times in `I`, each pair separated by at least `r`. -/
def separatedTriples (I : Set ℝ) (r : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  {p | p.1 ∈ separatedPairs I r ∧ p.2 ∈ separatedTimes I ![p.1.1, p.1.2] Finset.univ r}

theorem mem_separatedTriples {I : Set ℝ} {r : ℝ} {p : (ℝ × ℝ) × ℝ} :
    p ∈ separatedTriples I r ↔ p.1.1 ∈ I ∧ p.1.2 ∈ I ∧ p.2 ∈ I ∧
      r ≤ dist p.1.1 p.1.2 ∧ r ≤ dist p.1.1 p.2 ∧ r ≤ dist p.1.2 p.2 := by
  simp only [separatedTriples, mem_ofPred_eq, separatedPairs, mem_inter_iff, mem_prod,
    mem_separatedTimes, Finset.mem_univ, forall_true_left, Fin.forall_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, dist_comm,
    and_assoc, and_left_comm, and_comm]

theorem measurableSet_separatedTriples {I : Set ℝ} (hI : MeasurableSet I) (r : ℝ) :
    MeasurableSet (separatedTriples I r) := by
  have he : separatedTriples I r = {p : (ℝ × ℝ) × ℝ | p.1.1 ∈ I ∧ p.1.2 ∈ I ∧ p.2 ∈ I ∧
      r ≤ dist p.1.1 p.1.2 ∧ r ≤ dist p.1.1 p.2 ∧ r ≤ dist p.1.2 p.2} := by
    ext p
    exact mem_separatedTriples
  rw [he]
  exact (hI.preimage measurable_fst.fst).inter ((hI.preimage measurable_fst.snd).inter
    ((hI.preimage measurable_snd).inter
      ((measurableSet_le measurable_const (measurable_fst.fst.dist measurable_fst.snd)).inter
        ((measurableSet_le measurable_const (measurable_fst.fst.dist measurable_snd)).inter
          (measurableSet_le measurable_const (measurable_fst.snd.dist measurable_snd))))))

theorem measurableSet_separatedTriples_family {X : Type*} [MeasurableSpace X]
    {I : Set (X × ℝ)} (hI : MeasurableSet I) {r : X → ℝ} (hr : Measurable r) :
    MeasurableSet {p : X × ((ℝ × ℝ) × ℝ) |
      p.2 ∈ separatedTriples {t | (p.1, t) ∈ I} (r p.1)} := by
  simp only [mem_separatedTriples]
  exact (hI.preimage (measurable_fst.prodMk measurable_snd.fst.fst)).inter
    ((hI.preimage (measurable_fst.prodMk measurable_snd.fst.snd)).inter
      ((hI.preimage (measurable_fst.prodMk measurable_snd.snd)).inter
        ((measurableSet_le (hr.comp measurable_fst)
          (measurable_snd.fst.fst.dist measurable_snd.fst.snd)).inter
          ((measurableSet_le (hr.comp measurable_fst)
            (measurable_snd.fst.fst.dist measurable_snd.snd)).inter
            (measurableSet_le (hr.comp measurable_fst)
              (measurable_snd.fst.snd.dist measurable_snd.snd))))))

theorem volume_separatedTriples {I : Set ℝ} (hI : MeasurableSet I) (r : ℝ) :
    volume (separatedTriples I r) =
      ∫⁻ p in separatedPairs I r, volume (separatedTimes I ![p.1, p.2] Finset.univ r) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_separatedTriples hI r)]
  have he : (fun p ↦ volume (Prod.mk p ⁻¹' separatedTriples I r)) =
      (separatedPairs I r).indicator
        (fun p ↦ volume (separatedTimes I ![p.1, p.2] Finset.univ r)) := by
    funext p
    by_cases hp : p ∈ separatedPairs I r
    · rw [Set.indicator_of_mem hp]
      congr 1
      ext t
      simp only [separatedTriples, mem_preimage, mem_ofPred_eq, hp, true_and]
    · rw [Set.indicator_of_notMem hp]
      have hz : Prod.mk p ⁻¹' separatedTriples I r = ∅ := by
        ext t
        simp only [separatedTriples, mem_preimage, mem_ofPred_eq, hp, false_and,
          mem_empty_iff_false]
      rw [hz, measure_empty]
  rw [he, lintegral_indicator (measurableSet_separatedPairs hI r)]

theorem quarter_cube_le_volume_separatedTriples {I : Set ℝ} (hI : MeasurableSet I)
    (hIfin : volume I ≠ ∞) :
    ENNReal.ofReal ((volume I).toReal ^ 3 / 4) ≤
      volume (separatedTriples I ((volume I).toReal / 100)) := by
  have hmass : ENNReal.ofReal ((volume I).toReal / 2) *
      volume (separatedPairs I ((volume I).toReal / 100)) ≤
        volume (separatedTriples I ((volume I).toReal / 100)) := by
    rw [volume_separatedTriples hI, ← setLIntegral_const]
    exact lintegral_mono fun p ↦ half_volume_le_separatedTimes_pair p.1 p.2
  refine le_trans ?_ hmass
  calc
    _ = ENNReal.ofReal ((volume I).toReal / 2) * ENNReal.ofReal ((volume I).toReal ^ 2 / 2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ ≤ _ := mul_le_mul le_rfl (half_square_le_volume_separatedPairs hI hIfin) zero_le zero_le

end NKBesicovitch.Projection.Selection
