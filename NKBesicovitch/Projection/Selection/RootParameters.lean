/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.TreeMass

/-!
# Selecting the root triple together with its whole tree

Integrating over separated root triples adds three to the polynomial
selection exponent. The resulting family is jointly Borel and has
positive measure for every positive-measure Borel subset of the unit interval.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection.SelectableProjectionScheme

variable {m D L : ℕ} {β : ℝ} (S : SelectableProjectionScheme m β D L)

/-- Simultaneous selection of a separated root triple and all tree parameters. -/
noncomputable def rootParameters (I : Set ℝ) (J : ℕ) :
    Set (((ℝ × ℝ) × ℝ) × (TreeCoordinate D L J → ℝ)) :=
  {p | p.1 ∈ separatedTriples I ((volume I).toReal / 100) ∧
    p.2 ∈ S.treeParameters I J p.1}

theorem measurableSet_rootParameters_family (J : ℕ) {X : Type} [MeasurableSpace X]
    {I : Set (X × ℝ)} (hI : MeasurableSet I) :
    MeasurableSet {p : X × (((ℝ × ℝ) × ℝ) × (TreeCoordinate D L J → ℝ)) |
      p.2 ∈ S.rootParameters {t | (p.1, t) ∈ I} J} := by
  have hm : Measurable
      (fun p : X × (((ℝ × ℝ) × ℝ) × (TreeCoordinate D L J → ℝ)) ↦ (p.1, p.2.1)) :=
    measurable_fst.prodMk measurable_snd.fst
  have hr := (measurableSet_separatedTriples_family hI
    ((measurable_measure_prodMk_left (ν := volume) hI).ennreal_toReal.div_const 100)).preimage
    (f := fun p : X × (((ℝ × ℝ) × ℝ) × (TreeCoordinate D L J → ℝ)) ↦ (p.1, p.2.1))
    hm
  have hI' : MeasurableSet {p : (X × ((ℝ × ℝ) × ℝ)) × ℝ | (p.1.1, p.2) ∈ I} :=
    hI.preimage (measurable_fst.fst.prodMk measurable_snd)
  have ht := (S.measurableSet_treeParameters_family J hI' measurable_snd).preimage
    (f := fun p : X × (((ℝ × ℝ) × ℝ) × (TreeCoordinate D L J → ℝ)) ↦ ((p.1, p.2.1), p.2.2))
    ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)
  simpa only [rootParameters, preimage, mem_ofPred_eq, ofPred_and, mem_inter_iff] using hr.inter ht

theorem measurableSet_rootParameters {I : Set ℝ} (hI : MeasurableSet I) (J : ℕ) :
    MeasurableSet (S.rootParameters I J) := by
  have h := S.measurableSet_rootParameters_family J
    (X := Unit) (I := {p : Unit × ℝ | p.2 ∈ I}) (hI.preimage measurable_snd)
  exact h.preimage (f := fun p ↦ ((), p)) (by fun_prop)

theorem volume_rootParameters {I : Set ℝ} (hI : MeasurableSet I) (J : ℕ) :
    volume (S.rootParameters I J) =
      ∫⁻ q in separatedTriples I ((volume I).toReal / 100), volume (S.treeParameters I J q) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (S.measurableSet_rootParameters hI J),
    ← lintegral_indicator (measurableSet_separatedTriples hI _)]
  apply lintegral_congr
  intro q
  by_cases hq : q ∈ separatedTriples I ((volume I).toReal / 100)
  · rw [indicator_of_mem hq]
    congr 1
    ext σ
    simp only [rootParameters, mem_preimage, mem_ofPred_eq, hq, true_and]
  · rw [indicator_of_notMem hq]
    have he : Prod.mk q ⁻¹' S.rootParameters I J = ∅ := by
      ext σ
      simp only [rootParameters, mem_preimage, mem_ofPred_eq, hq, false_and,
        mem_empty_iff_false]
    rw [he, measure_empty]

/-- The full selection exponent includes three root coordinates. -/
theorem exists_root_volume_constant (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Set ℝ, MeasurableSet I → I ⊆ Icc 0 1 → 0 < volume I →
      ENNReal.ofReal (C * (volume I).toReal ^
        (3 + (4 + (8 + 6 * L) * S.volumeExponent) * treeNodeCount L J)) ≤
          volume (S.rootParameters I J) := by
  obtain ⟨C, hC, htree⟩ := S.exists_tree_volume_constant J
  refine ⟨C / 4, by positivity, fun I hI hIunit hIpos ↦ ?_⟩
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have ht := setLIntegral_mono' (μ := volume) (measurableSet_separatedTriples hI _)
    (htree I hI hIunit hIpos)
  rw [setLIntegral_const, ← S.volume_rootParameters hI J] at ht
  have h := le_trans (mul_le_mul le_rfl
    (quarter_cube_le_volume_separatedTriples hI hIfin) zero_le zero_le) ht
  rw [← ENNReal.ofReal_mul (by positivity)] at h
  convert h using 1
  · rfl
  · congr 1
    rw [pow_add]
    ring

theorem rootParameters_nonempty {I : Set ℝ} (hI : MeasurableSet I) (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) (J : ℕ) : (S.rootParameters I J).Nonempty := by
  obtain ⟨C, hC, hbound⟩ := S.exists_root_volume_constant J
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  exact nonempty_of_measure_ne_zero
    ((ENNReal.ofReal_pos.mpr (by positivity)).trans_le (hbound I hI hIunit hIpos)).ne'

end NKBesicovitch.Projection.Selection.SelectableProjectionScheme
