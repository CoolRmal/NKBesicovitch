/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.CornerOuterTimes

/-!
# Quantitative selection of a common corner scalar

Retain scalars with at least `δ|I|⁷/320000000000` of compatible outer
times. At least half of the compatible time-scalar measure survives,
and the retained scalars have measure at least `δ|I|³/160000`.
Every compatible outer time supplies an inner dual-pair reservoir.
Both levels of time selection are jointly Borel.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection

/-- Common corner scalars with sufficiently many compatible outer times. -/
noncomputable def cornerReservoir (I : Set ℝ) (a b c δ : ℝ) : Set ℝ :=
  {κ | ENNReal.ofReal (δ * (volume I).toReal ^ 7 / 320000000000) ≤
    volume (cornerOuterTimes I a b c δ κ)}

theorem measurableSet_cornerReservoir {I : Set ℝ} (hI : MeasurableSet I) (a b c δ : ℝ) :
    MeasurableSet (cornerReservoir I a b c δ) :=
  measurableSet_le measurable_const (measurable_volume_cornerOuterTimes hI a b c δ)

theorem measurableSet_cornerReservoir_family {X : Type*} [MeasurableSpace X]
    {I : Set (X × ℝ)} (hI : MeasurableSet I) {a b c δ : X → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) (hδ : Measurable δ) :
    MeasurableSet {p : X × ℝ | p.2 ∈ cornerReservoir {t | (p.1, t) ∈ I}
      (a p.1) (b p.1) (c p.1) (δ p.1)} := by
  have hL := (measurable_measure_prodMk_left (ν := volume) hI).ennreal_toReal
  exact measurableSet_le
    (((hδ.mul (hL.pow_const 7)).div_const 320000000000).ennreal_ofReal.comp measurable_fst)
    (measurable_volume_cornerOuterTimes_family hI ha hb hc hδ)

theorem cornerReservoir_scalar_bounds {I : Set ℝ} (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) {a b c δ : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (hc : c ∈ Icc 0 1) (hδ : 0 < δ) (hab : δ ≤ dist a b) {κ : ℝ}
    (hκ : κ ∈ cornerReservoir I a b c δ) :
    κ ≠ 0 ∧ δ * ((volume I).toReal / 100) ^ 2 ≤ |κ| ∧
      |κ| ≤ (100 / (volume I).toReal) ^ 3 := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  have hpos : 0 < volume (cornerOuterTimes I a b c δ κ) :=
    (ENNReal.ofReal_pos.mpr (by positivity)).trans_le hκ
  obtain ⟨u, hu⟩ := nonempty_of_measure_ne_zero hpos.ne'
  exact cornerTimeRelation_scalar_bounds hIunit hIpos ha hb hc hδ hab hu

theorem volume_cornerReservoir_ne_top {I : Set ℝ} (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) {a b c δ : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (hc : c ∈ Icc 0 1) (hδ : 0 < δ) (hab : δ ≤ dist a b) :
    volume (cornerReservoir I a b c δ) ≠ ∞ := by
  have hsub : cornerReservoir I a b c δ ⊆
      Icc (-((100 / (volume I).toReal) ^ 3)) ((100 / (volume I).toReal) ^ 3) :=
    fun _ hκ ↦ abs_le.mp (cornerReservoir_scalar_bounds hIunit hIpos ha hb hc hδ hab hκ).2.2
  exact ne_top_of_le_ne_top (by simp) (measure_mono hsub)

theorem lintegral_cornerOuterTimes_discarded_le {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b c δ : ℝ}
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hc : c ∈ Icc 0 1)
    (hδ : 0 < δ) (hab : δ ≤ dist a b) :
    (∫⁻ κ in (cornerReservoir I a b c δ)ᶜ, volume (cornerOuterTimes I a b c δ κ)) ≤
      ENNReal.ofReal (δ * (volume I).toReal ^ 4 / 160000) := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  have h := setLIntegral_lt_le_mul_measure (μ := volume)
    (measurable_volume_cornerOuterTimes hI a b c δ)
    (support_volume_cornerOuterTimes_subset hIunit hIpos ha hb hc hδ hab)
    (ENNReal.ofReal (δ * (volume I).toReal ^ 7 / 320000000000))
  have hcomp : (cornerReservoir I a b c δ)ᶜ =
      {κ | volume (cornerOuterTimes I a b c δ κ) <
        ENNReal.ofReal (δ * (volume I).toReal ^ 7 / 320000000000)} := by
    ext κ
    simp only [cornerReservoir, mem_compl_iff, mem_ofPred_eq, not_le]
  rw [hcomp]
  refine h.trans_eq ?_
  rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

theorem lintegral_cornerOuterTimes_retained_lower {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b c δ : ℝ}
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hc : c ∈ Icc 0 1)
    (hδ : 0 < δ) (hab : δ ≤ dist a b) :
    ENNReal.ofReal (δ * (volume I).toReal ^ 4 / 160000) ≤
      ∫⁻ κ in cornerReservoir I a b c δ, volume (cornerOuterTimes I a b c δ κ) := by
  apply ENNReal.le_of_add_le_add_left (a := ENNReal.ofReal (δ * (volume I).toReal ^ 4 / 160000))
    ENNReal.ofReal_ne_top
  calc
    _ = ENNReal.ofReal (δ * (volume I).toReal ^ 4 / 80000) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    _ ≤ volume (cornerTimeRelation I a b c δ) :=
      volume_cornerTimeRelation_lower hI hIunit hIpos ha hb hc hδ hab
    _ = (∫⁻ κ in cornerReservoir I a b c δ, volume (cornerOuterTimes I a b c δ κ)) +
        ∫⁻ κ in (cornerReservoir I a b c δ)ᶜ, volume (cornerOuterTimes I a b c δ κ) :=
      (lintegral_volume_cornerOuterTimes hI a b c δ).symm.trans
        (lintegral_add_compl _ (measurableSet_cornerReservoir hI a b c δ)).symm
    _ ≤ (∫⁻ κ in cornerReservoir I a b c δ, volume (cornerOuterTimes I a b c δ κ)) +
        ENNReal.ofReal (δ * (volume I).toReal ^ 4 / 160000) :=
      add_le_add le_rfl (lintegral_cornerOuterTimes_discarded_le hI hIunit hIpos ha hb hc hδ hab)
    _ = _ := add_comm _ _

theorem volume_cornerReservoir_lower {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b c δ : ℝ}
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hc : c ∈ Icc 0 1)
    (hδ : 0 < δ) (hab : δ ≤ dist a b) :
    ENNReal.ofReal (δ * (volume I).toReal ^ 3 / 160000) ≤
      volume (cornerReservoir I a b c δ) := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  apply (ENNReal.mul_le_mul_iff_right hIpos.ne' hIfin).mp
  calc
    _ = ENNReal.ofReal (δ * (volume I).toReal ^ 4 / 160000) := by
      conv_lhs => arg 1; rw [← ENNReal.ofReal_toReal hIfin]
      rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      congr 1
      ring
    _ ≤ ∫⁻ κ in cornerReservoir I a b c δ, volume (cornerOuterTimes I a b c δ κ) :=
      lintegral_cornerOuterTimes_retained_lower hI hIunit hIpos ha hb hc hδ hab
    _ ≤ volume I * volume (cornerReservoir I a b c δ) := by
      rw [← setLIntegral_const]
      exact setLIntegral_mono measurable_const fun κ _ ↦
        measure_mono (cornerOuterTimes_subset I a b c δ κ)

/-- A common scalar reservoir whose outer times each support an inner dual-pair reservoir. -/
theorem cornerReservoir_spec {I : Set ℝ} (hI : MeasurableSet I) (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) {a b c δ : ℝ} (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I)
    (hδ : 0 < δ) (hab : δ ≤ dist a b) :
    MeasurableSet (cornerReservoir I a b c δ) ∧
      ENNReal.ofReal (δ * (volume I).toReal ^ 3 / 160000) ≤
        volume (cornerReservoir I a b c δ) ∧
      ∀ κ ∈ cornerReservoir I a b c δ, κ ≠ 0 ∧
        δ * ((volume I).toReal / 100) ^ 2 ≤ |κ| ∧ |κ| ≤ (100 / (volume I).toReal) ^ 3 ∧
        MeasurableSet (cornerOuterTimes I a b c δ κ) ∧ cornerOuterTimes I a b c δ κ ⊆ I ∧
        ENNReal.ofReal (δ * (volume I).toReal ^ 7 / 320000000000) ≤
          volume (cornerOuterTimes I a b c δ κ) ∧
        ∀ u ∈ cornerOuterTimes I a b c δ κ,
          ENNReal.ofReal (δ * (volume I).toReal ^ 5 / 8000000) ≤
            volume (dualTimes I b a (cornerInnerCoefficient a c κ u)) := by
  refine ⟨measurableSet_cornerReservoir hI a b c δ,
    volume_cornerReservoir_lower hI hIunit hIpos (hIunit ha) (hIunit hb) (hIunit hc) hδ hab, ?_⟩
  intro κ hκ
  obtain ⟨hκ₀, hκ₁, hκ₂⟩ := cornerReservoir_scalar_bounds hIunit hIpos
    (hIunit ha) (hIunit hb) (hIunit hc) hδ hab hκ
  exact ⟨hκ₀, hκ₁, hκ₂, measurableSet_cornerOuterTimes hI a b c δ κ,
    cornerOuterTimes_subset I a b c δ κ, hκ, fun u hu ↦ (cornerOuterTimes_spec hu).2.2.2⟩

end NKBesicovitch.Projection.Selection
