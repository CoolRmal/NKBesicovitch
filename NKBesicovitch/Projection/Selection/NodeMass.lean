/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.NodeGeometry
public import NKBesicovitch.Projection.Selection.SchemeBounds

/-!
# Polynomial parameter measure at one corner node

The outer scheme contributes its selection-volume bound at the outer-time
threshold. Each labeled inner copy contributes the corresponding bound
at the inner-time threshold. Finite product measure and two applications
of Tonelli multiply these contributions with the common scalar reservoir.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection.SelectableProjectionScheme

variable {m D L : ℕ} {β : ℝ} (S : SelectableProjectionScheme m β D L)

theorem volume_node_outer_parameters_lower {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b c δ κ : ℝ} (hδ : 0 < δ)
    (hκ : κ ∈ cornerReservoir I a b c δ) :
    ENNReal.ofReal (S.lowerConstant *
      (δ * (volume I).toReal ^ 7 / 320000000000) ^ S.volumeExponent) ≤
        volume (S.select (cornerOuterTimes I a b c δ κ)) := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  exact S.volume_lower_of_measure_lower (measurableSet_cornerOuterTimes hI _ _ _ _ _)
    ((cornerOuterTimes_subset I _ _ _ _ _).trans hIunit) (by positivity) hκ

theorem volume_node_inner_parameters_lower {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b c δ κ : ℝ} (hδ : 0 < δ)
    (hκ : κ ∈ cornerReservoir I a b c δ) {σ : Fin D → ℝ}
    (hσ : σ ∈ S.select (cornerOuterTimes I a b c δ κ)) (i : Fin L) :
    ENNReal.ofReal (S.lowerConstant * (δ * (volume I).toReal ^ 5 / 8000000) ^ S.volumeExponent) ≤
      volume (S.select (dualTimes I b a (cornerInnerCoefficient a c κ (S.time σ i)))) := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  have hO : 0 < volume (cornerOuterTimes I a b c δ κ) :=
    (ENNReal.ofReal_pos.mpr (by positivity)).trans_le hκ
  have hu := S.time_mem _ (measurableSet_cornerOuterTimes hI _ _ _ _ _)
    ((cornerOuterTimes_subset I _ _ _ _ _).trans hIunit) hO σ hσ i
  exact S.volume_lower_of_measure_lower (measurableSet_dualTimes hI _ _ _)
    ((dualTimes_subset I _ _ _).trans hIunit) (by positivity) (cornerOuterTimes_spec hu).2.2.2

theorem volume_node_inner_product_lower {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b c δ κ : ℝ} (hδ : 0 < δ)
    (hκ : κ ∈ cornerReservoir I a b c δ) {σ : Fin D → ℝ}
    (hσ : σ ∈ S.select (cornerOuterTimes I a b c δ κ)) :
    ENNReal.ofReal (S.lowerConstant *
      (δ * (volume I).toReal ^ 5 / 8000000) ^ S.volumeExponent) ^ L ≤
        volume (Prod.mk σ ⁻¹' (Prod.mk κ ⁻¹' S.cornerNodeParameters I a b c δ)) := by
  have he : Prod.mk σ ⁻¹' (Prod.mk κ ⁻¹' S.cornerNodeParameters I a b c δ) =
      Set.pi univ
        (fun i ↦ S.select (dualTimes I b a (cornerInnerCoefficient a c κ (S.time σ i)))) := by
    ext ρ
    simp only [cornerNodeParameters, mem_preimage, mem_ofPred_eq, hκ, hσ, true_and,
      mem_pi, mem_univ, forall_true_left]
  rw [he, volume_pi_pi]
  calc
    _ = ∏ i : Fin L, ENNReal.ofReal (S.lowerConstant *
        (δ * (volume I).toReal ^ 5 / 8000000) ^ S.volumeExponent) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ ↦ zero_le)
      (fun i _ ↦ S.volume_node_inner_parameters_lower hI hIunit hIpos hδ hκ hσ i)

theorem volume_node_scalar_fiber_lower {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b c δ κ : ℝ} (hδ : 0 < δ)
    (hκ : κ ∈ cornerReservoir I a b c δ) :
    ENNReal.ofReal (S.lowerConstant *
      (δ * (volume I).toReal ^ 5 / 8000000) ^ S.volumeExponent) ^ L *
      ENNReal.ofReal (S.lowerConstant *
        (δ * (volume I).toReal ^ 7 / 320000000000) ^ S.volumeExponent) ≤
        volume (Prod.mk κ ⁻¹' S.cornerNodeParameters I a b c δ) := by
  have hsection := (S.measurableSet_cornerNodeParameters hI a b c δ).preimage
    (f := Prod.mk κ) (by fun_prop)
  rw [Measure.volume_eq_prod, Measure.prod_apply hsection]
  calc
    _ ≤ ENNReal.ofReal (S.lowerConstant *
        (δ * (volume I).toReal ^ 5 / 8000000) ^ S.volumeExponent) ^ L *
        volume (S.select (cornerOuterTimes I a b c δ κ)) :=
      mul_le_mul le_rfl (S.volume_node_outer_parameters_lower hI hIunit hIpos hδ hκ)
        zero_le zero_le
    _ = ∫⁻ σ in S.select (cornerOuterTimes I a b c δ κ), ENNReal.ofReal (S.lowerConstant *
        (δ * (volume I).toReal ^ 5 / 8000000) ^ S.volumeExponent) ^ L :=
      (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ σ in S.select (cornerOuterTimes I a b c δ κ),
        volume (Prod.mk σ ⁻¹' (Prod.mk κ ⁻¹' S.cornerNodeParameters I a b c δ)) :=
      setLIntegral_mono' (S.measurableSet_select (measurableSet_cornerOuterTimes hI _ _ _ _ _))
        (fun σ hσ ↦ S.volume_node_inner_product_lower hI hIunit hIpos hδ hκ hσ)
    _ ≤ _ := setLIntegral_le_lintegral _ _

theorem volume_cornerNodeParameters_lower {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b c δ : ℝ}
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hc : c ∈ Icc 0 1)
    (hδ : 0 < δ) (hab : δ ≤ dist a b) :
    ENNReal.ofReal (S.lowerConstant *
      (δ * (volume I).toReal ^ 5 / 8000000) ^ S.volumeExponent) ^ L *
      ENNReal.ofReal (S.lowerConstant *
        (δ * (volume I).toReal ^ 7 / 320000000000) ^ S.volumeExponent) *
      ENNReal.ofReal (δ * (volume I).toReal ^ 3 / 160000) ≤
        volume (S.cornerNodeParameters I a b c δ) := by
  rw [Measure.volume_eq_prod,
    Measure.prod_apply (S.measurableSet_cornerNodeParameters hI a b c δ)]
  calc
    _ ≤ ENNReal.ofReal (S.lowerConstant *
        (δ * (volume I).toReal ^ 5 / 8000000) ^ S.volumeExponent) ^ L *
        ENNReal.ofReal (S.lowerConstant *
          (δ * (volume I).toReal ^ 7 / 320000000000) ^ S.volumeExponent) *
        volume (cornerReservoir I a b c δ) :=
      mul_le_mul le_rfl (volume_cornerReservoir_lower hI hIunit hIpos ha hb hc hδ hab)
        zero_le zero_le
    _ = ∫⁻ κ in cornerReservoir I a b c δ, ENNReal.ofReal (S.lowerConstant *
        (δ * (volume I).toReal ^ 5 / 8000000) ^ S.volumeExponent) ^ L *
        ENNReal.ofReal (S.lowerConstant *
          (δ * (volume I).toReal ^ 7 / 320000000000) ^ S.volumeExponent) :=
      (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ κ in cornerReservoir I a b c δ,
        volume (Prod.mk κ ⁻¹' S.cornerNodeParameters I a b c δ) :=
      setLIntegral_mono' (measurableSet_cornerReservoir hI a b c δ)
        (fun κ hκ ↦ S.volume_node_scalar_fiber_lower hI hIunit hIpos hδ hκ)
    _ ≤ _ := setLIntegral_le_lintegral _ _

end NKBesicovitch.Projection.Selection.SelectableProjectionScheme
