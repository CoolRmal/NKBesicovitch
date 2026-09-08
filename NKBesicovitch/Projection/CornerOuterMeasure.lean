/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerOuter

/-!
# The outer corner density as a pushforward

The outer-data coordinates have the same Jacobian as the corner-code
coordinates. Their explicit inverse gives total and restricted mass identities.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- Outer data, first-line slope, and last-line intercept. -/
noncomputable def cornerOuterCoordinates (a b c κ u : ℝ)
    (p : CornerCoordinates m) : CornerCoordinates m :=
  (cornerOuterData a b c κ u p, ((cornerFirst a p).2, (cornerLast b p).1))

theorem measurePreserving_cornerOuterPermutation (u : ℝ) :
    MeasurePreserving (fun p : CornerCoordinates m ↦
      ((atHeight u p.1, p.2.2), (p.1.2, p.2.1))) volume volume := by
  have hinv : MeasurePreserving (lineCoordinates (m := m) u).symm volume volume :=
    (measurePreserving_lineCoordinates u).symm
      (lineCoordinates u).toHomeomorph.toMeasurableEquiv
  have hi := MeasurePreserving.id (volume : Measure (Line m))
  have hswap := Measure.measurePreserving_swap (μ := (volume : Measure (EuclideanSpace ℝ (Fin m))))
    (ν := (volume : Measure (EuclideanSpace ℝ (Fin m))))
  simpa [Function.comp_def, Prod.map_def, lineCoordinates_symm_apply,
    Measure.volume_eq_prod] using
    measurePreserving_swap_middle.comp ((hi.prod hswap).comp (hinv.prod hi))

theorem measurePreserving_sub_smul_second (A : ℝ) :
    MeasurePreserving (fun p : Line m ↦ (p.1, p.2 - A • p.1)) volume volume := by
  change MeasurePreserving _ (volume.prod volume) (volume.prod volume)
  refine (MeasurePreserving.id (volume : Measure (EuclideanSpace ℝ (Fin m)))).skew_product
    (g := fun y (z : EuclideanSpace ℝ (Fin m)) ↦ z - A • y)
    (by fun_prop) (ae_of_all _ fun y ↦ ?_)
  simpa [sub_eq_add_neg] using map_add_right_eq_self volume (-(A • y))

theorem measurePreserving_cornerOuterCoordinates {a b c κ u : ℝ}
    (hab : a ≠ b) (hua : u ≠ a) :
    MeasurePreserving (cornerOuterCoordinates (m := m) a b c κ u) volume
      (codeJacobian m a b ^ 2 • volume) := by
  have hs := (measurePreserving_sub_smul_second (m := m)
    (cornerOuterCoefficient a c κ u)).prod (MeasurePreserving.id (volume : Measure (Line m)))
  have ht : MeasurePreserving (fun p : CornerCoordinates m ↦
      ((atHeight u p.1, p.2.2 - cornerOuterCoefficient a c κ u • atHeight u p.1),
        (p.1.2, p.2.1))) volume volume := by
    simpa [Function.comp_def, Prod.map_def, Measure.volume_eq_prod] using
      hs.comp (measurePreserving_cornerOuterPermutation u)
  change MeasurePreserving (fun p : CornerCoordinates m ↦
    (cornerOuterData a b c κ u p, ((cornerFirst a p).2, (cornerLast b p).1))) _ _
  simpa [Function.comp_def, cornerCodeCoordinates, cornerOuterData_eq hua] using
    (ht.smul_measure (codeJacobian m a b ^ 2)).comp
      (measurePreserving_cornerCodeCoordinates hab c κ)

/-- Reconstruction from outer data and the two remaining coordinates. -/
noncomputable def cornerFromOuter (a b c κ u : ℝ) (yz s : Line m) : CornerCoordinates m :=
  cornerFromCode a b c κ (lineAt u yz.1 s.1) s.2
    (cornerOuterCoefficient a c κ u • yz.1 + yz.2)

theorem cornerFromOuter_cornerOuterCoordinates {a b c κ u : ℝ}
    (hab : a ≠ b) (hua : u ≠ a) (p : CornerCoordinates m) :
    cornerFromOuter a b c κ u (cornerOuterCoordinates a b c κ u p).1
      (cornerOuterCoordinates a b c κ u p).2 = p := by
  simp only [cornerFromOuter, cornerOuterCoordinates, cornerOuterData_eq hua]
  rw [lineAt_atHeight, add_sub_cancel, cornerFromCode_cornerCode hab]

theorem cornerOuterData_cornerFromOuter {a b c κ u : ℝ} (hab : a ≠ b)
    (hua : u ≠ a) (yz s : Line m) :
    cornerOuterData a b c κ u (cornerFromOuter a b c κ u yz s) = yz := by
  simp [cornerFromOuter, cornerOuterData_cornerFromCode hab hua, atHeight_lineAt]

theorem measurable_cornerFromOuter (a b c κ u : ℝ) :
    Measurable (fun p : CornerCoordinates m ↦ cornerFromOuter a b c κ u p.1 p.2) := by
  unfold cornerFromOuter cornerFromCode lineAt atHeight
  fun_prop

theorem lintegral_cornerOuterDensity {a b c κ u : ℝ} (hab : a ≠ b) (hua : u ≠ a)
    {D : Set (CornerCoordinates m)} (hD : MeasurableSet D) :
    (∫⁻ yz, cornerOuterDensity a b c κ u D yz) = volume D := by
  let f : CornerCoordinates m → ℝ≥0∞ := fun p ↦
    D.indicator 1 (cornerFromOuter a b c κ u p.1 p.2)
  have hf : Measurable f :=
    (measurable_const.indicator hD).comp (measurable_cornerFromOuter a b c κ u)
  have hi := (measurePreserving_cornerOuterCoordinates (m := m) (c := c) (κ := κ)
    hab hua).lintegral_comp hf
  calc
    _ = codeJacobian m a b ^ 2 * ∫⁻ yz, ∫⁻ s, f (yz, s) :=
      lintegral_const_mul _ hf.lintegral_prod_right'
    _ = codeJacobian m a b ^ 2 * ∫⁻ p, f p := by
      congr 1
      simpa only [Measure.volume_eq_prod] using
        (lintegral_prod _ hf.aemeasurable).symm
    _ = ∫⁻ p, f p ∂(codeJacobian m a b ^ 2 • volume) := by
      rw [lintegral_smul_measure, smul_eq_mul]
    _ = ∫⁻ p, D.indicator 1 p := by
      rw [← hi]
      apply lintegral_congr
      intro p
      dsimp only [f]
      rw [cornerFromOuter_cornerOuterCoordinates hab hua]
    _ = volume D := lintegral_indicator_one hD

theorem cornerOuterDensity_inter_preimage {a b c κ u : ℝ} (hab : a ≠ b) (hua : u ≠ a)
    (D : Set (CornerCoordinates m)) (B : Set (Line m)) (yz : Line m) :
    cornerOuterDensity a b c κ u (D ∩ cornerOuterData a b c κ u ⁻¹' B) yz =
      B.indicator (cornerOuterDensity a b c κ u D) yz := by
  by_cases hB : yz ∈ B
  · rw [Set.indicator_of_mem hB]
    change codeJacobian m a b ^ 2 *
      (∫⁻ s, (D ∩ cornerOuterData a b c κ u ⁻¹' B).indicator
        (1 : CornerCoordinates m → ℝ≥0∞) (cornerFromOuter a b c κ u yz s)) =
      codeJacobian m a b ^ 2 * ∫⁻ s,
        D.indicator (1 : CornerCoordinates m → ℝ≥0∞) (cornerFromOuter a b c κ u yz s)
    congr 1
    apply lintegral_congr
    intro s
    by_cases hs : cornerFromOuter a b c κ u yz s ∈ D
    · have hp : cornerFromOuter a b c κ u yz s ∈ D ∩ cornerOuterData a b c κ u ⁻¹' B :=
        ⟨hs, by simpa only [Set.mem_preimage, cornerOuterData_cornerFromOuter hab hua] using hB⟩
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem (fun h ↦ hs h.1), Set.indicator_of_notMem hs]
  · rw [Set.indicator_of_notMem hB]
    change codeJacobian m a b ^ 2 *
      (∫⁻ s, (D ∩ cornerOuterData a b c κ u ⁻¹' B).indicator
        (1 : CornerCoordinates m → ℝ≥0∞) (cornerFromOuter a b c κ u yz s)) = 0
    have hz (s : Line m) : (D ∩ cornerOuterData a b c κ u ⁻¹' B).indicator
        (1 : CornerCoordinates m → ℝ≥0∞) (cornerFromOuter a b c κ u yz s) = 0 := by
      simp [Set.indicator, cornerOuterData_cornerFromOuter hab hua, hB]
    simp [hz]

theorem setLIntegral_cornerOuterDensity {a b c κ u : ℝ} (hab : a ≠ b) (hua : u ≠ a)
    {D : Set (CornerCoordinates m)} (hD : MeasurableSet D)
    {B : Set (Line m)} (hB : MeasurableSet B) :
    (∫⁻ yz in B, cornerOuterDensity a b c κ u D yz) =
      volume (D ∩ cornerOuterData a b c κ u ⁻¹' B) := by
  rw [← lintegral_indicator hB]
  simp_rw [← cornerOuterDensity_inter_preimage hab hua]
  exact lintegral_cornerOuterDensity hab hua
    (hD.inter (hB.preimage (continuous_cornerOuterData a b c κ u).measurable))

end NKBesicovitch.Projection
