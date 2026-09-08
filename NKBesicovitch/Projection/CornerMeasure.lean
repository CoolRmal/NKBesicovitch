/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerInverse
public import NKBesicovitch.Projection.CodeCoordinates

/-!
# Changes of intrinsic corner coordinates

Replacing the middle line by the first line preserves volume. The remaining
change to last intercept and corner code has the exact two-factor Jacobian.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

theorem measurePreserving_swap_middle :
    MeasurePreserving (fun p : CornerCoordinates m ↦ ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      volume volume := by
  have h₃ : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (Space m × Space m) × Space m ≃ᵐ Space m × (Space m × Space m))
      volume volume := volume_preserving_prodAssoc
  have hswap := Measure.measurePreserving_swap (μ := (volume : Measure (Space m)))
    (ν := (volume : Measure (Space m)))
  have hp := h₃.comp ((hswap.prod (MeasurePreserving.id (volume : Measure (Space m)))).comp
    (h₃.symm MeasurableEquiv.prodAssoc))
  have h₄ : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (Space m × Space m) × (Space m × Space m) ≃ᵐ
        Space m × (Space m × (Space m × Space m))) volume volume := volume_preserving_prodAssoc
  simpa [Function.comp_def, Prod.map_def, MeasurableEquiv.prodAssoc, Measure.volume_eq_prod] using
    (h₄.symm MeasurableEquiv.prodAssoc).comp
      (((MeasurePreserving.id (volume : Measure (Space m))).prod hp).comp h₄)

/-- First line and the remaining two slopes of a corner. -/
def cornerToFirst (a : ℝ) (p : CornerCoordinates m) : CornerCoordinates m :=
  (cornerFirst a p, (p.1.2, p.2.2))

theorem measurePreserving_cornerToFirst (a : ℝ) :
    MeasurePreserving (cornerToFirst (m := m) a) volume volume := by
  have hline := measurePreserving_lineCoordinates (m := m) a
  have hinv : MeasurePreserving (lineCoordinates (m := m) a).symm volume volume :=
    hline.symm (lineCoordinates a).toHomeomorph.toMeasurableEquiv
  have hi := (MeasurePreserving.id (volume : Measure (Line m)))
  change MeasurePreserving (fun p : CornerCoordinates m ↦
    (lineAt a (atHeight a p.1) p.2.1, (p.1.2, p.2.2))) _ _
  simpa [Function.comp_def, Prod.map_def, lineCoordinates_apply, lineCoordinates_symm_apply,
    Measure.volume_eq_prod] using (hline.prod hi).comp
      (measurePreserving_swap_middle.comp (hinv.prod hi))

theorem codeJacobian_comm (a b : ℝ) : codeJacobian m a b = codeJacobian m b a := by
  simp [codeJacobian, abs_sub_comm]

theorem measurePreserving_cornerFiber {a b : ℝ} (hab : a ≠ b) (v w : Space m) :
    MeasurePreserving (fun p : Line m ↦
      (v + (b - a) • p.1 - b • p.2, w + (a - b) • p.2)) volume
      (codeJacobian m a b ^ 2 • volume) := by
  have hscale : MeasurePreserving (fun ξ : Space m ↦ (b - a) • ξ) volume
      (codeJacobian m a b • volume) := by
    refine ⟨by fun_prop, ?_⟩
    simpa [codeJacobian] using
      Measure.map_addHaar_smul (volume : Measure (Space m)) (sub_ne_zero.mpr hab.symm)
  have hscale' : MeasurePreserving (fun ξ : Space m ↦ (a - b) • ξ) volume
      (codeJacobian m a b • volume) := by
    refine ⟨by fun_prop, ?_⟩
    simpa [codeJacobian, abs_sub_comm] using
      Measure.map_addHaar_smul (volume : Measure (Space m)) (sub_ne_zero.mpr hab)
  have hfirst := (MeasurePreserving.id (volume : Measure (Space m))).skew_product
    (g := fun ξ (x : Space m) ↦ (v - b • ξ) + (b - a) • x)
    (by fun_prop) (ae_of_all _ fun ξ ↦ (hscale.add_left _ (v - b • ξ)).map_eq)
  have hs : MeasurePreserving (fun p : Line m ↦ (v + (b - a) • p.1 - b • p.2, p.2))
      volume (codeJacobian m a b • volume) := by
    simpa [Function.comp_def, Measure.prod_smul_left, Measure.prod_smul_right,
      Measure.volume_eq_prod, sub_add_eq_add_sub] using
      Measure.measurePreserving_swap.comp (hfirst.comp Measure.measurePreserving_swap)
  have hlast : MeasurePreserving (fun p : Line m ↦ (p.1, w + (a - b) • p.2))
      volume (codeJacobian m a b • volume) := by
    simpa [Prod.map_def, Measure.prod_smul_right, Measure.volume_eq_prod] using
      (MeasurePreserving.id (volume : Measure (Space m))).prod (hscale'.add_left _ w)
  simpa [Function.comp_def, smul_smul, pow_two] using (hlast.smul_measure _).comp hs

/-- First line, last-line intercept, and corner code. -/
def cornerCodeCoordinates (a b c κ : ℝ) (p : CornerCoordinates m) : CornerCoordinates m :=
  (cornerFirst a p, ((cornerLast b p).1, cornerCode a b c κ p))

theorem cornerLast_fst_eq (a b : ℝ) (p : CornerCoordinates m) :
    (cornerLast b p).1 =
      atHeight a (cornerFirst a p) + (b - a) • p.1.2 - b • p.2.2 := by
  rw [atHeight_cornerFirst]
  unfold cornerLast lineAt atHeight
  module

theorem continuous_cornerCodeCoordinates (a b c κ : ℝ) :
    Continuous (cornerCodeCoordinates (m := m) a b c κ) := by
  unfold cornerCodeCoordinates cornerCode cornerFirst cornerLast lineAt atHeight
  fun_prop

theorem measurePreserving_cornerCodeCoordinates {a b : ℝ} (hab : a ≠ b) (c κ : ℝ) :
    MeasurePreserving (cornerCodeCoordinates (m := m) a b c κ) volume
      (codeJacobian m a b ^ 2 • volume) := by
  have hs : MeasurePreserving (fun p : CornerCoordinates m ↦
      (p.1, (atHeight a p.1 + (b - a) • p.2.1 - b • p.2.2,
        κ • atHeight c p.1 + (a - b) • p.2.2))) volume
      (codeJacobian m a b ^ 2 • volume) := by
    have h := (MeasurePreserving.id (volume : Measure (Line m))).skew_product
      (g := fun g (s : Line m) ↦ (atHeight a g + (b - a) • s.1 - b • s.2,
        κ • atHeight c g + (a - b) • s.2))
      (by unfold atHeight; fun_prop)
      (ae_of_all _ fun g ↦ (measurePreserving_cornerFiber hab (atHeight a g)
        (κ • atHeight c g)).map_eq)
    simpa [Measure.prod_smul_right, Measure.volume_eq_prod] using h
  change MeasurePreserving (fun p : CornerCoordinates m ↦
    (cornerFirst a p, ((cornerLast b p).1, κ • atHeight c (cornerFirst a p) + (a - b) • p.2.2))) _ _
  simpa [Function.comp_def, cornerToFirst, cornerLast_fst_eq a b] using
    hs.comp (measurePreserving_cornerToFirst a)

theorem measurePreserving_cornerCodeCoordinates_assoc {a b : ℝ} (hab : a ≠ b) (c κ : ℝ) :
    MeasurePreserving (fun p : CornerCoordinates m ↦
      ((cornerFirst a p, (cornerLast b p).1), cornerCode a b c κ p)) volume
      (codeJacobian m a b ^ 2 • volume) := by
  have ha : MeasurePreserving (MeasurableEquiv.prodAssoc :
      (Line m × Space m) × Space m ≃ᵐ Line m × (Space m × Space m)) volume volume :=
    volume_preserving_prodAssoc
  simpa [Function.comp_def, MeasurableEquiv.prodAssoc, cornerCodeCoordinates] using
    ((ha.symm MeasurableEquiv.prodAssoc).smul_measure (codeJacobian m a b ^ 2)).comp
      (measurePreserving_cornerCodeCoordinates hab c κ)

end NKBesicovitch.Projection
