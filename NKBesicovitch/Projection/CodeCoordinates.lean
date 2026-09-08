/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.PairCode
public import NKBesicovitch.Projection.PairData

/-!
# First-line and pair-code coordinates

The code change preserves the first line and scales the second slope. This
gives the exact factor relating intrinsic pair volume to first-line fiber volume.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- Encode a pair by its first line and pair code. -/
def codeCoordinates (a b c : ℝ) (p : PairCoordinates m) : Line m × Space m :=
  (lineAt a p.1 p.2.1, pairCode a b c p)

/-- The inverse Jacobian of the second-slope-to-code change. -/
noncomputable def codeJacobian (m : ℕ) (a b : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal |((b - a) ^ m)⁻¹|

theorem continuous_codeCoordinates (a b c : ℝ) :
    Continuous (codeCoordinates (m := m) a b c) := by
  unfold codeCoordinates pairCode lineAt atHeight
  fun_prop

theorem continuous_pairFromCode (a b c : ℝ) :
    Continuous (fun p : Line m × Space m ↦ pairFromCode a b c p.1 p.2) := by
  unfold pairFromCode atHeight
  fun_prop

theorem measurePreserving_codeCoordinates {a b : ℝ} (hab : a ≠ b) (c : ℝ) :
    MeasurePreserving (codeCoordinates (m := m) a b c) volume
      (codeJacobian m a b • volume) := by
  change MeasurePreserving (fun p : PairCoordinates m ↦
    (lineAt a p.1 p.2.1, c • atHeight b (lineAt a p.1 p.2.1) + (b - a) • p.2.2)) _ _
  have hscale : MeasurePreserving (fun ξ : Space m ↦ (b - a) • ξ) volume
      (codeJacobian m a b • volume) := by
    refine ⟨by fun_prop, ?_⟩
    simpa [codeJacobian] using
      Measure.map_addHaar_smul (volume : Measure (Space m)) (sub_ne_zero.mpr hab.symm)
  have hcode := (MeasurePreserving.id (volume : Measure (Line m))).skew_product
    (g := fun g (ξ : Space m) ↦ c • atHeight b g + (b - a) • ξ)
    (by unfold atHeight; fun_prop)
    (ae_of_all _ fun g ↦ (hscale.add_left _ (c • atHeight b g)).map_eq)
  have hline := (measurePreserving_lineCoordinates (m := m) a).prod
    (MeasurePreserving.id (volume : Measure (Space m)))
  have hassoc := (measurePreserving_prodAssoc (volume : Measure (Space m))
    (volume : Measure (Space m)) (volume : Measure (Space m))).symm
      MeasurableEquiv.prodAssoc
  simpa [lineCoordinates_apply, Function.comp_def, Prod.map_def, MeasurableEquiv.prodAssoc,
    Measure.prod_smul_right, Measure.volume_eq_prod] using hcode.comp (hline.comp hassoc)

end NKBesicovitch.Projection
