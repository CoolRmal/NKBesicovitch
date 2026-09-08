/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerCoordinates

/-!
# Corner coordinates at a junction

A corner is equivalently its parent pair and its last-line slope. This
change preserves the intrinsic measure, with no separation assumption on
the two junction heights.
-/

@[expose] public section

open MeasureTheory

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- Parent pair together with the last-line slope. -/
def cornerParentCoordinates (a : ℝ) (p : CornerCoordinates m) :
    PairCoordinates m × EuclideanSpace ℝ (Fin m) := (cornerParent a p, p.2.2)

/-- Reconstruct a corner from its parent pair and last-line slope. -/
def cornerFromParent (a : ℝ) (p : PairCoordinates m) (ξ : EuclideanSpace ℝ (Fin m)) :
    CornerCoordinates m := (lineAt a p.1 p.2.1, (p.2.2, ξ))

theorem cornerFromParent_cornerParentCoordinates (a : ℝ) (p : CornerCoordinates m) :
    cornerFromParent a (cornerParentCoordinates a p).1 (cornerParentCoordinates a p).2 = p := by
  simp [cornerFromParent, cornerParentCoordinates, cornerParent, lineAt_atHeight]

theorem cornerParent_cornerFromParent (a : ℝ) (p : PairCoordinates m)
    (ξ : EuclideanSpace ℝ (Fin m)) : cornerParent a (cornerFromParent a p ξ) = p := by
  simp [cornerParent, cornerFromParent, atHeight, lineAt]

theorem measurable_cornerFromParent (a : ℝ) :
    Measurable (fun p : PairCoordinates m × EuclideanSpace ℝ (Fin m) ↦
      cornerFromParent a p.1 p.2) := by
  unfold cornerFromParent lineAt
  fun_prop

theorem measurePreserving_cornerParentCoordinates (a : ℝ) :
    MeasurePreserving (cornerParentCoordinates (m := m) a) volume volume := by
  have hline : MeasurePreserving (lineCoordinates (m := m) a).symm volume volume :=
    (measurePreserving_lineCoordinates a).symm
      (lineCoordinates a).toHomeomorph.toMeasurableEquiv
  have h₁ : MeasurePreserving (MeasurableEquiv.prodAssoc : Line m × Line m ≃ᵐ
      EuclideanSpace ℝ (Fin m) × (EuclideanSpace ℝ (Fin m) × Line m)) volume volume :=
    volume_preserving_prodAssoc
  have h₂ : MeasurePreserving (MeasurableEquiv.prodAssoc :
      Line m × EuclideanSpace ℝ (Fin m) ≃ᵐ EuclideanSpace ℝ (Fin m) × Line m) volume volume :=
    volume_preserving_prodAssoc
  have h₃ : MeasurePreserving (MeasurableEquiv.prodAssoc :
      PairCoordinates m × EuclideanSpace ℝ (Fin m) ≃ᵐ
        EuclideanSpace ℝ (Fin m) × (Line m × EuclideanSpace ℝ (Fin m))) volume volume :=
    volume_preserving_prodAssoc
  have hp := ((MeasurePreserving.id (volume : Measure (EuclideanSpace ℝ (Fin m)))).prod
    (h₂.symm MeasurableEquiv.prodAssoc))
  change MeasurePreserving (fun p : CornerCoordinates m ↦
    ((atHeight a p.1, (p.1.2, p.2.1)), p.2.2)) _ _
  simpa [Function.comp_def, Prod.map_def, MeasurableEquiv.prodAssoc,
    lineCoordinates_symm_apply, cornerParentCoordinates, cornerParent,
    Measure.volume_eq_prod] using (h₃.symm MeasurableEquiv.prodAssoc).comp
      (hp.comp (h₁.comp (hline.prod (MeasurePreserving.id (volume : Measure (Line m))))))

end NKBesicovitch.Projection
