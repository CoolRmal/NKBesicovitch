/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.Defs
public import NKBesicovitch.Operators.MixedNorm.MapProd

/-!
# Plate estimates for measurable families

A diagonal estimate integrates over an additional parameter without changing
its constant. Tonelli identifies the iterated input norm with its product norm.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace NKBesicovitch

/-- A uniform diagonal plate bound also bounds the joint norm of a measurable family. -/
theorem eLpNorm_plateMaximal_family_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {n k : ℕ} (ν : Measure (Grassmannian n k)) {δ : ℝ} {p : ℝ≥0∞}
    (hp : p ≠ 0) (hpfin : p ≠ ∞) (C : ℝ≥0)
    (hbound : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞, Measurable g →
      eLpNorm (plateMaximal δ g) p ν ≤ C * eLpNorm g p volume)
    {f : X × EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : Measurable f) :
    eLpNorm (fun z : X × Grassmannian n k ↦ plateMaximal δ (fun y ↦ f (z.1, y)) z.2)
      p (μ.prod ν) ≤ C * eLpNorm f p (μ.prod volume) := by
  apply (eLpNorm_prod_le_iterated _ hp hpfin).trans
  rw [← eLpNorm_iterated_eq_prod hf hp hpfin]
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul'
  exact ae_of_all _ fun x ↦ by
    simpa only [enorm_eq_self] using hbound (fun y ↦ f (x, y))
      (hf.comp measurable_prodMk_left)

end NKBesicovitch
