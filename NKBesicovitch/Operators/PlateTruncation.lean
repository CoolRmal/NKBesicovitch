/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.PlateAlgebra
public import NKBesicovitch.Operators.PlateMeasurability
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Monotone truncation of plate moments

Truncating a nonnegative extended-real input at natural heights recovers every
positive moment of its plate maximum. Uniform bounds on bounded inputs therefore
pass to arbitrary inputs, including functions taking the value infinity.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace NKBesicovitch

/-- Every positive plate moment is the supremum of the moments of bounded truncations. -/
theorem lintegral_plateMaximal_rpow_eq_iSup_truncation {n k : ℕ}
    (ν : Measure (Grassmannian n k)) (δ : ℝ) {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hf : Measurable f) {p : ℝ} (hp : 0 < p) :
    (∫⁻ V, plateMaximal δ f V ^ p ∂ν) =
      ⨆ j : ℕ, ∫⁻ V, plateMaximal δ (fun x ↦ min (f x) j) V ^ p ∂ν := by
  let F (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) := min (f x) (j : ℝ≥0∞)
  have hF (j) : Measurable (F j) := hf.min measurable_const
  have hm : Monotone F := fun i j hij x ↦ min_le_min_left (f x) (by exact_mod_cast hij)
  have hs : (fun x ↦ ⨆ j, F j x) = f := by
    funext x
    change (⨆ j : ℕ, f x ⊓ (j : ℝ≥0∞)) = f x
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have he (V : Grassmannian n k) : plateMaximal δ f V = ⨆ j, plateMaximal δ (F j) V := by
    rw [← plateMaximal_iSup hF hm, hs]
  have hpow (V : Grassmannian n k) :
      (⨆ j, plateMaximal δ (F j) V) ^ p = ⨆ j, plateMaximal δ (F j) V ^ p :=
    (ENNReal.orderIsoRpow p hp).map_iSup _
  simp_rw [he, hpow]
  exact lintegral_iSup (fun j ↦ (measurable_plateMaximal δ (hF j)).pow_const p)
    (fun i j hij V ↦ ENNReal.rpow_le_rpow (plateMaximal_mono (hm hij) V) hp.le)

end NKBesicovitch
