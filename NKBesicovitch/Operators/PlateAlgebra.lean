/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Geometry.Plates
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Order and sum bounds for plate maxima

Normalized positive finite plate volumes preserve constants. Monotonicity,
positive homogeneity, and countable subadditivity let input level decompositions
pass through the maximal operator, including extended-real inputs.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace NKBesicovitch

variable {n k : ℕ} {δ : ℝ} {f g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}

theorem plateMaximal_mono (h : f ≤ g) (V : Grassmannian n k) :
    plateMaximal δ f V ≤ plateMaximal δ g V := by
  apply iSup_mono
  intro a
  exact ENNReal.div_le_div_right (lintegral_mono h) _

@[simp]
theorem plateMaximal_const (hδ : 0 < δ) (c : ℝ≥0∞) (V : Grassmannian n k) :
    plateMaximal δ (fun _ ↦ c) V = c := by
  unfold plateMaximal
  have he (a : EuclideanSpace ℝ (Fin n)) :
      (∫⁻ _ in plate δ V.val a, c) / volume (plate δ V.val a) = c := by
    rw [setLIntegral_const, ENNReal.mul_div_cancel_right
      (volume_plate_pos hδ V.val a).ne' (volume_plate_lt_top δ V.val a).ne]
  simp only [he, ciSup_const]

theorem plateMaximal_add_le (hf : Measurable f) (V : Grassmannian n k) :
    plateMaximal δ (fun x ↦ f x + g x) V ≤ plateMaximal δ f V + plateMaximal δ g V := by
  apply iSup_le
  intro a
  rw [lintegral_add_left hf, ENNReal.add_div]
  exact add_le_add
    (le_iSup (fun a ↦ (∫⁻ x in plate δ V.val a, f x) / volume (plate δ V.val a)) a)
    (le_iSup (fun a ↦ (∫⁻ x in plate δ V.val a, g x) / volume (plate δ V.val a)) a)

theorem plateMaximal_const_mul (c : ℝ≥0∞) (hf : Measurable f) (V : Grassmannian n k) :
    plateMaximal δ (fun x ↦ c * f x) V = c * plateMaximal δ f V := by
  unfold plateMaximal
  simp_rw [lintegral_const_mul c hf, div_eq_mul_inv, mul_assoc]
  exact (ENNReal.mul_iSup _ _).symm

theorem plateMaximal_tsum_le {F : ℕ → EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hF : ∀ j, Measurable (F j)) (V : Grassmannian n k) :
    plateMaximal δ (fun x ↦ ∑' j, F j x) V ≤ ∑' j, plateMaximal δ (F j) V := by
  apply iSup_le
  intro a
  rw [lintegral_tsum (fun j ↦ (hF j).aemeasurable), div_eq_mul_inv, ← ENNReal.tsum_mul_right]
  exact ENNReal.tsum_le_tsum fun j ↦ le_iSup
    (fun a ↦ (∫⁻ x in plate δ V.val a, F j x) / volume (plate δ V.val a)) a

end NKBesicovitch
