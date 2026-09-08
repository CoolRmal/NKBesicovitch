/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.PairCode
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Changing the second time into the dual-code scalar

Solve the dual-height identity for its scalar. The resulting rational map
is injective away from the first base height, with an explicit derivative.
The one-dimensional change-of-variables theorem computes its image measure
on every Borel subset of this domain.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection

theorem measurable_dualTime {X : Type*} [MeasurableSpace X] {a b c t : X → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) (ht : Measurable t) :
    Measurable (fun x ↦ dualTime (a x) (b x) (c x) (t x)) :=
  ha.add (((hb.sub ha).mul (ht.sub ha)).div (hc.mul (ht.sub hb)))

/-- The scalar making `t` and `u` dual heights for the base pair `(a,b)`. -/
noncomputable def dualScalar (a b t u : ℝ) : ℝ := ((b - a) * (t - a) / (t - b)) / (u - a)

theorem measurable_dualScalar {X : Type*} [MeasurableSpace X] {a b t u : X → ℝ}
    (ha : Measurable a) (hb : Measurable b) (ht : Measurable t) (hu : Measurable u) :
    Measurable (fun x ↦ dualScalar (a x) (b x) (t x) (u x)) :=
  (((hb.sub ha).mul (ht.sub ha)).div (ht.sub hb)).div (hu.sub ha)

theorem dualScalar_ne_zero {a b t u : ℝ} (hab : a ≠ b) (hta : t ≠ a) (htb : t ≠ b)
    (hua : u ≠ a) : dualScalar a b t u ≠ 0 :=
  div_ne_zero (div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hab.symm) (sub_ne_zero.mpr hta))
    (sub_ne_zero.mpr htb)) (sub_ne_zero.mpr hua)

theorem dualTime_dualScalar {a b t u : ℝ} (hab : a ≠ b) (hta : t ≠ a) (htb : t ≠ b) :
    dualTime a b (dualScalar a b t u) t = u := by
  unfold dualTime dualScalar
  field_simp
  ring

theorem dualScalar_dualTime {a b c t : ℝ} (hab : a ≠ b) (hc : c ≠ 0) (hta : t ≠ a)
    (htb : t ≠ b) : dualScalar a b t (dualTime a b c t) = c := by
  unfold dualScalar
  rw [dualTime_sub_base]
  field_simp

theorem injOn_dualScalar {a b t : ℝ} (hab : a ≠ b) (hta : t ≠ a) (htb : t ≠ b) :
    InjOn (dualScalar a b t) {u | u ≠ a} := by
  intro u _ v _ h
  calc
    u = dualTime a b (dualScalar a b t u) t := (dualTime_dualScalar hab hta htb).symm
    _ = dualTime a b (dualScalar a b t v) t := congrArg (fun c ↦ dualTime a b c t) h
    _ = v := dualTime_dualScalar hab hta htb

theorem image_dualScalar {a b t : ℝ} (hab : a ≠ b) (hta : t ≠ a) (htb : t ≠ b)
    {S : Set ℝ} (hS : ∀ u ∈ S, u ≠ a) :
    dualScalar a b t '' S = {c | c ≠ 0 ∧ dualTime a b c t ∈ S} := by
  ext c
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨dualScalar_ne_zero hab hta htb (hS u hu),
      (dualTime_dualScalar hab hta htb).symm ▸ hu⟩
  · rintro ⟨hc, ht'⟩
    exact ⟨dualTime a b c t, ht', dualScalar_dualTime hab hc hta htb⟩

theorem hasDerivAt_dualScalar (a b t : ℝ) {u : ℝ} (hua : u ≠ a) :
    HasDerivAt (dualScalar a b t) (-((b - a) * (t - a) / (t - b)) / (u - a) ^ 2) u := by
  unfold dualScalar
  simpa only [id_eq, zero_mul, mul_one, zero_sub] using
    (hasDerivAt_const u ((b - a) * (t - a) / (t - b))).fun_div
      ((hasDerivAt_id u).sub_const a) (sub_ne_zero.mpr hua)

theorem volume_image_dualScalar {a b t : ℝ} (hab : a ≠ b) (hta : t ≠ a) (htb : t ≠ b)
    {S : Set ℝ} (hS : MeasurableSet S) (hSa : ∀ u ∈ S, u ≠ a) :
    volume (dualScalar a b t '' S) =
      ∫⁻ u in S, ENNReal.ofReal (|-((b - a) * (t - a) / (t - b)) / (u - a) ^ 2|) := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul hS
    (fun u hu ↦ (hasDerivAt_dualScalar a b t (hSa u hu)).hasDerivWithinAt)
    ((injOn_dualScalar hab hta htb).mono hSa) (fun _ ↦ (1 : ℝ≥0∞))
  simpa only [setLIntegral_one, mul_one] using h

end NKBesicovitch.Projection.Selection
