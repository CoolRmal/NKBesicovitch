/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.Fourier.PlaneKernel
public import NKBesicovitch.Grassmannian.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Mass of weighted plane kernels

The normalizing dilation cancels in the total kernel mass. The remaining
factors are the ambient polynomial profile integral and the translated plane
weight integral. Moving a plane away from the origin only decreases the latter.
-/

public section

open MeasureTheory Submodule
open scoped ENNReal NNReal RealInnerProductSpace

namespace NKBesicovitch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private lemma lintegral_polynomial_smul_aux (a : ℝ) (ha : 0 < a) (N : ℕ) :
    (∫⁻ z : E, ENNReal.ofReal (((1 + ‖a • z‖ ^ 2) ^ N)⁻¹)) =
      (ENNReal.ofReal (a ^ Module.finrank ℝ E))⁻¹ *
        ∫⁻ z : E, ENNReal.ofReal (((1 + ‖z‖ ^ 2) ^ N)⁻¹) := by
  rw [← lintegral_map (f := fun z : E ↦ ENNReal.ofReal (((1 + ‖z‖ ^ 2) ^ N)⁻¹))
    (g := fun z : E ↦ a • z) (by fun_prop) (by fun_prop),
    Measure.map_addHaar_smul volume ha.ne', lintegral_smul_measure]
  rw [abs_of_pos (by positivity), ENNReal.ofReal_inv_of_pos (pow_pos ha _), smul_eq_mul]

/-- The mass of a weighted plane kernel is independent of the positive dilation scale. -/
theorem lintegral_weightedPlaneKernel (V : Submodule ℝ E) (a : ℝ) (ha : 0 < a)
    (A N : ℕ) (x : E) :
    (∫⁻ z, weightedPlaneKernel V a A N x z) =
      (∫⁻ w : V, ENNReal.ofReal (((1 + ‖x + w‖ ^ 2) ^ A)⁻¹)) *
        ∫⁻ z : E, ENNReal.ofReal (((1 + ‖z‖ ^ 2) ^ N)⁻¹) := by
  simp only [weightedPlaneKernel, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_lintegral_swap (by fun_prop)]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_sub_left_eq_self (fun z : E ↦ ENNReal.ofReal (((1 + ‖a • z‖ ^ 2) ^ N)⁻¹)),
    lintegral_polynomial_smul_aux a ha]
  rw [lintegral_mul_const _ (by fun_prop)]
  have h₀ : ENNReal.ofReal (a ^ Module.finrank ℝ E) ≠ 0 := by positivity
  calc
    _ = (ENNReal.ofReal (a ^ Module.finrank ℝ E) *
        (ENNReal.ofReal (a ^ Module.finrank ℝ E))⁻¹) *
      ((∫⁻ w : V, ENNReal.ofReal (((1 + ‖x + w‖ ^ 2) ^ A)⁻¹)) *
        ∫⁻ z : E, ENNReal.ofReal (((1 + ‖z‖ ^ 2) ^ N)⁻¹)) := by ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel h₀ ENNReal.ofReal_ne_top, one_mul]

/-- A translated plane has no more polynomial weight mass than the plane through the origin. -/
theorem lintegral_inv_weight_affine_le (V : Submodule ℝ E) (A : ℕ) (x : E) :
    (∫⁻ w : V, ENNReal.ofReal (((1 + ‖x + w‖ ^ 2) ^ A)⁻¹)) ≤
      ∫⁻ w : V, ENNReal.ofReal (((1 + ‖w‖ ^ 2) ^ A)⁻¹) := by
  rw [← lintegral_sub_right_eq_self (fun w : V ↦
    ENNReal.ofReal (((1 + ‖x + w‖ ^ 2) ^ A)⁻¹)) (V.orthogonalProjectionOnto x)]
  apply lintegral_mono
  intro w
  have hi := (V.mem_orthogonal (x - V.starProjection x)).mp
    (V.sub_starProjection_mem_orthogonal x) w w.2
  have he : x + (w - V.orthogonalProjectionOnto x : V) =
      (x - V.starProjection x) + w := by simp only [Submodule.coe_sub]; abel
  dsimp only
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  have hn : ‖w‖ ^ 2 ≤ ‖(x - V.starProjection x) + (w : E)‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_comm, hi]
    simp only [Submodule.norm_coe]
    nlinarith [sq_nonneg ‖x - V.starProjection x‖]
  gcongr

private lemma lintegral_inv_weight_euclidean_ne_top_aux (d N : ℕ) (hN : d < 2 * N) :
    (∫⁻ z : EuclideanSpace ℝ (Fin d), ENNReal.ofReal (((1 + ‖z‖ ^ 2) ^ N)⁻¹)) ≠ ∞ := by
  apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (ae_of_all _ fun _ ↦ by positivity)).mpr
  have hd : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < 2 * (N : ℝ) := by
    simpa using (Nat.cast_lt (α := ℝ)).mpr hN
  convert! integrable_rpow_neg_one_add_norm_sq (μ := volume) hd using 1
  ext z
  rw [show -(2 * (N : ℝ)) / 2 = -(N : ℝ) by ring,
    Real.rpow_neg (by positivity), Real.rpow_natCast]

/-- Sufficient polynomial decay gives a finite kernel mass uniform in direction and translation. -/
theorem exists_lintegral_weightedPlaneKernel_le {n k A N : ℕ} (hA : k < 2 * A) (hN : n < 2 * N) :
    ∃ C : ℝ≥0, ∀ (V : Grassmannian n k) (a : ℝ), 0 < a →
      ∀ x, (∫⁻ z, weightedPlaneKernel V.val a A N x z) ≤ C := by
  let B := (∫⁻ w : EuclideanSpace ℝ (Fin k), ENNReal.ofReal (((1 + ‖w‖ ^ 2) ^ A)⁻¹)) *
    ∫⁻ z : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (((1 + ‖z‖ ^ 2) ^ N)⁻¹)
  have hB : B ≠ ∞ := ENNReal.mul_ne_top (lintegral_inv_weight_euclidean_ne_top_aux k A hA)
    (lintegral_inv_weight_euclidean_ne_top_aux n N hN)
  refine ⟨B.toNNReal, fun V a ha x ↦ ?_⟩
  rw [ENNReal.coe_toNNReal hB, lintegral_weightedPlaneKernel V.val a ha]
  let e : V.val ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k) :=
    ((stdOrthonormalBasis ℝ V.val).reindex (finCongr V.property)).repr
  have he : (∫⁻ w : V.val, ENNReal.ofReal (((1 + ‖w‖ ^ 2) ^ A)⁻¹)) =
      ∫⁻ w : EuclideanSpace ℝ (Fin k), ENNReal.ofReal (((1 + ‖w‖ ^ 2) ^ A)⁻¹) := by
    simpa only [e.norm_map] using e.measurePreserving.lintegral_comp
      (by fun_prop : Measurable (fun w : EuclideanSpace ℝ (Fin k) ↦
        ENNReal.ofReal (((1 + ‖w‖ ^ 2) ^ A)⁻¹)))
  exact (mul_le_mul_left (lintegral_inv_weight_affine_le V.val A x) _).trans_eq
    (congrArg (· * ∫⁻ z : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (((1 + ‖z‖ ^ 2) ^ N)⁻¹)) he)

end NKBesicovitch
