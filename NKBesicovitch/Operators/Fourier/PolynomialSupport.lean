/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Fourier support under polynomial transverse weights

Multiplication by a linear coordinate becomes differentiation on the Fourier
side and hence does not enlarge closed Fourier support. The same holds for
the polynomial weights `(1 + ‖x‖²)^A` used in the full-plane comparison.
-/

public section

open SchwartzMap Set FourierTransform
open scoped SchwartzMap FourierTransform LineDeriv RealInnerProductSpace

namespace NKBesicovitch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Multiplication by a real linear coordinate does not enlarge closed Fourier support. -/
theorem tsupport_fourier_smulLeftCLM_inner_subset (f : 𝓢(E, ℂ)) (v : E) :
    tsupport (𝓕 (smulLeftCLM ℂ (inner ℝ · v) f) : 𝓢(E, ℂ)) ⊆ tsupport (𝓕 f : 𝓢(E, ℂ)) := by
  have hc : -(2 * Real.pi * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
  have he : 𝓕 (smulLeftCLM ℂ (inner ℝ · v) f) =
      (-(2 * Real.pi * Complex.I))⁻¹ • ∂_{v} (𝓕 f) := by
    rw [SchwartzMap.lineDerivOp_fourier_eq, fourier_smul, inv_smul_smul₀ hc]
  rw [he]
  exact (tsupport_smul_subset_right (fun _ ↦ (-(2 * Real.pi * Complex.I))⁻¹)
    (∂_{v} (𝓕 f) : 𝓢(E, ℂ))).trans (SchwartzMap.tsupport_lineDerivOp_subset v (𝓕 f))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma smulLeftCLM_one_add_norm_sq_eq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (f : 𝓢(E, ℂ)) :
    smulLeftCLM ℂ (fun x : E ↦ 1 + ‖x‖ ^ 2) f =
      f + ∑ i, smulLeftCLM ℂ (inner ℝ · (b i)) (smulLeftCLM ℂ (inner ℝ · (b i)) f) := by
  ext x
  have h (i : ι) : (inner ℝ · (b i)).HasTemperateGrowth := by fun_prop
  simp only [smulLeftCLM_apply_apply (by fun_prop :
    (fun x : E ↦ 1 + ‖x‖ ^ 2).HasTemperateGrowth), add_apply, sum_apply,
    smulLeftCLM_apply_apply (h _), smul_smul, ← pow_two, ← Finset.sum_smul,
    b.sum_sq_inner_left, add_smul, one_smul]

private lemma tsupport_fourier_smulLeftCLM_one_add_norm_sq_subset (f : 𝓢(E, ℂ)) :
    tsupport (𝓕 (smulLeftCLM ℂ (fun x : E ↦ 1 + ‖x‖ ^ 2) f) : 𝓢(E, ℂ)) ⊆
      tsupport (𝓕 f : 𝓢(E, ℂ)) := by
  let b := stdOrthonormalBasis ℝ E
  have hs (i) := (tsupport_fourier_smulLeftCLM_inner_subset
    (smulLeftCLM ℂ (inner ℝ · (b i)) f) (b i)).trans
      (tsupport_fourier_smulLeftCLM_inner_subset f (b i))
  apply closure_minimal ?_ isClosed_closure
  intro ξ hξ
  by_contra hξ'
  have hf := image_eq_zero_of_notMem_tsupport hξ'
  have hi (i) := image_eq_zero_of_notMem_tsupport (fun h ↦ hξ' (hs i h))
  rw [smulLeftCLM_one_add_norm_sq_eq b, FourierTransform.fourier_add,
    FourierTransform.fourier_sum] at hξ
  simp only [Function.mem_support, add_apply, sum_apply, hf, hi, Finset.sum_const_zero,
    add_zero, ne_eq, not_true_eq_false] at hξ

/-- The polynomial weights used in the terminal step do not enlarge closed Fourier support. -/
theorem tsupport_fourier_smulLeftCLM_one_add_norm_sq_pow_subset (f : 𝓢(E, ℂ)) (A : ℕ) :
    tsupport (𝓕 (smulLeftCLM ℂ (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ A) f) : 𝓢(E, ℂ)) ⊆
      tsupport (𝓕 f : 𝓢(E, ℂ)) := by
  induction A with
  | zero => simp
  | succ A hA =>
    have he : smulLeftCLM ℂ (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ (A + 1)) f =
        smulLeftCLM ℂ (fun x : E ↦ 1 + ‖x‖ ^ 2)
          (smulLeftCLM ℂ (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ A) f) := by
      rw [smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
      congr 2
      ext x
      simp only [Pi.mul_apply, pow_succ, mul_comm]
    rw [he]
    exact (tsupport_fourier_smulLeftCLM_one_add_norm_sq_subset _).trans hA

end NKBesicovitch
