/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Plancherel as a nonnegative integral identity

The nonnegative-integral form of Mathlib's Schwartz Plancherel theorem
can be averaged over directions without a separate outer integrability assumption.
-/

public section

open MeasureTheory
open scoped SchwartzMap FourierTransform ENNReal

namespace NKBesicovitch

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem lintegral_enorm_sq_fourier (f : 𝓢(E, H)) :
    (∫⁻ ξ, ‖𝓕 f ξ‖ₑ ^ 2) = ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  have h := congrArg ENNReal.ofReal f.integral_norm_sq_fourier
  rw [ofReal_integral_eq_lintegral_ofReal ((𝓕 f).memLp 2 volume |>.integrable_norm_pow
    (by norm_num)) (ae_of_all _ fun x ↦ sq_nonneg _),
    ofReal_integral_eq_lintegral_ofReal (f.memLp 2 volume |>.integrable_norm_pow
      (by norm_num)) (ae_of_all _ fun x ↦ sq_nonneg _)] at h
  simpa only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using h

end NKBesicovitch
