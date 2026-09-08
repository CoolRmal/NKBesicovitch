/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Operators.Interpolation.BlockBounds

/-!
# Separating the two dyadic scales from the fixed constants

The decomposition weight is twice its superlevel threshold. Enlarging the
threshold's positive power and splitting the fiber scale leave a product
of two halving-scale powers and one fixed coefficient.
-/

public section

open scoped ENNReal

namespace NKBesicovitch

theorem normalize_dyadic_block_bound {N A S : ℝ≥0∞} {s B t u v : ℝ}
    (hs : 0 ≤ s) (hB : 0 ≤ B) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : ENNReal.ofReal (s / 2) * N ≤ A * ENNReal.ofReal (s / 2) ^ u *
      ENNReal.ofReal (B * t) ^ v * S) :
    ENNReal.ofReal s * N ≤ (2 * A * ENNReal.ofReal B ^ v * S) *
      ENNReal.ofReal s ^ u * ENNReal.ofReal t ^ v := by
  have hhalf : ENNReal.ofReal (s / 2) ^ u ≤ ENNReal.ofReal s ^ u :=
    ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (by linarith)) hu
  calc
    _ = 2 * (ENNReal.ofReal (s / 2) * N) := by
      have he : s = 2 * (s / 2) := by ring
      conv_lhs => arg 1; rw [he, ENNReal.ofReal_mul (by norm_num)]
      norm_num only [ENNReal.ofReal_ofNat, mul_assoc]
    _ ≤ 2 * (A * ENNReal.ofReal (s / 2) ^ u * ENNReal.ofReal (B * t) ^ v * S) :=
      mul_le_mul_right h _
    _ ≤ 2 * (A * ENNReal.ofReal s ^ u * ENNReal.ofReal (B * t) ^ v * S) := by
      gcongr
    _ = _ := by
      rw [ENNReal.ofReal_mul hB, ENNReal.mul_rpow_of_nonneg _ _ hv]
      ring

end NKBesicovitch
