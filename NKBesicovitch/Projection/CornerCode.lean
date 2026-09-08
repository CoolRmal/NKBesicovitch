/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerCoordinates

/-!
# Corner codes and their pair decomposition

The corner code splits into a first-line position and the code of the inner
pair. This is equation (33) of the supplied projection manuscript.
-/

@[expose] public section

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- The corner code using the first line's position at `c` and the last line's slope. -/
def cornerCode (a b c κ : ℝ) (p : CornerCoordinates m) : Space m :=
  κ • atHeight c (cornerFirst a p) + (a - b) • p.2.2

/-- The coefficient of the outer first-line position. -/
noncomputable def cornerOuterCoefficient (a c κ u : ℝ) : ℝ := κ * (c - a) / (u - a)

/-- The scalar parameter for the inner pair code. -/
noncomputable def cornerInnerCoefficient (a c κ u : ℝ) : ℝ := κ * (u - c) / (u - a)

theorem cornerInnerCoefficient_ne_zero {a c κ u : ℝ} (hκ : κ ≠ 0)
    (hua : u ≠ a) (huc : u ≠ c) : cornerInnerCoefficient a c κ u ≠ 0 :=
  div_ne_zero (mul_ne_zero hκ (sub_ne_zero.mpr huc)) (sub_ne_zero.mpr hua)

theorem cornerOuterCoefficient_ne_zero {a c κ u : ℝ} (hκ : κ ≠ 0)
    (hca : c ≠ a) (hua : u ≠ a) : cornerOuterCoefficient a c κ u ≠ 0 :=
  div_ne_zero (mul_ne_zero hκ (sub_ne_zero.mpr hca)) (sub_ne_zero.mpr hua)

theorem corner_coefficients_sum {a c κ u : ℝ} (hua : u ≠ a) :
    cornerOuterCoefficient a c κ u + cornerInnerCoefficient a c κ u = κ := by
  unfold cornerOuterCoefficient cornerInnerCoefficient
  field_simp
  ring

theorem corner_coefficients_weighted_sum {a c κ u : ℝ} (hua : u ≠ a) :
    cornerOuterCoefficient a c κ u * u + cornerInnerCoefficient a c κ u * a = κ * c := by
  unfold cornerOuterCoefficient cornerInnerCoefficient
  field_simp
  ring

theorem corner_projection_identity {a c κ u : ℝ} (hua : u ≠ a) (g : Line m) :
    κ • atHeight c g = cornerOuterCoefficient a c κ u • atHeight u g +
      cornerInnerCoefficient a c κ u • atHeight a g := by
  unfold atHeight
  calc
    _ = (cornerOuterCoefficient a c κ u + cornerInnerCoefficient a c κ u) • g.1 +
        (cornerOuterCoefficient a c κ u * u + cornerInnerCoefficient a c κ u * a) • g.2 := by
      rw [corner_coefficients_sum hua, corner_coefficients_weighted_sum hua]
      module
    _ = _ := by module

/-- On a corner-code fiber, the outer position determines the inner-pair code. -/
theorem cornerCode_eq_outer_add_inner {a b c κ u : ℝ} (hua : u ≠ a)
    (p : CornerCoordinates m) : cornerCode a b c κ p =
      cornerOuterCoefficient a c κ u • atHeight u (cornerFirst a p) +
        pairCode b a (cornerInnerCoefficient a c κ u) (cornerInner b p) := by
  rw [cornerCode, corner_projection_identity hua, pairCode, first_cornerInner,
    atHeight_cornerFirst]
  simp only [cornerInner, add_assoc]

end NKBesicovitch.Projection
