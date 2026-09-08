/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerCode

/-!
# Reconstructing a corner from its code

The first line, last-line intercept, and corner code determine the full corner.
The inverse has the two nonzero factors `a-b` and `b-a` required by equation (30)
of the supplied manuscript.
-/

@[expose] public section

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- Recover a corner from its first line, last intercept, and code. -/
noncomputable def cornerFromCode (a b c κ : ℝ) (g : Line m) (x z : EuclideanSpace ℝ (Fin m)) :
    CornerCoordinates m :=
  let ξ₃ := (a - b)⁻¹ • (z - κ • atHeight c g)
  let ξ₂ := (b - a)⁻¹ • (x + b • ξ₃ - atHeight a g)
  (lineAt a (atHeight a g) ξ₂, (g.2, ξ₃))

theorem first_cornerFromCode (a b c κ : ℝ) (g : Line m) (x z : EuclideanSpace ℝ (Fin m)) :
    cornerFirst a (cornerFromCode a b c κ g x z) = g := by
  simp [cornerFirst, cornerFromCode, atHeight_lineAt, lineAt_atHeight]

theorem last_cornerFromCode {a b : ℝ} (hab : a ≠ b) (c κ : ℝ)
    (g : Line m) (x z : EuclideanSpace ℝ (Fin m)) :
    cornerLast b (cornerFromCode a b c κ g x z) =
      (x, (a - b)⁻¹ • (z - κ • atHeight c g)) := by
  dsimp only [cornerLast, cornerFromCode]
  rw [atHeight_lineAt, smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr hab.symm), one_smul]
  simp [lineAt]

theorem cornerCode_cornerFromCode {a b : ℝ} (hab : a ≠ b) (c κ : ℝ)
    (g : Line m) (x z : EuclideanSpace ℝ (Fin m)) : cornerCode a b c κ
      (cornerFromCode a b c κ g x z) = z := by
  rw [cornerCode, first_cornerFromCode]
  change κ • atHeight c g + (a - b) • ((a - b)⁻¹ • (z - κ • atHeight c g)) = z
  rw [smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr hab), one_smul]
  module

theorem cornerFromCode_cornerCode {a b : ℝ} (hab : a ≠ b) (c κ : ℝ)
    (p : CornerCoordinates m) :
    cornerFromCode a b c κ (cornerFirst a p) (cornerLast b p).1 (cornerCode a b c κ p) = p := by
  have h₃ : (a - b)⁻¹ • (cornerCode a b c κ p - κ • atHeight c (cornerFirst a p)) = p.2.2 := by
    simp [cornerCode, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hab)]
  have h₂ : (b - a)⁻¹ • ((cornerLast b p).1 + b • p.2.2 -
      atHeight a (cornerFirst a p)) = p.1.2 := by
    rw [atHeight_cornerFirst]
    have he : (cornerLast b p).1 + b • p.2.2 - atHeight a p.1 = (b - a) • p.1.2 := by
      unfold cornerLast lineAt atHeight
      module
    rw [he, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hab.symm), one_smul]
  dsimp only [cornerFromCode]
  rw [h₃, h₂, atHeight_cornerFirst, lineAt_atHeight]
  rfl

theorem continuous_cornerFromCode (a b c κ : ℝ) :
    Continuous (fun p : Line m × (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) ↦
      cornerFromCode a b c κ p.1 p.2.1 p.2.2) := by
  unfold cornerFromCode lineAt atHeight
  fun_prop

end NKBesicovitch.Projection
