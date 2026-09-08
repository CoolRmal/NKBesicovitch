/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.PatternConstants
public import NKBesicovitch.Projection.OuterStep
public import NKBesicovitch.Projection.MonomialBounds

/-!
# A fixed outer constant at the conjugate exponent

For a fixed corner pattern with normalized parallel multiplicity, the
internally chosen outer threshold has its conjugate power bounded by a
constant times the projection size and the parent-pair density threshold.
-/

@[expose] public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection.CornerPattern

variable {m : ℕ} {β : ℝ}

/-- The outer conjugate-power estimate with a specified constant. -/
def OuterBound (P : CornerPattern m β) (C : ℝ) : Prop :=
    ∀ G : Set (Line m), IsBounded G → (parallelMultiplicity G).toReal ≤ 1 →
      ∀ N R : ℝ≥0∞, N ≠ 0 → N ≠ ∞ → R ≠ 0 → R ≠ ∞ →
      volume (atHeight P.c '' G) ≤ N →
      (∀ u ∈ P.outer, volume (atHeight u '' G) ≤ N) →
      ∀ D : Set (CornerCoordinates m), MeasurableSet D → D ⊆ cornerFamily P.a P.b G →
      0 < volume D → ∀ W E : Set (PairCoordinates m),
      (∀ p ∈ D, cornerParent P.a p ∈ W) → (∀ p ∈ D, cornerInner P.b p ∈ E) →
      ∀ Q₀ : ℝ≥0∞, Q₀ ≠ ∞ →
      (∀ p ∈ D, pairDensity P.a P.b P.c W
        (pairProjections P.a P.b P.c (cornerParent P.a p)) ≤ Q₀) →
      (∀ u ∈ P.outer, volume (pairCode P.b P.a (cornerInnerCoefficient P.a P.c P.κ u) '' E) ≤ R) →
      ((volume D).toReal / (2 * P.outer.card * N.toReal * R.toReal)) ^ (β / (β - 1)) ≤
        C * (N.toReal * Q₀.toReal)

theorem outerBound_of_input_bound (P : CornerPattern m β) (hβ : 1 < β) (hβ2 : β ≤ 2)
    {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hOuter : ∀ G : Set (Line m), MeasurableSet G → IsBounded G →
      (volume G).toReal ≤ C₀ * (parallelMultiplicity G).toReal ^ (2 - β) *
        (sliceSize P.outer G).toReal ^ β) :
    P.OuterBound (((2 * (codeJacobian m P.a P.b).toReal ^ 2 * C₀) *
      (codeJacobian m P.a P.b).toReal ^ (β - 1)) ^ (1 / (β - 1))) := by
  let A := (2 * (codeJacobian m P.a P.b).toReal ^ 2 * C₀) *
    (codeJacobian m P.a P.b).toReal ^ (β - 1)
  have hj := ENNReal.toReal_pos (codeJacobian_pos (m := m) P.a_ne_b).ne'
    (codeJacobian_ne_top m P.a P.b)
  have hA : 0 < A := by dsimp only [A]; positivity
  intro G hGb hM N R hN₀ hN hR₀ hR hcN huN D hD hDG hpos W E hDW hDE Q₀ hQ₀ hQ himage
  have h := corner_mass_bound_of_code_images P.a_ne_b P.c_ne_a P.κ_ne_zero
    hβ hβ2 hC₀ zero_lt_one P.outer P.outer_nonempty hOuter P.outer_ne_a hGb hM
    hN₀ hN hR₀ hR hcN huN hD hDG hpos hDW hDE Q₀ hQ₀ hQ himage
  have hpower : ((volume D).toReal / (2 * P.outer.card * N.toReal * R.toReal)) ^ β ≤
      A * (N.toReal * Q₀.toReal) ^ (β - 1) := by
    simpa only [one_pow, mul_one] using h
  exact rpow_conjugate_le_of_rpow_le hβ hA.le (by positivity) (by positivity) hpower

theorem OuterBound.mono {P : CornerPattern m β} {C C' : ℝ} (h : P.OuterBound C)
    (hC : C ≤ C') : P.OuterBound C' := by
  intro G hGb hM N R hN₀ hN hR₀ hR hcN huN D hD hDG hpos W E hDW hDE Q₀ hQ₀ hQ himage
  exact (h G hGb hM N R hN₀ hN hR₀ hR hcN huN D hD hDG hpos W E hDW hDE Q₀ hQ₀ hQ himage).trans
    (mul_le_mul_of_nonneg_right hC (by positivity))

theorem exists_outer_constant (P : CornerPattern m β) (hβ : 1 < β) (hβ2 : β ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ P.OuterBound C := by
  obtain ⟨C₀, hC₀, hOuter, _⟩ := P.exists_input_constant
  have hj := ENNReal.toReal_pos (codeJacobian_pos (m := m) P.a_ne_b).ne'
    (codeJacobian_ne_top m P.a P.b)
  exact ⟨_, by positivity, P.outerBound_of_input_bound hβ hβ2 hC₀ hOuter⟩

end NKBesicovitch.Projection.CornerPattern
