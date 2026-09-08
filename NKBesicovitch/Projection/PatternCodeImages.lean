/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.PatternConstants
public import NKBesicovitch.Projection.CodeImage
public import NKBesicovitch.Projection.MonomialBounds

/-!
# One inner-code image constant for a corner pattern

For normalized parallel multiplicity, all surviving inner-code images have
outer measure at most `K |W| ℓ^(-β/(β-1))`. The positive constant `K` depends
only on the fixed pattern and the input exponent.
-/

@[expose] public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection.CornerPattern

variable {m : ℕ} {β : ℝ}

/-- The simultaneous inner-code image estimate with a specified constant. -/
def CodeImageBound (P : CornerPattern m β) (K : ℝ) : Prop :=
    ∀ G : Set (Line m), IsBounded G → (parallelMultiplicity G).toReal ≤ 1 →
      ∀ W E₁ E₂ E₃ : Set (PairCoordinates m),
      MeasurableSet W → MeasurableSet E₁ → MeasurableSet E₂ →
      W ⊆ pairFamily P.b G → E₁ ⊆ W → E₂ ⊆ W →
      ∀ ℓ : ℝ≥0∞, 0 < ℓ.toReal →
      (∀ v ∈ P.children, ∀ p ∈ E₂, ℓ ≤ pairDensity P.b v.2
        (dualTime P.b P.a (cornerInnerCoefficient P.a P.c P.κ v.1) v.2) E₁
        (pairProjections P.b v.2
          (dualTime P.b P.a (cornerInnerCoefficient P.a P.c P.κ v.1) v.2) p)) →
      (∀ u ∈ P.outer, ∀ p ∈ E₃,
        0 < codeDensity P.b P.a (cornerInnerCoefficient P.a P.c P.κ u) W
          (pairCode P.b P.a (cornerInnerCoefficient P.a P.c P.κ u) p) ∧
        codeDensity P.b P.a (cornerInnerCoefficient P.a P.c P.κ u) W
          (pairCode P.b P.a (cornerInnerCoefficient P.a P.c P.κ u) p) ≤
          2 * codeDensity P.b P.a (cornerInnerCoefficient P.a P.c P.κ u) E₂
            (pairCode P.b P.a (cornerInnerCoefficient P.a P.c P.κ u) p)) →
      ∀ u ∈ P.outer, volume (pairCode P.b P.a (cornerInnerCoefficient P.a P.c P.κ u) '' E₃) ≤
        ENNReal.ofReal (K * (volume W).toReal * ℓ.toReal ^ (-(β / (β - 1))))

theorem codeImageBound_of_input_bound (P : CornerPattern m β) (hβ : 1 < β) (hβ2 : β ≤ 2)
    {C q : ℝ} (hC : 0 < C) (hq : 0 < q)
    (hInner : ∀ u ∈ P.outer, ∀ G : Set (Line m), MeasurableSet G → IsBounded G →
      (volume G).toReal ≤ C * (parallelMultiplicity G).toReal ^ (2 - β) *
        (sliceSize (P.inner u) G).toReal ^ β)
    (hqt : ∀ u ∈ P.outer, ∀ t ∈ P.inner u, q ≤
      (ENNReal.ofReal |(((P.a - P.b) /
        (dualTime P.b P.a (cornerInnerCoefficient P.a P.c P.κ u) t - P.b)) ^ m)⁻¹|).toReal) :
    P.CodeImageBound ((2 * (codeJacobian m P.b P.a).toReal * C) ^ (1 / (β - 1)) /
      q ^ (β / (β - 1))) := by
  let K := (2 * (codeJacobian m P.b P.a).toReal * C) ^ (1 / (β - 1)) / q ^ (β / (β - 1))
  have hj := ENNReal.toReal_pos (codeJacobian_pos (m := m) P.a_ne_b.symm).ne'
    (codeJacobian_ne_top m P.b P.a)
  have hA : 0 < 2 * (codeJacobian m P.b P.a).toReal * C := by positivity
  intro G hGb hM W E₁ E₂ E₃ hW hE₁ hE₂ hWG hE₁W hE₂W ℓ hℓ hdense hretain u hu
  obtain ⟨_, himagefin, himage⟩ := volume_pairCode_image_le_of_retained_density
    P.a_ne_b.symm (P.innerCoefficient_ne_zero hu) hβ hβ2 hC zero_lt_one
    (P.inner u) (hInner u hu) (P.inner_ne_b u hu) (P.inner_ne_a u hu)
    hGb hM hW hE₁ hE₂ hWG hE₁W hE₂W ℓ hℓ q hq (hqt u hu)
    (fun t ht ↦ hdense (u, t) (mem_children.mpr ⟨hu, ht⟩)) (hretain u hu)
  have hreal : (volume (pairCode P.b P.a (cornerInnerCoefficient P.a P.c P.κ u) '' E₃)).toReal ≤
      K * (volume W).toReal * ℓ.toReal ^ (-(β / (β - 1))) := by
    simpa only [Real.one_rpow, mul_one, inverse_density_threshold hA hq hℓ] using himage
  rw [← ENNReal.ofReal_toReal himagefin]
  exact ENNReal.ofReal_le_ofReal hreal

theorem CodeImageBound.mono {P : CornerPattern m β} {K K' : ℝ} (h : P.CodeImageBound K)
    (hK : K ≤ K') : P.CodeImageBound K' := by
  intro G hGb hM W E₁ E₂ E₃ hW hE₁ hE₂ hWG hE₁W hE₂W ℓ hℓ hdense hretain u hu
  refine (h G hGb hM W E₁ E₂ E₃ hW hE₁ hE₂ hWG hE₁W hE₂W ℓ hℓ hdense hretain u hu).trans ?_
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hK ENNReal.toReal_nonneg)
    (Real.rpow_nonneg ENNReal.toReal_nonneg _))

theorem exists_code_image_constant (P : CornerPattern m β) (hβ : 1 < β) (hβ2 : β ≤ 2) :
    ∃ K : ℝ, 0 < K ∧ P.CodeImageBound K := by
  obtain ⟨C, hC, _, hInner⟩ := P.exists_input_constant
  obtain ⟨q, hq, hqt⟩ := P.exists_innerJacobian_lower_bound
  have hj := ENNReal.toReal_pos (codeJacobian_pos (m := m) P.a_ne_b.symm).ne'
    (codeJacobian_ne_top m P.b P.a)
  exact ⟨_, by positivity, P.codeImageBound_of_input_bound hβ hβ2 hC hq hInner hqt⟩

end NKBesicovitch.Projection.CornerPattern
