/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerPattern
public import NKBesicovitch.Projection.TimeTranslation

/-!
# Admissible patterns from a finite input projection estimate

Translate the outer input heights away from the first and third parent
heights. For each outer height, translate the inner input heights away
from both inner bases and the unique additional fixed point of duality.
Only finitely many heights are forbidden at each step.
-/

public section

namespace NKBesicovitch.Projection

variable {m : ℕ} {β : ℝ}

theorem dualTime_ne_self {a b c t : ℝ} (hc : c ≠ 0) (hta : t ≠ a) (htb : t ≠ b)
    (ht : t ≠ b + (b - a) / c) : dualTime a b c t ≠ t := by
  intro h
  have hdiv : (b - a) * (t - a) / (c * (t - b)) = t - a := by
    simpa only [dualTime_sub_base] using congrArg (fun x : ℝ ↦ x - a) h
  have hmul := (div_eq_iff (mul_ne_zero hc (sub_ne_zero.mpr htb))).mp hdiv
  have he : b - a = c * (t - b) := mul_left_cancel₀ (sub_ne_zero.mpr hta)
    (by simpa only [mul_comm (b - a) (t - a)] using hmul)
  have ht' : t - b = (b - a) / c := (eq_div_iff hc).mpr (by nlinarith [he])
  exact ht (by linarith)

theorem exists_cornerPattern {Γ : Finset ℝ} (hΓ : Γ.Nonempty)
    (hEstimate : HasProjectionEstimate m β Γ) (a b c : ℝ)
    (hba : b ≠ a) (hca : c ≠ a) (hcb : c ≠ b) :
    ∃ P : CornerPattern m β, P.a = a ∧ P.b = b ∧ P.c = c := by
  classical
  obtain ⟨τ, hτ⟩ := exists_translate_avoiding Γ {a, c}
  choose σ hσ using fun u : ℝ ↦ exists_translate_avoiding Γ
    {b, a, a + (a - b) / cornerInnerCoefficient a c 1 u}
  have houter (u : ℝ) (hu : u ∈ Γ.image (· + τ)) : u ≠ a ∧ u ≠ c := by
    have h := hτ u hu
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using h
  have hinner (u t : ℝ) (ht : t ∈ Γ.image (· + σ u)) :
      t ≠ b ∧ t ≠ a ∧ t ≠ a + (a - b) / cornerInnerCoefficient a c 1 u := by
    have h := hσ u t ht
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using h
  refine ⟨{
    a := a, b := b, c := c, κ := 1
    a_ne_b := hba.symm, c_ne_a := hca, c_ne_b := hcb, κ_ne_zero := one_ne_zero
    outer := Γ.image (· + τ)
    outer_nonempty := hΓ.image _
    inner := fun u ↦ Γ.image (· + σ u)
    inner_nonempty := fun _ _ ↦ hΓ.image _
    outer_ne_a := fun u hu ↦ (houter u hu).1
    outer_ne_c := fun u hu ↦ (houter u hu).2
    inner_ne_b := fun u _ t ht ↦ (hinner u t ht).1
    inner_ne_a := fun u _ t ht ↦ (hinner u t ht).2.1
    dual_ne_inner := ?_
    outer_estimate := hEstimate.translate τ
    inner_estimate := fun u _ ↦ hEstimate.translate (σ u)
  }, rfl, rfl, rfl⟩
  intro u hu t ht
  exact dualTime_ne_self
    (cornerInnerCoefficient_ne_zero one_ne_zero (houter u hu).1 (houter u hu).2)
    (hinner u t ht).1 (hinner u t ht).2.1 (hinner u t ht).2.2

end NKBesicovitch.Projection
