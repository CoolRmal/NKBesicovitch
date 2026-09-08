/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerPattern
public import NKBesicovitch.Projection.JacobianBounds

/-!
# Uniform data controlling the constants of a corner pattern

A common separation radius, label-count bound, and input projection
constant control the Jacobians and finite combinatorial factors appearing
in the stopping proof. These data are uniform across selected patterns.
-/

@[expose] public section

open MeasureTheory Set Bornology

namespace NKBesicovitch.Projection.CornerPattern

variable {m L : ℕ} {β r C : ℝ} {P : CornerPattern m β}

/-- Quantitative geometric and analytic bounds for one admissible pattern. -/
structure IsControlled (P : CornerPattern m β) (r C : ℝ) (L : ℕ) : Prop where
  radius_pos : 0 < r
  radius_le_one : r ≤ 1
  one_le_constant : 1 ≤ C
  times_unit : ∀ t ∈ P.times, t ∈ Icc 0 1
  base_separation : r ≤ dist P.a P.b
  base_c_separation : r ≤ dist P.a P.c
  dual_separation : ∀ u ∈ P.outer, ∀ t ∈ P.inner u,
    r ≤ dist P.b (dualTime P.b P.a (cornerInnerCoefficient P.a P.c P.κ u) t)
  outer_card : P.outer.card ≤ L
  inner_card : ∀ u ∈ P.outer, (P.inner u).card ≤ L
  outer_bound : ∀ G : Set (Line m), MeasurableSet G → IsBounded G →
    (volume G).toReal ≤ C * (parallelMultiplicity G).toReal ^ (2 - β) *
      (sliceSize P.outer G).toReal ^ β
  inner_bound : ∀ u ∈ P.outer, ∀ G : Set (Line m), MeasurableSet G → IsBounded G →
    (volume G).toReal ≤ C * (parallelMultiplicity G).toReal ^ (2 - β) *
      (sliceSize (P.inner u) G).toReal ^ β

namespace IsControlled

theorem children_card (h : P.IsControlled r C L) : P.children.card ≤ L * L := by
  classical
  calc
    _ ≤ ∑ u ∈ P.outer, ((P.inner u).image (fun t ↦ (u, t))).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ P.outer, L := Finset.sum_le_sum
      (fun u hu ↦ Finset.card_image_le.trans (h.inner_card u hu))
    _ = P.outer.card * L := by simp
    _ ≤ L * L := Nat.mul_le_mul_right L h.outer_card

theorem codeJacobian_le (h : P.IsControlled r C L) :
    (codeJacobian m P.a P.b).toReal ≤ r⁻¹ ^ m :=
  codeJacobian_toReal_le_of_separated m h.radius_pos h.base_separation

theorem reverse_codeJacobian_le (h : P.IsControlled r C L) :
    (codeJacobian m P.b P.a).toReal ≤ r⁻¹ ^ m :=
  codeJacobian_toReal_le_of_separated m h.radius_pos
    (by simpa only [dist_comm] using h.base_separation)

theorem pairJacobian_le (h : P.IsControlled r C L) :
    (pairJacobian m P.a P.b P.c).toReal ≤ r⁻¹ ^ (2 * m) :=
  pairJacobian_toReal_le_of_separated m h.radius_pos h.base_separation h.base_c_separation

theorem innerJacobian_ge (h : P.IsControlled r C L) {u t : ℝ}
    (hu : u ∈ P.outer) (ht : t ∈ P.inner u) :
    r ^ m ≤ (ENNReal.ofReal |(((P.a - P.b) /
      (dualTime P.b P.a (cornerInnerCoefficient P.a P.c P.κ u) t - P.b)) ^ m)⁻¹|).toReal :=
  innerJacobian_toReal_ge_of_separated m (h.times_unit _ P.a_mem_times)
    (h.times_unit _ P.b_mem_times) P.a_ne_b h.radius_pos.le (h.dual_separation u hu t ht)

end IsControlled

end NKBesicovitch.Projection.CornerPattern
